//! The retained-access check (R812-1, era-5c 139/140): the evidence of the
//! retained-alias hold, counted as part of the analysis's decision.
//!
//! A pointer loaded from memory (a field, an element, a static) or returned opaquely by
//! a callee may reach an object that a reference also borrows. An access through it
//! while the loan is live is a conflict the frame-local replay does not see (era-5c 131
//! §1). This module computes, flow-insensitively over the whole program, which objects
//! such a pointer may reach, and withdraws a subject's safe decision when an access in
//! its extent may reach one of its objects: a write, or for a `&mut` subject a read too.
//!
//! **Fail closed by construction (R813-1).** Every statement, rvalue, cast, aggregate,
//! projection and terminator kind is matched exhaustively. A kind the module does not
//! model gives what it may carry the object [`Obj::Top`], which overlaps every object; a
//! subject an access through `Top` may reach is `Unknown`, and `Unknown` withdraws. The
//! table of kinds and rules is era-5c 140 §1; the soundness claim rests on it alone.
//!
//! **The world is the record's (W2, era-5c 136):** the census's closed world (outside
//! objects only at entries with no caller in the program) and the allocator contract
//! P5 (a call through an allocator hook allocates). No switch in the production path.
//!
//! **Objects:** an allocation per call site; an opaque result per call site, typed by
//! its pointee and its casts; an address-taken local; a static item; anonymous constant
//! memory; what an outside caller passes, per pointee type; `Top`.
//!
//! **Overlap:** two distinct program objects never overlap. An outside object overlaps
//! a program object as that object or a part of it (equal types, or contained by value);
//! two outside objects if either type contains the other. A character or `void` outside
//! object meets a typed object only if [`OUTSIDE_BYTES_DISJOINT`] is false (R1, the
//! user's question).
// The hold's wiring is wave-6o's (batch 56); until then only the witnesses call it.
#![allow(dead_code)]

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_middle::{
    mir::{
        AggregateKind, BasicBlock, BinOp, Body, CastKind, InlineAsmOperand, Local, Location,
        NonDivergingIntrinsic, Operand, Place, ProjectionElem, Rvalue, StatementKind,
        TerminatorKind,
        interpret::{AllocId, GlobalAlloc, Scalar},
    },
    ty::{Ty, TyCtxt, TyKind, adjustment::PointerCoercion},
};
use rustc_mir_dataflow::Analysis;
use rustc_span::def_id::{DefId, LocalDefId};

use crate::{
    analyses::{
        borrow_ownership::{SlotKind, crate_slots::CrateSlots, solver::SlotRef},
        liveness::MaybeLiveLocals,
    },
    utils::rustc::RustProgram,
};

/// R1 (era-5c 139 §3; the user's question): an outside character or `void` object never
/// meets a typed object. The premise: "an outside caller does not hand the program a
/// byte view of an object that it also hands it typed". `false` drops the premise.
pub(crate) const OUTSIDE_BYTES_DISJOINT: bool = true;

/// A call's callee, as `analyses::mir::CallKind` classifies it (that module is private
/// to `analyses`, whose tree this module must not touch).
enum CallKind {
    FreeStanding(LocalDefId),
    LibC(rustc_span::Symbol),
    RustLib(DefId),
    Impl(LocalDefId),
    /// A call through a function pointer.
    Closure,
    Dynamic,
}

struct Call<'a, 'tcx> {
    func: CallKind,
    args: &'a [rustc_span::source_map::Spanned<Operand<'tcx>>],
    destination: Place<'tcx>,
}

fn as_call<'a, 'tcx>(
    terminator: &'a rustc_middle::mir::Terminator<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> Option<Call<'a, 'tcx>> {
    let (func, args, destination) = match &terminator.kind {
        TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } => (func, args, *destination),
        TerminatorKind::TailCall { func, args, .. } => (func, args, Place::return_place()),
        _ => return None,
    };
    let func = match func.constant().map(|c| *c.ty().kind()) {
        Some(TyKind::FnDef(callee, _)) => match callee.as_local() {
            Some(local) => match tcx.hir_node_by_def_id(local) {
                rustc_hir::Node::Item(_) => CallKind::FreeStanding(local),
                rustc_hir::Node::ForeignItem(item) => CallKind::LibC(item.ident.name),
                rustc_hir::Node::ImplItem(_) => CallKind::Impl(local),
                _ => CallKind::Dynamic,
            },
            None => CallKind::RustLib(callee),
        },
        _ => CallKind::Closure,
    };
    Some(Call {
        func,
        args,
        destination,
    })
}

/// A rule of the check, for the test faults (one fault per rule).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Rule {
    /// A load from outside memory yields the outside object of the pointee type.
    OutsideLoad,
    /// A call through a hook whose every target allocates is an allocation (P5).
    AllocatorHook,
    /// A struct copied by value or by `memcpy` carries the pointers it holds.
    CopyCarry,
    /// A byte copy carries the pointers the source holds, through any integer.
    ByteCopy,
    /// A cell read also reads the fields of that pointer type, and the reverse.
    CellField,
    /// A cell of a mixed object reads everything the object holds.
    MixedUnion,
    /// A subject whose extent loads a cell of a mixed object is `Unknown`.
    Unknown,
    /// An integer made a pointer, and every unmodelled kind, carries `Top`.
    TopFlows,
    /// A write counts only through a raw retaining place (132 §2's guard).
    RawGuard,
    /// A `&mut` subject is held for a read too.
    MutRead,
    /// A formal whose derived value is stored into memory is held.
    DerivedStore,
    /// Memory a library contract returns (a `FILE`, `errno`, a static buffer) is the
    /// library's: it never meets a program object (R1b's unknown results are `Top`).
    LibraryMemory,
    /// R2: a wrapper is an allocator only if its fresh value escapes by its return alone.
    WrapperEscape,
    /// R2b: the caller's site object takes the wrapper's object's contents.
    WrapperContents,
    /// R3: a static's initializer stores its relocations.
    StaticInit,
    /// R4: an address-taken pointer local is its own memory cell.
    AddressTaken,
    /// R5: a union's members are one place.
    UnionMembers,
    /// R6: an array or tuple value stores its pointers as its cells.
    ArrayInit,
    /// R7: an aggregate passed or returned by value carries its pointers.
    ByValue,
    /// R9: a foreign call's effects follow its contract; an unlisted one is `Top`.
    ForeignEffects,
    /// R10: a local's extent is read at every statement, not at block ends.
    StatementLiveness,
    /// R11: only a must-derived local is the subject's own.
    MustDerive,
    /// R12: a value a callee returns from its parameter derives from the argument.
    ReturnedAlias,
    /// 2.1: a copy of outside memory holds what the outside stored.
    OutsideCopy,
    /// 2.2: what was stored through `Top` may be in any memory.
    TopStores,
    /// 2.4: corresponding signed and unsigned types alias.
    Signedness,
    /// 2.6: a write by a foreign or unknown call makes a local mutable.
    ForeignMutability,
    /// 2.7: a function pointer may be any program or foreign target.
    JointTargets,
    /// 2.8: formatted output's pointer varargs are written unless the format is a
    /// literal without `%n`.
    FormatWrites,
    /// 2.9: `strtok` reads and writes the buffer it remembers.
    StrtokState,
    /// 2.12: a local whose value escapes into memory or an aggregate is live throughout.
    EscapingExtent,
    /// Item 4: the address of a struct field names the member.
    Members,
    /// Item 4: a member's address cast to another struct or union pointer may be the
    /// container's (the first-member conversion).
    MemberCast,
    /// Item 4: a member's byte view moved by a negative or non-constant offset reaches
    /// the whole object (container-of arithmetic).
    ContainerOf,
    /// Relay 176: a member's address cast back to the member's own type is the member.
    VoidCast,
    /// 3.6: an integer local's memory holds the bytes a copy wrote there.
    IntLocalMemory,
    /// H2: a copy into an object of another type keeps the pointers it carries.
    CrossCopy,
    /// H1: an outside object may contain a program object or a member (an aggregate of
    /// its type).
    Containers,
    /// H6: stores of a formal's value inside an aggregate, by a library contract, by an
    /// unlisted foreign function, or by a callee that stores its own formal.
    WideStores,
    /// era-5c 145 H1: under (E), an evident hold stands even where the subject may be
    /// `Top` (an unknown hold is not a reason to drop an evident shape).
    EvidentUnknown,
    /// era-5c 145 H2: a local's derived stores are a formal's (aggregates, library
    /// contracts, unlisted calls, callees that store it).
    LocalWideStores,
    /// era-5c 145 H4: a self store without a dereference on the left (`h.q = &h.x`), or
    /// with an address on the right, is a self-reference.
    SelfStores,
    /// era-5c 145a (Codex round 2, TOP): a hold on a `Top` access takes the subject's own
    /// evident shape.
    TopShape,
    /// H3: a byte pointer reaching a member is a view wherever it was loaded from, and a
    /// re-cast view keeps its mark.
    ViewValues,
    /// M1: pointers printed (`%p`) or written out may come back through library input.
    RoundTrip,
    /// H4 / H5: a function handed to outside code that may call it takes the outside's
    /// objects, and a callback contract inherits the accesses of a function held in a
    /// local (`Some(f)`).
    Callbacks,
    /// 2.3 (item 4): an outside object meets a program object only if the program handed
    /// it to the outside, and then whatever the outside pointer's type (R1 is about
    /// outside objects only).
    Escape,
    /// 3.4: memory the program hands out (and an exported static) holds what the outside
    /// stores there: a load from it yields the outside object of its pointee type. Solved
    /// jointly with the escapes.
    IncomingStores,
    /// 3.8: a formal a callee returns or keeps inside an aggregate (or hands to another
    /// such callee) is stored: the caller's local stays live throughout.
    AggregateTransfer,
}

/// The options of one computation: the witnesses' faults and the R1 measurement.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Options {
    pub(crate) fault: Option<Rule>,
    pub(crate) outside_bytes_disjoint: bool,
    /// The wider R1 sentence (era-5c 140 §3, a measurement only): an outside byte pointer
    /// never reaches a typed object of the program's own either, escaped or not.
    pub(crate) program_bytes_disjoint: bool,
    /// era-5c 142a §3 (ii), a measurement: the hold by types alone. An access in the
    /// subject's extent conflicts when its pointer's pointee type may alias the subject's
    /// (equal up to signedness, one containing the other, a character or unknown type),
    /// whatever objects either may reach.
    pub(crate) by_types: bool,
    /// R816-1, the closed world: entry arguments designate fresh objects (one per
    /// argument, and one per way reached from it); nothing outside the program writes
    /// its memory; no outside rule applies.
    pub(crate) closed: bool,
    /// era-5c relay 178 (E), a measurement: only the evident shapes hold (a stored
    /// pointer derived from the subject; an object holding a pointer into itself or its
    /// container); nothing is Unknown.
    pub(crate) evident: bool,
    /// More rules removed at once (a measurement): a mask of `Rule as u64`.
    pub(crate) faults: u64,
    /// Relay 179, a measurement of N1's closure (off by default; N1 stays RED): a
    /// local's extent takes its own function's accesses at a recursive call to itself.
    pub(crate) close_n1: bool,
    /// `glob` stores library memory into its fourth argument's memory (relay 179's N2
    /// closure; the contract row of record since relay 183 item 3).
    pub(crate) close_n2: bool,
}

impl Options {
    /// The mode of record (R826-1): (E) in the closed world, M1 off, with `glob`'s
    /// store row (relay 183 item 3).
    pub(crate) fn of_record() -> Self {
        Options {
            closed: true,
            evident: true,
            close_n1: true,
            close_n2: true,
            faults: 1u64 << Rule::RoundTrip as u64,
            ..Options::default()
        }
    }
}

impl Default for Options {
    fn default() -> Self {
        Options {
            fault: None,
            outside_bytes_disjoint: OUTSIDE_BYTES_DISJOINT,
            program_bytes_disjoint: false,
            by_types: false,
            closed: false,
            evident: false,
            faults: 0,
            close_n1: false,
            close_n2: false,
        }
    }
}

/// An index into [`Relation::types`].
type TyId = usize;

/// An abstract object a pointer may point to, or into.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Obj {
    Alloc(LocalDefId, BasicBlock),
    /// Memory a library contract returns, per call site.
    Opaque(LocalDefId, BasicBlock),
    Stack(LocalDefId, Local),
    /// A pointer-typed constant into memory of no item, per pointee type.
    Static(TyId),
    /// A static item.
    Global(DefId),
    /// Anonymous constant memory a constant or a static's initializer points to.
    Anon(u32),
    /// What an outside caller passes, per pointee type.
    External(TyId),
    /// Anything: what a kind the module does not model may carry. Overlaps every object.
    Top,
    /// The closed world (R816-1): an object the program's client passes to an entry, or
    /// one reached from it; an index into [`Relation::fresh`]. Distinct from every other.
    Fresh(u32),
    /// A member of an object, by the address of a struct field (`&(*s).br`): an index
    /// into [`Relation::subs`]. Two members of one object are disjoint (C: arithmetic
    /// from a member stays inside it on a UB-free input); memory keys are the root's.
    Sub(u32),
}

/// Where a pointer value is kept in memory.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Key {
    /// The field `(struct, index)` of an object (a union's members are index 0).
    Field(Obj, DefId, usize),
    /// Any other memory cell of an object holding a pointer of this type.
    Cell(Obj, TyId),
    /// What an initializer, or an unmodelled write, stored anywhere in the object;
    /// every load from the object reads it.
    Init(Obj),
}

impl Key {
    fn holder(self) -> Obj {
        match self {
            Key::Field(obj, ..) | Key::Cell(obj, _) | Key::Init(obj) => obj,
        }
    }

    fn moved(self, target: Obj) -> Key {
        match self {
            Key::Field(_, did, index) => Key::Field(target, did, index),
            Key::Cell(_, ty) => Key::Cell(target, ty),
            Key::Init(_) => Key::Init(target),
        }
    }
}

/// How a closed-world fresh object is reached: an entry's argument, or a load of a
/// field or a cell from an object reached from that argument.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum FreshWay {
    Arg(LocalDefId, usize),
    Field(DefId, usize),
    Cell(TyId),
    Init,
}

/// Where a retained pointer was loaded from: its retaining place.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Via {
    Field(DefId, usize),
    Cell(TyId),
    /// The result of a call the analysis cannot see.
    Opaque,
    /// A load whose place never resolved to a key.
    Unresolved,
    /// A kind the module does not model.
    Unknown,
}

/// An access through a pointer loaded from memory or returned opaquely.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct Access {
    obj: Obj,
    write: bool,
    via: Via,
    /// The local of `at`'s function the access goes through.
    by: Local,
    at: (LocalDefId, Location),
}

/// A pointer value: the objects it may reach, whether it came from memory (retained)
/// and through which places, and the parameters it derives from.
#[derive(Clone, Debug, Default)]
struct Value {
    objs: FxHashSet<Obj>,
    retained: bool,
    vias: FxHashSet<Via>,
    params: FxHashSet<usize>,
}

impl Value {
    fn objs(objs: impl IntoIterator<Item = Obj>) -> Self {
        Value {
            objs: objs.into_iter().collect(),
            ..Default::default()
        }
    }

    fn top() -> Self {
        Value {
            objs: FxHashSet::from_iter([Obj::Top]),
            retained: true,
            vias: FxHashSet::from_iter([Via::Unknown]),
            params: FxHashSet::default(),
        }
    }

    fn join(&mut self, other: Value) {
        self.objs.extend(other.objs);
        self.retained |= other.retained;
        self.vias.extend(other.vias);
        self.params.extend(other.params);
    }
}

/// A pointer argument's effect in a foreign call's contract.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Eff {
    None,
    Read,
    Write,
    ReadWrite,
}

/// A foreign call's result.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Ret {
    /// No pointer result.
    None,
    /// A fresh allocation per call site.
    Alloc,
    /// `realloc`: a fresh allocation, or the old block.
    Realloc,
    /// A pointer into argument `i`.
    Arg(usize),
    /// Memory the library owns (a `FILE`, a static buffer): opaque, typed by its pointee.
    Opaque,
    /// `strtok`: a pointer into the first argument of some earlier call.
    Strtok,
}

/// The contract of a C library function: its pointer arguments' effects (the rest
/// for varargs), its result, the pointers it copies (`memcpy`: destination ← source)
/// or stores (`strtoul`'s end pointer: `*endptr` ← argument), and whether it calls a
/// function it is given. The table covers every foreign function the twenty call
/// (era-5c 140 §1); an unlisted one is `Top` (fail closed).
struct Contract {
    args: &'static [Eff],
    rest: Eff,
    ret: Ret,
    copy: Option<(usize, usize)>,
    store: Option<(usize, usize)>,
    callback: bool,
}

const fn contract(args: &'static [Eff], rest: Eff, ret: Ret) -> Contract {
    Contract {
        args,
        rest,
        ret,
        copy: None,
        store: None,
        callback: false,
    }
}

fn contract_of(name: &str) -> Option<Contract> {
    use Eff::{None as N, Read as R, ReadWrite as RW, Write as W};
    Some(match name {
        // Allocation.
        "malloc" | "calloc" => contract(&[], N, Ret::Alloc),
        "realloc" => contract(&[W], N, Ret::Realloc),
        "strdup" => contract(&[R], N, Ret::Alloc),
        "free" => contract(&[W], N, Ret::None),
        // Memory and strings.
        "memcpy" | "memmove" => Contract {
            copy: Some((0, 1)),
            ..contract(&[W, R], N, Ret::Arg(0))
        },
        "memset" => contract(&[W], N, Ret::Arg(0)),
        "memcmp" | "strcmp" | "strncmp" | "strcasecmp" | "strncasecmp" | "strlen" => {
            contract(&[R, R], N, Ret::None)
        }
        "strcpy" | "strncpy" | "strcat" | "strncat" => contract(&[W, R], N, Ret::Arg(0)),
        "strchr" | "strrchr" => contract(&[R], N, Ret::Arg(0)),
        "strstr" => contract(&[R, R], N, Ret::Arg(0)),
        "strtok" => contract(&[RW, R], N, Ret::Strtok),
        "strtoul" | "strtoumax" => Contract {
            store: Some((1, 0)),
            ..contract(&[R, W], N, Ret::None)
        },
        "atof" | "atoi" | "atoll" => contract(&[R], N, Ret::None),
        "getenv" => contract(&[R], N, Ret::Opaque),
        "strerror" => contract(&[], N, Ret::Opaque),
        // Formatted output and input.
        "printf" | "puts" | "perror" | "printw" | "__assert_fail" | "__assert_rtn" => {
            contract(&[R], R, Ret::None)
        }
        "mvprintw" => contract(&[], R, Ret::None),
        "fprintf" | "fputs" => contract(&[RW, R], R, Ret::None),
        "sprintf" | "snprintf" => contract(&[W], R, Ret::None),
        "sscanf" => contract(&[R, R], W, Ret::None),
        "fscanf" => contract(&[RW, R], W, Ret::None),
        // Files.
        "fopen" | "fdopen" | "popen" => contract(&[R, R], N, Ret::Opaque),
        "fclose" | "pclose" | "fflush" | "feof" | "ferror" | "fileno" | "fgetc" | "getc"
        | "_IO_getc" | "fseek" | "ftell" | "rewind" => contract(&[RW], N, Ret::None),
        "ungetc" | "fputc" | "putc" | "_IO_putc" => contract(&[N, RW], N, Ret::None),
        "fread" => contract(&[W, N, N, RW], N, Ret::None),
        "fwrite" => contract(&[R, N, N, RW], N, Ret::None),
        "fgets" => contract(&[W, N, RW], N, Ret::Arg(0)),
        "open" | "chmod" | "chown" | "unlink" | "remove" => contract(&[R], N, Ret::None),
        "utime" => contract(&[R, R], N, Ret::None),
        "read" => contract(&[N, W], N, Ret::None),
        "write" => contract(&[N, R], N, Ret::None),
        "stat" | "lstat" => contract(&[R, W], N, Ret::None),
        "__xstat" => contract(&[N, R, W], N, Ret::None),
        "uname" | "time" => contract(&[W], N, Ret::None),
        "glob" => Contract {
            callback: true,
            ..contract(&[R, N, N, RW], N, Ret::None)
        },
        "globfree" => contract(&[RW], N, Ret::None),
        // No pointer argument, or only a pointer the library owns.
        "close"
        | "fchmod"
        | "fchown"
        | "isatty"
        | "clock"
        | "rand"
        | "srand"
        | "sleep"
        | "exit"
        | "_exit"
        | "abort"
        | "abs"
        | "acos"
        | "acosf"
        | "asin"
        | "atan"
        | "atan2"
        | "ceil"
        | "cos"
        | "cosf"
        | "cosh"
        | "exp"
        | "fabs"
        | "fabsf"
        | "floor"
        | "fmax"
        | "fmin"
        | "fmod"
        | "log"
        | "log10"
        | "log2"
        | "pow"
        | "sin"
        | "sinf"
        | "sinh"
        | "sqrt"
        | "sqrtf"
        | "tan"
        | "tanh"
        | "omp_get_max_threads"
        | "__maskrune" => contract(&[], N, Ret::None),
        "__errno_location" | "__error" | "__ctype_b_loc" | "initscr" => {
            contract(&[], N, Ret::Opaque)
        }
        // A signal handler may touch only `volatile sig_atomic_t` and lock-free atomic
        // objects on a UB-free input (C11 7.14.1.1), never a subject's object.
        "signal" => contract(&[], N, Ret::None),
        // `longjmp` reads its buffer.
        "longjmp" => contract(&[R], N, Ret::None),
        // curses: the window is library memory.
        "cbreak" | "endwin" | "has_colors" | "init_pair" | "intrflush" | "keypad" | "noecho"
        | "nonl" | "start_color" | "waddch" | "wattrset" | "wclear" | "wclrtoeol" | "wgetch"
        | "wmove" | "wrefresh" => contract(&[RW], N, Ret::None),
        "waddnstr" => contract(&[RW, R], N, Ret::None),
        "wattr_get" => contract(&[RW, W, W, W], N, Ret::None),
        _ => return None,
    })
}

/// Rust pointer methods whose result is derived from their receiver.
const DERIVING: &[&str] = &[
    "offset",
    "add",
    "sub",
    "wrapping_offset",
    "wrapping_add",
    "wrapping_sub",
    "byte_offset",
    "wrapping_byte_offset",
    "cast",
    "cast_mut",
    "cast_const",
    "as_ptr",
    "as_mut_ptr",
];
/// Rust library calls with no pointer effect and no pointer result.
const RUST_INERT: &[&str] = &[
    "is_null",
    "offset_from",
    "is_none",
    "is_some",
    "size_of",
    "eq",
    "panic_fmt",
    "new_const",
    "leading_zeros",
    "trailing_zeros",
    "wrapping_div",
    "wrapping_mul",
    "wrapping_rem",
];

fn is_ptr(ty: Ty<'_>) -> bool {
    matches!(ty.kind(), TyKind::RawPtr(..) | TyKind::Ref(..))
}

fn is_byte_scalar(ty: Ty<'_>) -> bool {
    matches!(
        ty.kind(),
        TyKind::Int(rustc_middle::ty::IntTy::I8) | TyKind::Uint(rustc_middle::ty::UintTy::U8)
    )
}

fn local_of(op: &Operand<'_>) -> Option<Local> {
    op.place()
        .filter(|place| place.projection.is_empty())
        .map(|place| place.local)
}

/// The flow-insensitive relation over the whole program.
struct Relation<'tcx> {
    tcx: TyCtxt<'tcx>,
    options: Options,
    types: Vec<Ty<'tcx>>,
    type_ids: FxHashMap<Ty<'tcx>, TyId>,
    points: FxHashMap<(LocalDefId, Local), FxHashSet<Obj>>,
    contents: FxHashMap<Key, FxHashSet<Obj>>,
    held: FxHashMap<Obj, FxHashSet<Key>>,
    obj_types: FxHashMap<Obj, FxHashSet<TyId>>,
    retained: FxHashSet<(LocalDefId, Local)>,
    vias: FxHashMap<(LocalDefId, Local), FxHashSet<Via>>,
    from_param: FxHashMap<(LocalDefId, Local), FxHashSet<usize>>,
    /// The objects whose bytes an integer local may hold (R8).
    byte_from: FxHashMap<(LocalDefId, Local), FxHashSet<Obj>>,
    /// Pointer locals whose address is taken (R4).
    addr_taken: FxHashSet<(LocalDefId, Local)>,
    /// The objects `strtok`'s first argument may be, crate-wide.
    strtok: FxHashSet<Obj>,
    /// 2.1: objects whose memory an outside caller (or the library) filled: a load from
    /// them yields the outside object of its pointee type.
    outside_backed: FxHashSet<Obj>,
    /// 2.11: the objects whose bytes an object's integer memory may hold.
    int_mem: FxHashMap<Obj, FxHashSet<Obj>>,
    /// Members: (parent, struct, field), and each member's own type.
    subs: Vec<(Obj, DefId, usize)>,
    sub_ids: FxHashMap<(Obj, DefId, usize), u32>,
    sub_types: Vec<Option<TyId>>,
    /// Locals holding a member's address cast to a byte pointer (the container-of rule).
    byte_member: FxHashSet<(LocalDefId, Local)>,
    /// A change the fixpoint must see that no `changed` flag carries.
    dirty: bool,
    /// Byte views of a member already moved by an offset.
    byte_moved: FxHashSet<(LocalDefId, Local)>,
    /// 2.3: the program objects (roots) handed to the outside.
    escaped: FxHashSet<Obj>,
    /// H4: functions handed to outside code that may call them.
    handed_callbacks: FxHashSet<LocalDefId>,
    /// M1: a pointer has reached an output.
    exposed_output: bool,
    /// The closed world's fresh objects: (the entry argument's fresh id it is reached
    /// from, or itself; how it is reached), interned.
    fresh: Vec<(u32, FreshWay)>,
    fresh_ids: FxHashMap<(u32, FreshWay), u32>,
    /// Program memory a copy filled from fresh memory: the fresh roots it holds.
    fresh_backed: FxHashMap<Obj, FxHashSet<u32>>,
    /// P8's receipt (relay 176): R1 lifted for one overlap test at a time.
    r1_lifted: std::cell::Cell<bool>,
    /// The container-of sites: an unbounded offset from a member's byte view.
    container_of: FxHashSet<(LocalDefId, Local)>,
    anon: FxHashMap<AllocId, u32>,
    acc: FxHashMap<LocalDefId, FxHashSet<Access>>,
    param_acc: FxHashMap<(LocalDefId, usize), (bool, bool)>,
    exposed: FxHashSet<LocalDefId>,
    called: FxHashSet<LocalDefId>,
    cell_loads: FxHashSet<(LocalDefId, Obj, TyId)>,
    address_taken: FxHashSet<LocalDefId>,
    foreign_taken: FxHashSet<DefId>,
    allocators: FxHashSet<LocalDefId>,
    functions: Vec<LocalDefId>,
}

impl<'tcx> Relation<'tcx> {
    fn on(&self, rule: Rule) -> bool {
        self.options.fault != Some(rule) && self.options.faults & (1u64 << rule as u64) == 0
    }

    fn new(program: &RustProgram<'tcx>, options: Options) -> Self {
        let mut this = Self {
            tcx: program.tcx,
            options,
            types: Vec::new(),
            type_ids: FxHashMap::default(),
            points: FxHashMap::default(),
            contents: FxHashMap::default(),
            held: FxHashMap::default(),
            obj_types: FxHashMap::default(),
            retained: FxHashSet::default(),
            vias: FxHashMap::default(),
            from_param: FxHashMap::default(),
            byte_from: FxHashMap::default(),
            addr_taken: FxHashSet::default(),
            strtok: FxHashSet::default(),
            outside_backed: FxHashSet::default(),
            int_mem: FxHashMap::default(),
            subs: Vec::new(),
            sub_ids: FxHashMap::default(),
            sub_types: Vec::new(),
            byte_member: FxHashSet::default(),
            dirty: false,
            byte_moved: FxHashSet::default(),
            escaped: FxHashSet::default(),
            handed_callbacks: FxHashSet::default(),
            exposed_output: false,
            fresh: Vec::new(),
            fresh_ids: FxHashMap::default(),
            fresh_backed: FxHashMap::default(),
            r1_lifted: std::cell::Cell::new(false),
            container_of: FxHashSet::default(),
            anon: FxHashMap::default(),
            acc: FxHashMap::default(),
            param_acc: FxHashMap::default(),
            exposed: FxHashSet::default(),
            called: FxHashSet::default(),
            cell_loads: FxHashSet::default(),
            address_taken: FxHashSet::default(),
            foreign_taken: FxHashSet::default(),
            allocators: FxHashSet::default(),
            functions: program.functions.clone(),
        };
        this.find_exposed(program);
        this.find_called();
        this.find_handed_callbacks();
        this.find_addr_taken();
        this.find_allocators();
        this.seed_statics();
        let trace = std::env::var("CRAT_E5C_HOLD_TRACE").is_ok();
        let started = std::time::Instant::now();
        let mark = |what: &str| {
            if trace {
                eprintln!(
                    "E5C_HOLD_TRACE {what} {:.1} s",
                    started.elapsed().as_secs_f64()
                );
            }
        };
        this.solve_points();
        mark("points");
        this.compute_escapes();
        mark("escapes");
        while !this.options.closed
            && this.on(Rule::Escape)
            && this.on(Rule::IncomingStores)
            && this.publish()
        {
            this.solve_points();
            mark("points again");
            this.compute_escapes();
            mark("escapes again");
        }
        this.solve_accesses();
        mark("accesses");
        this
    }

    fn body(&self, f: LocalDefId) -> impl std::ops::Deref<Target = Body<'tcx>> + 'tcx {
        self.tcx.mir_drops_elaborated_and_const_checked(f).borrow()
    }

    fn ty_id(&mut self, ty: Ty<'tcx>) -> TyId {
        let ty = self.tcx.erase_regions(ty);
        if let Some(&id) = self.type_ids.get(&ty) {
            return id;
        }
        let id = self.types.len();
        self.types.push(ty);
        self.type_ids.insert(ty, id);
        id
    }

    /// Does a value of `ty` carry a data pointer (by value, at any depth)?
    fn carries_ptr(&self, ty: Ty<'tcx>, depth: usize) -> bool {
        if depth > 8 {
            return true;
        }
        match ty.kind() {
            TyKind::RawPtr(..) | TyKind::Ref(..) => true,
            TyKind::Adt(adt, args) => adt.all_fields().any(|field| {
                self.carries_ptr(self.tcx.erase_regions(field.ty(self.tcx, args)), depth + 1)
            }),
            TyKind::Array(element, _) | TyKind::Slice(element) => {
                self.carries_ptr(*element, depth + 1)
            }
            TyKind::Tuple(items) => items.iter().any(|ty| self.carries_ptr(ty, depth + 1)),
            _ => false,
        }
    }

    fn find_called(&mut self) {
        for &f in &self.functions.clone() {
            let body = self.body(f);
            for block in body.basic_blocks.indices() {
                for g in self.call_targets(&body, block) {
                    if g != f {
                        self.called.insert(g);
                    }
                }
            }
        }
    }

    /// The function items each local may hold: a fn item constant, through `Use`,
    /// casts and aggregates (c2rust's `Some(f)`), to a fixpoint (H4, H5).
    fn fn_items_of(&self, body: &Body<'tcx>) -> FxHashMap<Local, FxHashSet<DefId>> {
        let mut out: FxHashMap<Local, FxHashSet<DefId>> = FxHashMap::default();
        loop {
            let mut grew = false;
            for data in body.basic_blocks.iter() {
                for statement in &data.statements {
                    let StatementKind::Assign(box (dst, rvalue)) = &statement.kind else {
                        continue;
                    };
                    let ops: Vec<&Operand<'tcx>> = match rvalue {
                        Rvalue::Use(op) | Rvalue::Cast(_, op, _) => vec![op],
                        Rvalue::Aggregate(_, ops) => ops.iter().collect(),
                        _ => continue,
                    };
                    let mut items = FxHashSet::default();
                    for op in ops {
                        items.extend(self.fn_items_in(op, &out));
                    }
                    if !items.is_empty() {
                        let set = out.entry(dst.local).or_default();
                        let before = set.len();
                        set.extend(items);
                        grew |= set.len() != before;
                    }
                }
            }
            if !grew {
                return out;
            }
        }
    }

    fn fn_items_in(
        &self,
        op: &Operand<'tcx>,
        locals: &FxHashMap<Local, FxHashSet<DefId>>,
    ) -> FxHashSet<DefId> {
        match op {
            Operand::Constant(c) => match c.ty().kind() {
                TyKind::FnDef(d, _) => FxHashSet::from_iter([*d]),
                _ => FxHashSet::default(),
            },
            Operand::Copy(place) | Operand::Move(place) => {
                locals.get(&place.local).cloned().unwrap_or_default()
            }
        }
    }

    /// H4: functions handed to code outside the program that may call them (an
    /// unlisted foreign function, a callback contract, a call with no known target):
    /// the outside calls them with its own objects, even when the program calls them too.
    fn find_handed_callbacks(&mut self) {
        if !self.on(Rule::Callbacks) {
            return;
        }
        let tcx = self.tcx;
        for &f in &self.functions.clone() {
            let body = self.body(f);
            let items = self.fn_items_of(&body);
            for (block, data) in body.basic_blocks.iter_enumerated() {
                let Some(call) = as_call(data.terminator(), tcx) else { continue };
                let calls_back = match &call.func {
                    CallKind::LibC(name) => contract_of(name.as_str()).is_none_or(|c| c.callback),
                    CallKind::Closure | CallKind::Dynamic => {
                        self.call_targets(&body, block).is_empty()
                            || !self.foreign_targets(&body, block).is_empty()
                    }
                    CallKind::RustLib(_) | CallKind::FreeStanding(_) | CallKind::Impl(_) => false,
                };
                if !calls_back {
                    continue;
                }
                for arg in call.args.iter() {
                    for d in self.fn_items_in(&arg.node, &items) {
                        if let Some(g) = d.as_local()
                            && self.functions.contains(&g)
                        {
                            self.handed_callbacks.insert(g);
                        }
                    }
                }
            }
        }
    }

    fn direct_call(body: &Body<'tcx>, block: BasicBlock) -> bool {
        matches!(&body.basic_blocks[block].terminator().kind,
            TerminatorKind::Call { func, .. } if func.constant().is_some())
    }

    /// Function items a body takes by value (casts, aggregates, call arguments).
    fn note_fn_items(&mut self, body: &Body<'tcx>) {
        let tcx = self.tcx;
        let mut note = |op: &Operand<'tcx>| {
            if let Some(c) = op.constant()
                && let TyKind::FnDef(target, _) = c.ty().kind()
            {
                // A C library function declared in the crate's own `extern` block is a
                // local item, but a foreign one (era-5c 139: binn's `malloc_fn = malloc`).
                match target.as_local().filter(|_| !tcx.is_foreign_item(*target)) {
                    Some(local) => {
                        self.address_taken.insert(local);
                    }
                    None => {
                        self.foreign_taken.insert(*target);
                    }
                }
            }
        };
        for data in body.basic_blocks.iter() {
            for statement in &data.statements {
                if let StatementKind::Assign(box (_, Rvalue::Cast(_, op, _))) = &statement.kind {
                    note(op);
                }
                if let StatementKind::Assign(box (_, Rvalue::Aggregate(_, ops))) = &statement.kind {
                    ops.iter().for_each(&mut note);
                }
            }
            if let TerminatorKind::Call { args, .. } = &data.terminator().kind {
                args.iter().for_each(|a| note(&a.node));
            }
        }
    }

    fn find_exposed(&mut self, program: &RustProgram<'tcx>) {
        let tcx = self.tcx;
        for &f in &program.functions {
            if tcx.visibility(f.to_def_id()).is_public() {
                self.exposed.insert(f);
            }
            let body = self.body(f);
            self.note_fn_items(&body);
        }
        for def in tcx.hir_crate_items(()).definitions() {
            if matches!(tcx.def_kind(def), rustc_hir::def::DefKind::Static { .. })
                && !tcx.is_foreign_item(def.to_def_id())
            {
                let body = tcx.mir_for_ctfe(def.to_def_id());
                self.note_fn_items(body);
            }
        }
        let functions: FxHashSet<LocalDefId> = program.functions.iter().copied().collect();
        self.address_taken.retain(|f| functions.contains(f));
        let taken = self.address_taken.clone();
        self.exposed.extend(taken);
    }

    /// R4: the pointer locals whose address the body takes.
    fn find_addr_taken(&mut self) {
        if !self.on(Rule::AddressTaken) {
            return;
        }
        for &f in &self.functions.clone() {
            let body = self.body(f);
            for data in body.basic_blocks.iter() {
                for statement in &data.statements {
                    if let StatementKind::Assign(box (
                        _,
                        Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place),
                    )) = &statement.kind
                        && place.projection.is_empty()
                        && is_ptr(body.local_decls[place.local].ty)
                    {
                        self.addr_taken.insert((f, place.local));
                    }
                }
            }
        }
    }

    /// The object of a constant pointer's target allocation.
    fn alloc_obj(&mut self, id: AllocId, pointee: Option<Ty<'tcx>>) -> Option<Obj> {
        match self.tcx.global_alloc(id) {
            GlobalAlloc::Static(def) => Some(Obj::Global(def)),
            GlobalAlloc::Memory(memory) => {
                let next = self.anon.len() as u32;
                let fresh = !self.anon.contains_key(&id);
                let n = *self.anon.entry(id).or_insert(next);
                let obj = Obj::Anon(n);
                if let Some(pointee) = pointee {
                    let ty = self.ty_id(pointee);
                    self.obj_types.entry(obj).or_default().insert(ty);
                }
                if fresh {
                    // Anonymous memory may itself hold pointers.
                    let targets: Vec<AllocId> = memory
                        .inner()
                        .provenance()
                        .ptrs()
                        .iter()
                        .map(|(_, prov)| prov.alloc_id())
                        .collect();
                    let mut objs = FxHashSet::default();
                    for target in targets {
                        if let Some(o) = self.alloc_obj(target, None) {
                            objs.insert(o);
                        }
                    }
                    self.store(Key::Init(obj), &objs);
                }
                Some(obj)
            }
            GlobalAlloc::Function { .. } | GlobalAlloc::VTable(..) => None,
        }
    }

    /// R3: a static's initializer stores the objects its relocations name.
    fn seed_statics(&mut self) {
        let tcx = self.tcx;
        for def in tcx.hir_crate_items(()).definitions() {
            if !matches!(tcx.def_kind(def), rustc_hir::def::DefKind::Static { .. })
                || tcx.is_foreign_item(def.to_def_id())
            {
                continue;
            }
            let holder = Obj::Global(def.to_def_id());
            let objs: FxHashSet<Obj> = if !self.on(Rule::StaticInit) {
                FxHashSet::default()
            } else {
                match tcx.eval_static_initializer(def.to_def_id()) {
                    Ok(alloc) => {
                        let targets: Vec<AllocId> = alloc
                            .inner()
                            .provenance()
                            .ptrs()
                            .iter()
                            .map(|(_, prov)| prov.alloc_id())
                            .collect();
                        targets
                            .into_iter()
                            .filter_map(|id| self.alloc_obj(id, None))
                            .collect()
                    }
                    Err(_) => FxHashSet::from_iter([Obj::Top]),
                }
            };
            self.store(Key::Init(holder), &objs);
        }
    }

    fn sub(&mut self, parent: Obj, did: DefId, index: usize) -> Obj {
        // A member exists only of an object of the field's own struct (3.1, 3.2). Through
        // a cast (the first-member conversion) the field belongs to the nearest enclosing
        // member of that struct; with none, or with an object of unknown or mixed type
        // (a union's storage, an array, an allocation typed two ways), the access is to
        // the whole object. This also bounds the paths by the types' nesting.
        let mut parent = parent;
        while !self.is_struct(parent, did) {
            match parent {
                Obj::Sub(id) => parent = self.subs[id as usize].0,
                _ => return parent,
            }
        }
        let key = (parent, did, index);
        if let Some(&id) = self.sub_ids.get(&key) {
            return Obj::Sub(id);
        }
        let id = self.subs.len() as u32;
        self.subs.push(key);
        self.sub_ids.insert(key, id);
        let ty = self.field_ty(did, index).map(|ty| self.ty_id(ty));
        self.sub_types.push(ty);
        Obj::Sub(id)
    }

    /// Is `obj` an object of the struct `did`, and of that type alone?
    fn is_struct(&self, obj: Obj, did: DefId) -> bool {
        let is = |ty: Ty<'tcx>| matches!(ty.kind(), TyKind::Adt(adt, _) if adt.did() == did);
        match obj {
            Obj::Sub(id) => self.sub_types[id as usize].is_some_and(|ty| is(self.types[ty])),
            Obj::Stack(f, local) => is(self.body(f).local_decls[local].ty),
            Obj::Global(d) => is(self.tcx.type_of(d).instantiate_identity()),
            Obj::Static(id) | Obj::External(id) => is(self.types[id]),
            Obj::Alloc(..) | Obj::Opaque(..) | Obj::Fresh(_) => {
                let types: Vec<Ty<'tcx>> = self
                    .obj_types
                    .get(&obj)
                    .into_iter()
                    .flatten()
                    .map(|&t| self.types[t])
                    .filter(|&t| !self.is_byte(t))
                    .collect();
                !types.is_empty() && types.into_iter().all(is)
            }
            Obj::Anon(_) | Obj::Top => false,
        }
    }

    /// The whole object a member belongs to.
    fn root(&self, obj: Obj) -> Obj {
        match obj {
            Obj::Sub(id) => self.root(self.subs[id as usize].0),
            other => other,
        }
    }

    /// The member path from the root, outermost first.
    fn path(&self, obj: Obj) -> Vec<(DefId, usize)> {
        match obj {
            Obj::Sub(id) => {
                let (parent, did, index) = self.subs[id as usize];
                let mut path = self.path(parent);
                path.push((did, index));
                path
            }
            _ => vec![],
        }
    }

    /// The struct fields a place selects after projection `from`, outermost first,
    /// stopping at anything but a struct field (a union's members overlap).
    fn field_path(
        &self,
        body: &Body<'tcx>,
        place: Place<'tcx>,
        from: usize,
    ) -> Vec<(DefId, usize)> {
        let mut path = vec![];
        for k in from..place.projection.len() {
            let ProjectionElem::Field(field, _) = place.projection[k] else { break };
            let base = Place {
                local: place.local,
                projection: self.tcx.mk_place_elems(&place.projection[..k]),
            }
            .ty(body, self.tcx)
            .ty;
            match base.kind() {
                TyKind::Adt(adt, _) if adt.is_struct() => path.push((adt.did(), field.index())),
                _ => break,
            }
        }
        path
    }

    /// `objs` narrowed to the member `path`.
    fn members(&mut self, objs: FxHashSet<Obj>, path: &[(DefId, usize)]) -> FxHashSet<Obj> {
        if path.is_empty() || !self.on(Rule::Members) {
            return objs;
        }
        let mut out = FxHashSet::default();
        for obj in objs {
            if obj == Obj::Top {
                out.insert(obj);
                continue;
            }
            let mut member = obj;
            for &(did, index) in path {
                member = self.sub(member, did, index);
            }
            out.insert(member);
        }
        out
    }

    /// A cast of a member's address: to another struct or union pointee it may be the
    /// container's (C's first-member conversion), so the whole object too; to a byte
    /// pointer it is a byte view of the member (the container-of rule watches it).
    fn member_cast(
        &mut self,
        f: LocalDefId,
        body: &Body<'tcx>,
        dst: Place<'tcx>,
        source: Option<Local>,
        from: Ty<'tcx>,
        to: Ty<'tcx>,
        value: &mut Value,
    ) {
        let _ = body;
        if !self.on(Rule::Members) || !value.objs.iter().any(|o| matches!(o, Obj::Sub(_))) {
            return;
        }
        let pointee = to.builtin_deref(true);
        let aggregate = pointee.is_some_and(|t| {
            matches!(t.kind(), TyKind::Adt(adt, _) if (adt.is_struct() || adt.is_union()) && !self.is_byte(t))
        });
        if aggregate && from.builtin_deref(true) != pointee && self.on(Rule::MemberCast) {
            // The void cast (relay 176): a member's address converted to its own type
            // (through `void *`) is that member (C11 6.3.2.3p1: the round trip compares
            // equal to the original; a struct contains no object of its own type). Only
            // a conversion to another struct reaches a container.
            let target = pointee.map(|t| self.tcx.erase_regions(t));
            let roots: Vec<Obj> = value
                .objs
                .iter()
                .filter(|&&o| match o {
                    Obj::Sub(id) => {
                        !(self.on(Rule::VoidCast)
                            && self.sub_types[id as usize].map(|t| self.types[t]) == target)
                    }
                    _ => false,
                })
                .map(|&o| self.root(o))
                .collect();
            value.objs.extend(roots);
        }
        if pointee.is_some_and(|t| self.is_byte(t)) && dst.projection.is_empty() {
            // H3 (b): a byte view re-cast keeps its source's mark: direct only from the
            // member's own address (a cast from a non-byte pointer) or a direct view.
            let from_byte = from.builtin_deref(true).is_some_and(|t| self.is_byte(t));
            let direct = !from_byte
                || !self.on(Rule::ViewValues)
                || source.is_some_and(|l| self.byte_member.contains(&(f, l)));
            if direct {
                self.dirty |= self.byte_member.insert((f, dst.local));
            } else {
                self.dirty |= self.byte_moved.insert((f, dst.local));
            }
        }
    }

    /// An offset of a byte view of a member. From the member's own address (a direct
    /// view) a constant offset inside the member's size stays in the member and leaves a
    /// moved view; any other offset — negative, non-constant, past the member, or from a
    /// moved view — may reach the whole object (container-of arithmetic). Arithmetic on a
    /// pointer of any other type stays in its member (C's subobject bounds; §28).
    fn member_offset(
        &mut self,
        f: LocalDefId,
        body: &Body<'tcx>,
        dst: Place<'tcx>,
        base: &Operand<'tcx>,
        offset: Option<&Operand<'tcx>>,
        value: &mut Value,
    ) {
        let marked = local_of(base);
        let direct = marked.is_some_and(|b| self.byte_member.contains(&(f, b)));
        let moved = marked.is_some_and(|b| self.byte_moved.contains(&(f, b)));
        // H3: the marks are on locals; a byte pointer loaded, passed or stored and
        // reaching a member is a view of it all the same, and not known to be direct.
        let byte_view = self.on(Rule::ViewValues)
            && base
                .ty(body, self.tcx)
                .builtin_deref(true)
                .is_some_and(|t| self.is_byte(t))
            && value.objs.iter().any(|o| matches!(o, Obj::Sub(_)));
        if !direct && !moved && !byte_view {
            return;
        }
        if dst.projection.is_empty() {
            self.dirty |= self.byte_moved.insert((f, dst.local));
        }
        let size = value
            .objs
            .iter()
            .map(|&o| match o {
                Obj::Sub(id) => {
                    let (_, did, index) = self.subs[id as usize];
                    self.field_ty(did, index)
                        .and_then(|ty| {
                            self.tcx
                                .layout_of(
                                    rustc_middle::ty::TypingEnv::fully_monomorphized()
                                        .as_query_input(ty),
                                )
                                .ok()
                        })
                        .map(|layout| layout.size.bytes() as i128)
                }
                _ => None,
            })
            .try_fold(i128::MAX, |min, size| size.map(|size| min.min(size)));
        let inside = match (direct, offset.and_then(|op| op.constant()), size) {
            (true, Some(c), Some(size)) => match c.const_.try_to_scalar_int() {
                Some(int) => (0..size).contains(&int.to_int(int.size())),
                None => false,
            },
            _ => false,
        };
        if !inside && self.on(Rule::ContainerOf) {
            self.dirty |= self.container_of.insert((f, dst.local));
            let roots = self.roots(value.objs.iter().copied());
            value.objs.extend(roots);
        }
    }

    /// An object the outside can reach without the program handing it over: a static
    /// (2.3: the program's globals count, exported or not), the outside's own memory, the
    /// library's, or anything.
    fn outside_reachable(obj: Obj) -> bool {
        matches!(
            obj,
            Obj::Global(_)
                | Obj::Static(_)
                | Obj::Anon(_)
                | Obj::External(_)
                | Obj::Opaque(..)
                | Obj::Top
        )
    }

    /// §3 (ii): may the access's pointee type alias `subject`'s?
    fn types_alias(&self, subject: Ty<'tcx>, a: &Access) -> bool {
        if a.obj == Obj::Top {
            return true;
        }
        let body = self.body(a.at.0);
        let Some(t) = body
            .local_decls
            .get(a.by)
            .and_then(|d| d.ty.builtin_deref(true))
        else {
            return true;
        };
        let (s, t) = (self.tcx.erase_regions(subject), self.tcx.erase_regions(t));
        self.is_byte(s)
            || self.is_byte(t)
            || self.same_ty(s, t)
            || self.contains(s, t, 0)
            || self.contains(t, s, 0)
    }

    /// The subject's objects meet the access's, or (by types) its type may alias.
    fn meets(&self, objs: &FxHashSet<Obj>, subject: Option<Ty<'tcx>>, a: &Access) -> bool {
        match subject {
            Some(ty) if self.options.by_types => self.types_alias(ty, a),
            _ => objs.iter().any(|&o| self.overlap(o, a.obj)),
        }
    }

    /// The closed world's fresh object `(root, way)`; `root` is `u32::MAX` for an
    /// argument itself.
    fn fresh_obj(&mut self, root: u32, way: FreshWay, ty: Option<Ty<'tcx>>) -> Obj {
        let key = (root, way);
        let id = match self.fresh_ids.get(&key) {
            Some(&id) => id,
            None => {
                let id = self.fresh.len() as u32;
                self.fresh.push(key);
                self.fresh_ids.insert(key, id);
                id
            }
        };
        let obj = Obj::Fresh(id);
        if let Some(ty) = ty {
            let t = self.ty_id(ty);
            self.obj_types.entry(obj).or_default().insert(t);
        }
        obj
    }

    /// The entry arguments' fresh roots whose memory `holder` (a root) is.
    fn fresh_sources(&self, holder: Obj) -> FxHashSet<u32> {
        let mut out = self.fresh_backed.get(&holder).cloned().unwrap_or_default();
        if let Obj::Fresh(id) = holder {
            let (root, _) = self.fresh[id as usize];
            out.insert(if root == u32::MAX { id } else { root });
        }
        out
    }

    /// R1 (P8, `OutsideByteViewDiscipline`) in force for this overlap test.
    fn r1(&self) -> bool {
        self.options.outside_bytes_disjoint && !self.r1_lifted.get()
    }

    /// Would `objs` meet `obj` without P8? Only asked where they do not meet with it.
    fn meets_without_p8(&self, objs: &FxHashSet<Obj>, obj: Obj) -> bool {
        if !self.options.outside_bytes_disjoint {
            return false;
        }
        self.r1_lifted.set(true);
        let meets = objs.iter().any(|&o| self.overlap(o, obj));
        self.r1_lifted.set(false);
        meets
    }

    fn is_escaped(&self, obj: Obj) -> bool {
        let root = self.root(obj);
        Self::outside_reachable(root) || self.escaped.contains(&root)
    }

    /// 2.3: what the program hands to the outside. Seeds: the results of exposed and
    /// address-taken functions (an outside caller receives them); every argument of a
    /// foreign call that may keep it (an unlisted function, `strtok`), and of a call
    /// through a function pointer with no known target or such a foreign one (callback
    /// arguments); a pointer made an integer (its provenance exposed);
    /// the integer bytes of a pointer passed or returned the same ways. Closure: what an
    /// escaped or outside-reachable object holds (stores into outside memory are the
    /// out-parameters), its pointer bytes included.
    fn compute_escapes(&mut self) {
        let tcx = self.tcx;
        let mut seeds: FxHashSet<Obj> = FxHashSet::default();
        let functions = self.functions.clone();
        for &f in &functions {
            let body = self.body(f);
            if self.exposed.contains(&f) || self.address_taken.contains(&f) {
                let ret = Local::from_usize(0);
                let ty = body.local_decls[ret].ty;
                if is_ptr(ty) {
                    seeds.extend(self.points.get(&(f, ret)).into_iter().flatten().copied());
                } else if ty.is_integral() {
                    seeds.extend(self.byte_from.get(&(f, ret)).into_iter().flatten().copied());
                } else if self.carries_ptr(ty, 0) {
                    seeds.insert(Obj::Stack(f, ret));
                }
            }
            for (block, data) in body.basic_blocks.iter_enumerated() {
                for statement in &data.statements {
                    if let StatementKind::Assign(box (
                        _,
                        Rvalue::Cast(
                            CastKind::PointerExposeProvenance | CastKind::Transmute,
                            op,
                            _,
                        ),
                    )) = &statement.kind
                    {
                        seeds.extend(self.handed(f, &body, op));
                    }
                }
                let Some(call) = as_call(data.terminator(), tcx) else { continue };
                // A listed contract is the call's whole effect: none of the table's
                // functions keeps an argument past the call but `strtok` (whose state
                // has its own rule, and whose argument is handed out here too). An
                // unlisted function, or a pointer call with no known or an unlisted
                // target, keeps anything.
                let retains = |d: DefId| {
                    let name = tcx.item_name(d);
                    contract_of(name.as_str()).is_none() || name.as_str() == "strtok"
                };
                let foreign = match &call.func {
                    CallKind::LibC(name) => {
                        contract_of(name.as_str()).is_none() || name.as_str() == "strtok"
                    }
                    CallKind::Closure | CallKind::Dynamic => {
                        self.call_targets(&body, block).is_empty()
                            && self.foreign_targets(&body, block).is_empty()
                            || self.foreign_targets(&body, block).into_iter().any(retains)
                    }
                    CallKind::RustLib(_) | CallKind::FreeStanding(_) | CallKind::Impl(_) => false,
                };
                if foreign {
                    for arg in call.args.iter() {
                        seeds.extend(self.handed(f, &body, &arg.node));
                    }
                }
            }
        }
        let mut escaped: FxHashSet<Obj> = self.roots(seeds);
        loop {
            let mut next = FxHashSet::default();
            for (key, objs) in &self.contents {
                let holder = self.root(key.holder());
                if Self::outside_reachable(holder) || escaped.contains(&holder) {
                    next.extend(self.roots(objs.iter().copied()));
                }
            }
            for (holder, objs) in &self.int_mem {
                let holder = self.root(*holder);
                if Self::outside_reachable(holder) || escaped.contains(&holder) {
                    next.extend(self.roots(objs.iter().copied()));
                }
            }
            let before = escaped.len();
            escaped.extend(next);
            if escaped.len() == before {
                break;
            }
        }
        self.escaped = escaped;
    }

    /// 3.4: the escaped objects and the exported statics take the outside's stores.
    /// Whether anything new was marked.
    fn publish(&mut self) -> bool {
        let tcx = self.tcx;
        let mut published: Vec<Obj> = self.escaped.iter().copied().collect();
        for def in tcx.hir_crate_items(()).definitions() {
            if matches!(tcx.def_kind(def), rustc_hir::def::DefKind::Static { .. })
                && !tcx.is_foreign_item(def.to_def_id())
                && (tcx.visibility(def.to_def_id()).is_public()
                    || tcx.codegen_fn_attrs(def).contains_extern_indicator())
            {
                published.push(Obj::Global(def.to_def_id()));
            }
        }
        let mut grew = false;
        for obj in published {
            grew |= self.outside_backed.insert(obj);
        }
        grew
    }

    /// What passing `op` hands over: a pointer's objects, an aggregate's memory (its
    /// contents then escape by the closure), an integer's pointer bytes.
    fn handed(&mut self, f: LocalDefId, body: &Body<'tcx>, op: &Operand<'tcx>) -> FxHashSet<Obj> {
        let ty = op.ty(body, self.tcx);
        if is_ptr(ty) {
            self.operand_value(f, body, op).objs
        } else if ty.is_integral() {
            self.int_operand(f, body, op)
        } else if self.carries_ptr(ty, 0) {
            self.operand_memory(f, body, op)
        } else {
            FxHashSet::default()
        }
    }

    /// The objects with every member replaced by its whole object.
    fn roots(&self, objs: impl IntoIterator<Item = Obj>) -> FxHashSet<Obj> {
        objs.into_iter().map(|o| self.root(o)).collect()
    }

    /// The objects a place's innermost dereference reaches, or the local itself as a
    /// stack object when the place has no dereference.
    fn base_objects(
        &mut self,
        f: LocalDefId,
        body: &Body<'tcx>,
        place: Place<'tcx>,
    ) -> FxHashSet<Obj> {
        let last = place
            .projection
            .iter()
            .rposition(|p| matches!(p, ProjectionElem::Deref));
        match last {
            None => {
                let obj = Obj::Stack(f, place.local);
                let id = self.ty_id(body.local_decls[place.local].ty);
                self.obj_types.entry(obj).or_default().insert(id);
                FxHashSet::from_iter([obj])
            }
            Some(0) => {
                let objs = self
                    .points
                    .get(&(f, place.local))
                    .cloned()
                    .unwrap_or_default();
                self.roots(objs)
            }
            Some(k) => {
                let prefix = Place {
                    local: place.local,
                    projection: self.tcx.mk_place_elems(&place.projection[..k]),
                };
                let objs = self.load_value(f, body, prefix).objs;
                self.roots(objs)
            }
        }
    }

    /// The memory keys of a place with a projection, if it holds a pointer.
    fn keys_of(&mut self, f: LocalDefId, body: &Body<'tcx>, place: Place<'tcx>) -> Vec<Key> {
        if place.projection.is_empty() {
            return vec![];
        }
        let ty = place.ty(body, self.tcx).ty;
        if !is_ptr(ty) {
            return vec![];
        }
        // Exhaustive over projections: a field of a struct or an enum variant names its
        // place; a union's members are one place (R5); anything else is a cell.
        let field = match place.projection.last().expect("a projection") {
            ProjectionElem::Field(field, _) => {
                let base = Place {
                    local: place.local,
                    projection: self
                        .tcx
                        .mk_place_elems(&place.projection[..place.projection.len() - 1]),
                }
                .ty(body, self.tcx)
                .ty;
                match base.kind() {
                    TyKind::Adt(adt, _) if adt.is_union() && self.on(Rule::UnionMembers) => {
                        Some((adt.did(), 0))
                    }
                    TyKind::Adt(adt, _) => Some((adt.did(), field.index())),
                    _ => None,
                }
            }
            ProjectionElem::Deref
            | ProjectionElem::Index(_)
            | ProjectionElem::ConstantIndex { .. }
            | ProjectionElem::Subslice { .. }
            | ProjectionElem::Downcast(..)
            | ProjectionElem::OpaqueCast(_)
            | ProjectionElem::UnwrapUnsafeBinder(_)
            | ProjectionElem::Subtype(_) => None,
        };
        let cell = self.ty_id(ty);
        // `*p` with `p = &s->f`, `f` a pointer field, is the field itself.
        if field.is_none()
            && let [ProjectionElem::Deref] = place.projection.as_slice()
        {
            let erased = self.tcx.erase_regions(ty);
            let objs = self
                .points
                .get(&(f, place.local))
                .cloned()
                .unwrap_or_default();
            let mut keys = FxHashSet::default();
            for obj in objs {
                let root = self.root(obj);
                match self.path(obj).last() {
                    Some(&(did, index)) if self.field_ty(did, index) == Some(erased) => {
                        keys.insert(Key::Field(root, did, index));
                    }
                    _ => {
                        keys.insert(Key::Cell(root, cell));
                    }
                }
            }
            return keys.into_iter().collect();
        }
        self.base_objects(f, body, place)
            .into_iter()
            .map(|obj| match field {
                Some((did, index)) => Key::Field(obj, did, index),
                None => Key::Cell(obj, cell),
            })
            .collect()
    }

    fn store(&mut self, key: Key, objs: &FxHashSet<Obj>) -> bool {
        if objs.is_empty() {
            return false;
        }
        self.held.entry(key.holder()).or_default().insert(key);
        let set = self.contents.entry(key).or_default();
        let before = set.len();
        set.extend(objs.iter().copied());
        set.len() != before
    }

    /// A copy of memory: every pointer the source objects hold, the destination
    /// objects may hold. `Top` as a source holds anything.
    fn copy_memory(&mut self, from: &FxHashSet<Obj>, to: &FxHashSet<Obj>) -> bool {
        // 3.3: a copy between two pointer members moves one field's pointers into the
        // other (`memcpy(&h.b, &h.a)`).
        let pointer_member = |this: &Self, o: Obj| match o {
            Obj::Sub(id) => this.sub_types[id as usize]
                .is_some_and(|t| is_ptr(this.types[t]))
                .then(|| this.subs[id as usize]),
            _ => None,
        };
        let mut changed = false;
        let mut paired_targets = FxHashSet::default();
        if self.on(Rule::Members) {
            let pairs: Vec<(Obj, Obj)> = from
                .iter()
                .flat_map(|&s| to.iter().map(move |&t| (s, t)))
                .collect();
            for (s, t) in pairs {
                if let (Some((_, sd, si)), Some((_, td, ti))) =
                    (pointer_member(self, s), pointer_member(self, t))
                {
                    let (sr, tr) = (self.root(s), self.root(t));
                    let mut objs = FxHashSet::default();
                    for key in [Key::Field(sr, sd, si), Key::Init(sr)] {
                        objs.extend(self.contents.get(&key).into_iter().flatten().copied());
                    }
                    if let Some(ty) = self.field_ty(sd, si) {
                        let cell = self.ty_id(ty);
                        objs.extend(
                            self.contents
                                .get(&Key::Cell(sr, cell))
                                .into_iter()
                                .flatten()
                                .copied(),
                        );
                    }
                    changed |= self.store(Key::Field(tr, td, ti), &objs);
                    paired_targets.insert(t);
                }
            }
        }
        // H2 / 3.3: where the destination's type does not hold the source's field, the
        // pointer lands in a cell of its type (the cell rule joins it to every field of
        // that type); with the destination's type unknown, in both places.
        // 3.6 / H7: a copy into integer memory (a local, a field, an element) puts pointer
        // bytes there; an integer read of that memory carries the sources.
        if self.on(Rule::IntLocalMemory) {
            let integral = |t: Ty<'tcx>| match t.kind() {
                TyKind::Array(e, _) => e.is_integral(),
                _ => t.is_integral(),
            };
            let roots_from = self.roots(from.iter().copied());
            for &t in to {
                if self.obj_ty(t).is_some_and(integral) {
                    let set = self.int_mem.entry(self.root(t)).or_default();
                    let before = set.len();
                    set.extend(roots_from.iter().copied());
                    changed |= set.len() != before;
                }
            }
        }
        let target_types: Vec<(Obj, Option<Ty<'tcx>>)> = to
            .iter()
            .filter(|t| !paired_targets.contains(*t))
            .map(|&t| (self.root(t), self.obj_ty(t)))
            .collect();
        // Memory belongs to whole objects.
        let (from, to) = (
            &self.roots(from.iter().copied()),
            &self.roots(to.iter().copied()),
        );
        // 3.6: an integer local's memory holds its value's bytes: a copy out of it copies
        // the memory its byte provenance names.
        let mut from = from.clone();
        if self.on(Rule::ByteCopy) && self.on(Rule::IntLocalMemory) {
            let mut more = vec![];
            for &source in from.iter() {
                if let Obj::Stack(g, l) = source
                    && self.body(g).local_decls[l].ty.is_integral()
                {
                    more.extend(self.byte_from.get(&(g, l)).into_iter().flatten().copied());
                }
            }
            from.extend(self.roots(more));
        }
        let from = &from;
        if from.contains(&Obj::Top) {
            for &target in to {
                changed |= self.store(Key::Init(target), &FxHashSet::from_iter([Obj::Top]));
            }
        }
        for &source in from {
            let keys: Vec<Key> = self
                .held
                .get(&source)
                .into_iter()
                .flatten()
                .copied()
                .collect();
            for key in keys {
                let objs = self.contents.get(&key).cloned().unwrap_or_default();
                for &(target, ty) in &target_types {
                    for at in self.placed(key, target, ty) {
                        changed |= self.store(at, &objs);
                    }
                }
            }
            // R816-1: a copy of fresh memory holds what the client stored there.
            if self.options.closed {
                let sources = self.fresh_sources(source);
                if !sources.is_empty() {
                    for &target in to {
                        let set = self.fresh_backed.entry(target).or_default();
                        let before = set.len();
                        set.extend(sources.iter().copied());
                        changed |= set.len() != before;
                    }
                }
            }
            // 2.1: a copy of outside memory holds what the outside stored.
            if !self.options.closed
                && self.on(Rule::OutsideCopy)
                && (matches!(source, Obj::External(_) | Obj::Opaque(..))
                    || self.outside_backed.contains(&source))
            {
                for &target in to {
                    changed |= self.outside_backed.insert(target);
                }
            }
            // 2.11: integer memory carries its byte provenance with the copy.
            if let Some(bytes) = self.int_mem.get(&source).cloned() {
                for &target in to {
                    let set = self.int_mem.entry(target).or_default();
                    let before = set.len();
                    set.extend(bytes.iter().copied());
                    changed |= set.len() != before;
                }
            }
        }
        changed
    }

    /// Where a copied key lands in `target` of type `ty` (H2): a field of a struct the
    /// destination's type holds stays that field; any other field becomes a cell of its
    /// type; with the type unknown, both.
    fn placed(&mut self, key: Key, target: Obj, ty: Option<Ty<'tcx>>) -> Vec<Key> {
        let Key::Field(_, did, index) = key else { return vec![key.moved(target)] };
        if !self.on(Rule::CrossCopy) {
            return vec![key.moved(target)];
        }
        let cell = self.field_ty(did, index).map(|t| self.ty_id(t));
        let holds = |this: &Self, t: Ty<'tcx>| {
            matches!(t.kind(), TyKind::Adt(adt, _) if adt.did() == did)
                || this.contains(t, this.tcx.type_of(did).instantiate_identity(), 0)
        };
        match (ty, cell) {
            (Some(t), _) if holds(self, t) => vec![key.moved(target)],
            (Some(_), Some(cell)) => vec![Key::Cell(target, cell)],
            (None, Some(cell)) => vec![key.moved(target), Key::Cell(target, cell)],
            (_, None) => vec![key.moved(target), Key::Init(target)],
        }
    }

    /// The one type of an object, if it has exactly one (byte views aside).
    fn obj_ty(&self, obj: Obj) -> Option<Ty<'tcx>> {
        match obj {
            Obj::Sub(id) => self.sub_types[id as usize].map(|t| self.types[t]),
            Obj::Stack(f, local) => Some(self.body(f).local_decls[local].ty),
            Obj::Global(d) => Some(self.tcx.type_of(d).instantiate_identity()),
            Obj::Static(id) | Obj::External(id) => Some(self.types[id]),
            Obj::Alloc(..) | Obj::Opaque(..) | Obj::Fresh(_) => {
                let types: Vec<Ty<'tcx>> = self
                    .obj_types
                    .get(&obj)
                    .into_iter()
                    .flatten()
                    .map(|&t| self.types[t])
                    .filter(|&t| !self.is_byte(t))
                    .collect();
                (types.len() == 1).then(|| types[0])
            }
            Obj::Anon(_) | Obj::Top => None,
        }
    }

    /// 2.10: does the place pass through a union's member after its last dereference?
    fn under_union(&self, body: &Body<'tcx>, place: Place<'tcx>) -> bool {
        let start = place
            .projection
            .iter()
            .rposition(|p| matches!(p, ProjectionElem::Deref))
            .map_or(0, |k| k + 1);
        (start..place.projection.len()).any(|k| {
            matches!(place.projection[k], ProjectionElem::Field(..))
                && matches!(
                    Place {
                        local: place.local,
                        projection: self.tcx.mk_place_elems(&place.projection[..k]),
                    }
                    .ty(body, self.tcx)
                    .ty
                    .kind(),
                    TyKind::Adt(adt, _) if adt.is_union()
                )
        })
    }

    /// Store `value` (a pointer) at every key of `place`; for a local, assign it.
    fn put(&mut self, f: LocalDefId, body: &Body<'tcx>, place: Place<'tcx>, value: Value) -> bool {
        if place.projection.is_empty() {
            return self.add_value((f, place.local), value);
        }
        let mut changed = false;
        for key in self.keys_of(f, body, place) {
            changed |= self.store(key, &value.objs);
        }
        changed
    }

    fn add_value(&mut self, at: (LocalDefId, Local), value: Value) -> bool {
        let mut changed = false;
        if !value.objs.is_empty() {
            let set = self.points.entry(at).or_default();
            let before = set.len();
            set.extend(value.objs.iter().copied());
            changed |= set.len() != before;
        }
        if value.retained {
            changed |= self.retained.insert(at);
            let set = self.vias.entry(at).or_default();
            let before = set.len();
            set.extend(value.vias);
            changed |= set.len() != before;
        }
        if !value.params.is_empty() {
            let set = self.from_param.entry(at).or_default();
            let before = set.len();
            set.extend(value.params);
            changed |= set.len() != before;
        }
        changed
    }

    fn local_value(&self, f: LocalDefId, local: Local) -> Value {
        let at = (f, local);
        Value {
            objs: self.points.get(&at).cloned().unwrap_or_default(),
            retained: self.retained.contains(&at),
            vias: self.vias.get(&at).cloned().unwrap_or_default(),
            params: self.from_param.get(&at).cloned().unwrap_or_default(),
        }
    }

    /// The value of a pointer-typed operand.
    fn operand_value(&mut self, f: LocalDefId, body: &Body<'tcx>, op: &Operand<'tcx>) -> Value {
        match op {
            Operand::Copy(place) | Operand::Move(place) => {
                if place.projection.is_empty() {
                    self.local_value(f, place.local)
                } else {
                    self.load_value(f, body, *place)
                }
            }
            Operand::Constant(c) => self.const_pointer(c),
        }
    }

    /// A pointer-typed constant: null, a static's address, anonymous memory, or `Top`.
    fn const_pointer(&mut self, c: &rustc_middle::mir::ConstOperand<'tcx>) -> Value {
        let pointee = c.ty().builtin_deref(true);
        let obj = match c.const_.try_to_scalar() {
            Some(Scalar::Int(int)) if int.is_null() => return Value::default(),
            // An integer address: `Top`.
            Some(Scalar::Int(_)) => return self.top(),
            Some(Scalar::Ptr(ptr, _)) => self.alloc_obj(ptr.provenance.alloc_id(), pointee),
            None => return self.top(),
        };
        match obj {
            Some(obj) => {
                if let Some(pointee) = pointee
                    && matches!(obj, Obj::Global(_))
                {
                    let id = self.ty_id(pointee);
                    self.obj_types.entry(obj).or_default().insert(id);
                }
                Value::objs([obj])
            }
            None => Value::default(),
        }
    }

    /// `Top`, unless the witnesses' fault removes it.
    fn top(&self) -> Value {
        if self.on(Rule::TopFlows) {
            Value::top()
        } else {
            Value::default()
        }
    }

    /// Does `obj` hold cells of two or more pointer types?
    fn mixed(&self, obj: Obj) -> bool {
        let mut types = FxHashSet::default();
        for key in self.held.get(&obj).into_iter().flatten() {
            if let Key::Cell(_, ty) = key {
                types.insert(*ty);
            }
        }
        types.len() > 1
    }

    /// The type of field `index` of struct `did`.
    fn field_ty(&self, did: DefId, index: usize) -> Option<Ty<'tcx>> {
        let adt = self.tcx.adt_def(did);
        let field = adt.all_fields().nth(index)?;
        Some(
            self.tcx
                .erase_regions(self.tcx.type_of(field.did).instantiate_identity()),
        )
    }

    /// The value loaded from the memory place `place`.
    /// 2.2: what was stored through `Top`: it may be in any memory.
    fn wild(&self) -> FxHashSet<Obj> {
        if !self.on(Rule::TopStores) {
            return FxHashSet::default();
        }
        self.held
            .get(&Obj::Top)
            .into_iter()
            .flatten()
            .flat_map(|k| self.contents.get(k).into_iter().flatten().copied())
            .collect()
    }

    fn load_value(&mut self, f: LocalDefId, body: &Body<'tcx>, place: Place<'tcx>) -> Value {
        let mut value = Value {
            retained: true,
            ..Default::default()
        };
        let pointee = place.ty(body, self.tcx).ty.builtin_deref(true);
        // 2.2: what was stored through `Top` may be in any memory.
        let wild = self.wild();
        let union = self.on(Rule::UnionMembers) && self.under_union(body, place);
        for key in self.keys_of(f, body, place) {
            let mut objs = self.contents.get(&key).cloned().unwrap_or_default();
            objs.extend(wild.iter().copied());
            let holder = key.holder();
            if holder == Obj::Top {
                value.join(self.top());
            }
            // 2.10: a member of a union, at any depth, may be any of the holder's places.
            if union {
                let keys: Vec<Key> = self
                    .held
                    .get(&holder)
                    .into_iter()
                    .flatten()
                    .copied()
                    .collect();
                for other in keys {
                    objs.extend(self.contents.get(&other).into_iter().flatten().copied());
                }
            }
            objs.extend(
                self.contents
                    .get(&Key::Init(holder))
                    .into_iter()
                    .flatten()
                    .copied(),
            );
            if self.on(Rule::CellField) {
                let keys: Vec<Key> = self
                    .held
                    .get(&holder)
                    .into_iter()
                    .flatten()
                    .copied()
                    .collect();
                for other in keys {
                    let same = match (key, other) {
                        (Key::Cell(_, ty), Key::Field(_, did, index))
                        | (Key::Field(_, did, index), Key::Cell(_, ty)) => {
                            self.field_ty(did, index) == Some(self.types[ty])
                        }
                        _ => false,
                    };
                    if same {
                        objs.extend(self.contents.get(&other).into_iter().flatten().copied());
                    }
                }
            }
            if let Key::Cell(_, ty) = key {
                self.cell_loads.insert((f, holder, ty));
                if self.on(Rule::MixedUnion) && self.mixed(holder) {
                    let keys: Vec<Key> = self
                        .held
                        .get(&holder)
                        .into_iter()
                        .flatten()
                        .copied()
                        .collect();
                    for other in keys {
                        objs.extend(self.contents.get(&other).into_iter().flatten().copied());
                    }
                }
            }
            if self.options.closed {
                // R816-1: memory reached from an argument holds further fresh objects.
                // One summary object stands for an argument and everything reached from
                // it (conservative: they may meet each other; never another argument's,
                // never the program's); library memory points into library memory.
                let root = self.root(holder);
                for source in self.fresh_sources(root) {
                    let obj = Obj::Fresh(source);
                    if let Some(pointee) = pointee {
                        let t = self.ty_id(pointee);
                        self.obj_types.entry(obj).or_default().insert(t);
                    }
                    objs.insert(obj);
                }
                if matches!(root, Obj::Opaque(..)) {
                    objs.insert(root);
                }
            } else if self.on(Rule::OutsideLoad)
                && (matches!(holder, Obj::External(_) | Obj::Opaque(..))
                    || self.outside_backed.contains(&holder))
                && let Some(pointee) = pointee
            {
                let id = self.ty_id(pointee);
                let outside = Obj::External(id);
                self.obj_types.entry(outside).or_default().insert(id);
                objs.insert(outside);
            }
            if objs.contains(&Obj::Top) {
                value.vias.insert(Via::Unknown);
            }
            value.objs.extend(objs);
            value.vias.insert(match key {
                Key::Field(_, did, index) => Via::Field(did, index),
                Key::Cell(_, ty) => Via::Cell(ty),
                Key::Init(_) => Via::Unknown,
            });
        }
        value
    }

    fn type_objs(&mut self, objs: &FxHashSet<Obj>, ty: Ty<'tcx>) {
        let Some(pointee) = ty.builtin_deref(true) else { return };
        let id = self.ty_id(pointee);
        for &obj in objs {
            if matches!(obj, Obj::Alloc(..) | Obj::Opaque(..)) {
                self.obj_types.entry(obj).or_default().insert(id);
            }
        }
    }

    /// The library's memory a contract returns, typed by its pointee.
    fn opaque(&mut self, f: LocalDefId, block: BasicBlock, ty: Ty<'tcx>) -> Value {
        let obj = Obj::Opaque(f, block);
        self.type_objs(&FxHashSet::from_iter([obj]), ty);
        Value {
            objs: FxHashSet::from_iter([obj]),
            retained: true,
            vias: FxHashSet::from_iter([Via::Opaque]),
            params: FxHashSet::default(),
        }
    }

    /// A place read or written through a byte pointer: `*p` or `(*p)[i]`.
    fn byte_view(&self, body: &Body<'tcx>, place: Place<'tcx>) -> bool {
        matches!(place.projection.first(), Some(ProjectionElem::Deref))
            && place.projection[1..].iter().all(|p| {
                matches!(
                    p,
                    ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. }
                )
            })
            && is_byte_scalar(place.ty(body, self.tcx).ty)
    }

    /// The objects whose bytes an integer operand may hold: a byte read through a byte
    /// pointer, or an integer local that holds them (R8; R542's effective types make a
    /// character read the only way to read a pointer's representation).
    fn int_operand(
        &mut self,
        f: LocalDefId,
        body: &Body<'tcx>,
        op: &Operand<'tcx>,
    ) -> FxHashSet<Obj> {
        if !self.on(Rule::ByteCopy) {
            return FxHashSet::default();
        }
        match op {
            Operand::Copy(place) | Operand::Move(place) => {
                if place.projection.is_empty() {
                    let mut objs = self
                        .byte_from
                        .get(&(f, place.local))
                        .cloned()
                        .unwrap_or_default();
                    // 3.6: a local whose memory a copy wrote holds those bytes too (the
                    // copy recorded them as integer memory).
                    let memory = Obj::Stack(f, place.local);
                    objs.extend(self.int_mem.get(&memory).into_iter().flatten().copied());
                    objs
                } else if self.byte_view(body, *place) {
                    self.base_objects(f, body, *place)
                } else {
                    // 2.11: an integer read from memory: what that memory's integers hold.
                    let holders = self.base_objects(f, body, *place);
                    holders
                        .iter()
                        .flat_map(|h| self.int_mem.get(h).into_iter().flatten().copied())
                        .collect()
                }
            }
            Operand::Constant(_) => FxHashSet::default(),
        }
    }

    /// An integer value assigned: it carries its operands' byte provenance; stored as a
    /// byte through a byte pointer, it carries their pointers.
    fn assign_int(
        &mut self,
        f: LocalDefId,
        body: &Body<'tcx>,
        dst: Place<'tcx>,
        sources: FxHashSet<Obj>,
    ) -> bool {
        if sources.is_empty() {
            return false;
        }
        if dst.projection.is_empty() {
            let set = self.byte_from.entry((f, dst.local)).or_default();
            let before = set.len();
            set.extend(sources);
            return set.len() != before;
        }
        if self.byte_view(body, dst) {
            let targets = self.base_objects(f, body, dst);
            return self.copy_memory(&sources, &targets);
        }
        // 2.11: an integer stored into other memory keeps its byte provenance there.
        let mut changed = false;
        for holder in self.base_objects(f, body, dst) {
            let set = self.int_mem.entry(holder).or_default();
            let before = set.len();
            set.extend(sources.iter().copied());
            changed |= set.len() != before;
        }
        changed
    }

    /// An aggregate value assigned: the objects whose memory it copies.
    fn assign_memory(
        &mut self,
        f: LocalDefId,
        body: &Body<'tcx>,
        dst: Place<'tcx>,
        from: FxHashSet<Obj>,
    ) -> bool {
        if from.is_empty() || !self.on(Rule::CopyCarry) {
            return false;
        }
        let to = self.base_objects(f, body, dst);
        self.copy_memory(&from, &to)
    }

    /// The memory an aggregate-typed operand denotes.
    fn operand_memory(
        &mut self,
        f: LocalDefId,
        body: &Body<'tcx>,
        op: &Operand<'tcx>,
    ) -> FxHashSet<Obj> {
        match op {
            Operand::Copy(place) | Operand::Move(place) => self.base_objects(f, body, *place),
            Operand::Constant(c) => {
                // A constant aggregate: its relocations, as anonymous memory.
                let mut objs = FxHashSet::default();
                match c.const_ {
                    rustc_middle::mir::Const::Val(
                        rustc_middle::mir::ConstValue::Indirect { alloc_id, .. },
                        _,
                    ) => {
                        if let Some(obj) = self.alloc_obj(alloc_id, None) {
                            objs.insert(obj);
                        }
                    }
                    rustc_middle::mir::Const::Val(
                        rustc_middle::mir::ConstValue::ZeroSized
                        | rustc_middle::mir::ConstValue::Scalar(Scalar::Int(_)),
                        _,
                    ) => {}
                    _ => {
                        objs.extend(self.top().objs);
                    }
                }
                objs
            }
        }
    }

    /// One assignment, exhaustively over the rvalue kinds.
    fn assign(
        &mut self,
        f: LocalDefId,
        body: &Body<'tcx>,
        dst: Place<'tcx>,
        rvalue: &Rvalue<'tcx>,
    ) -> bool {
        let tcx = self.tcx;
        let dst_ty = dst.ty(body, tcx).ty;
        let mut changed = false;
        // Integers: byte provenance (R8).
        if dst_ty.is_integral() {
            let sources = match rvalue {
                Rvalue::Use(op)
                | Rvalue::Cast(_, op, _)
                | Rvalue::UnaryOp(_, op)
                | Rvalue::WrapUnsafeBinder(op, _)
                | Rvalue::Repeat(op, _) => self.int_operand(f, body, op),
                Rvalue::BinaryOp(_, box (a, b)) => {
                    let mut s = self.int_operand(f, body, a);
                    s.extend(self.int_operand(f, body, b));
                    s
                }
                Rvalue::CopyForDeref(place) => self.int_operand(f, body, &Operand::Copy(*place)),
                Rvalue::Ref(..)
                | Rvalue::ThreadLocalRef(_)
                | Rvalue::RawPtr(..)
                | Rvalue::Len(_)
                | Rvalue::NullaryOp(..)
                | Rvalue::Discriminant(_)
                | Rvalue::Aggregate(..)
                | Rvalue::ShallowInitBox(..) => FxHashSet::default(),
            };
            return self.assign_int(f, body, dst, sources);
        }
        // Pointers.
        if is_ptr(dst_ty) {
            let value = match rvalue {
                Rvalue::Use(op)
                | Rvalue::WrapUnsafeBinder(op, _)
                | Rvalue::ShallowInitBox(op, _) => self.operand_value(f, body, op),
                Rvalue::CopyForDeref(place) => self.operand_value(f, body, &Operand::Copy(*place)),
                Rvalue::Cast(kind, op, _) => match kind {
                    CastKind::PtrToPtr
                    | CastKind::PointerCoercion(
                        PointerCoercion::MutToConstPointer
                        | PointerCoercion::ArrayToPointer
                        | PointerCoercion::Unsize
                        | PointerCoercion::DynStar,
                        _,
                    ) => {
                        let mut value = self.operand_value(f, body, op);
                        self.type_objs(&value.objs, dst_ty);
                        self.member_cast(
                            f,
                            body,
                            dst,
                            local_of(op),
                            op.ty(body, tcx),
                            dst_ty,
                            &mut value,
                        );
                        value
                    }
                    // A code pointer as data: no object.
                    CastKind::FnPtrToPtr
                    | CastKind::PointerCoercion(
                        PointerCoercion::ReifyFnPointer
                        | PointerCoercion::UnsafeFnPointer
                        | PointerCoercion::ClosureFnPointer(_),
                        _,
                    ) => Value::default(),
                    CastKind::PointerWithExposedProvenance => match op.constant() {
                        Some(c) if c.const_.try_to_scalar_int().is_some_and(|v| v.is_null()) => {
                            Value::default()
                        }
                        // An integer made a pointer: anything exposed.
                        _ => self.top(),
                    },
                    CastKind::PointerExposeProvenance
                    | CastKind::IntToInt
                    | CastKind::FloatToInt
                    | CastKind::FloatToFloat
                    | CastKind::IntToFloat
                    | CastKind::Transmute => self.top(),
                },
                Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => {
                    self.address_value(f, body, *place)
                }
                Rvalue::ThreadLocalRef(def) => Value::objs([Obj::Global(*def)]),
                Rvalue::BinaryOp(BinOp::Offset, box (base, offset)) => {
                    let mut value = self.operand_value(f, body, base);
                    self.member_offset(f, body, dst, base, Some(offset), &mut value);
                    value
                }
                Rvalue::Aggregate(box AggregateKind::RawPtr(..), ops) => match ops.iter().next() {
                    Some(op) => self.operand_value(f, body, op),
                    None => Value::default(),
                },
                Rvalue::BinaryOp(..)
                | Rvalue::Repeat(..)
                | Rvalue::Len(_)
                | Rvalue::NullaryOp(..)
                | Rvalue::UnaryOp(..)
                | Rvalue::Discriminant(_)
                | Rvalue::Aggregate(..) => self.top(),
            };
            return self.put(f, body, dst, value);
        }
        // Aggregates that carry pointers.
        if self.carries_ptr(dst_ty, 0) {
            match rvalue {
                Rvalue::Use(op) | Rvalue::Cast(_, op, _) | Rvalue::WrapUnsafeBinder(op, _) => {
                    let from = self.operand_memory(f, body, op);
                    changed |= self.assign_memory(f, body, dst, from);
                }
                Rvalue::CopyForDeref(place) => {
                    let from = self.base_objects(f, body, *place);
                    changed |= self.assign_memory(f, body, dst, from);
                }
                Rvalue::Aggregate(kind, ops) => {
                    let region = self.base_objects(f, body, dst);
                    changed |= self.aggregate(f, body, kind, &ops.raw, &region);
                }
                Rvalue::Repeat(op, _) => {
                    let region = self.base_objects(f, body, dst);
                    changed |= self.element(f, body, op, &region);
                }
                Rvalue::Ref(..)
                | Rvalue::ThreadLocalRef(_)
                | Rvalue::RawPtr(..)
                | Rvalue::Len(_)
                | Rvalue::BinaryOp(..)
                | Rvalue::NullaryOp(..)
                | Rvalue::UnaryOp(..)
                | Rvalue::Discriminant(_)
                | Rvalue::ShallowInitBox(..) => {
                    let region = self.base_objects(f, body, dst);
                    let top = self.top().objs;
                    for obj in region {
                        changed |= self.store(Key::Init(obj), &top);
                    }
                }
            }
        }
        changed
    }

    /// An aggregate value's operands into the destination's memory, by kind.
    fn aggregate(
        &mut self,
        f: LocalDefId,
        body: &Body<'tcx>,
        kind: &AggregateKind<'tcx>,
        ops: &[Operand<'tcx>],
        region: &FxHashSet<Obj>,
    ) -> bool {
        let mut changed = false;
        match kind {
            AggregateKind::Adt(did, _, _, _, active) => {
                let adt = self.tcx.adt_def(*did);
                for (index, op) in ops.iter().enumerate() {
                    let index = if adt.is_union() && self.on(Rule::UnionMembers) {
                        0
                    } else {
                        active.map_or(index, |a| a.index())
                    };
                    let ty = op.ty(body, self.tcx);
                    if is_ptr(ty) {
                        let value = self.operand_value(f, body, op);
                        for &obj in region {
                            changed |= self.store(Key::Field(obj, *did, index), &value.objs);
                        }
                    } else if self.carries_ptr(ty, 0) {
                        let from = self.operand_memory(f, body, op);
                        changed |= self.copy_memory(&from, region);
                    }
                }
            }
            AggregateKind::Array(_) | AggregateKind::Tuple => {
                if self.on(Rule::ArrayInit) {
                    for op in ops {
                        changed |= self.element(f, body, op, region);
                    }
                }
            }
            AggregateKind::RawPtr(..) => {}
            AggregateKind::Closure(..)
            | AggregateKind::Coroutine(..)
            | AggregateKind::CoroutineClosure(..) => {
                let top = self.top().objs;
                for &obj in region {
                    changed |= self.store(Key::Init(obj), &top);
                }
            }
        }
        changed
    }

    /// One element of an array or tuple value: a pointer is a cell of its type.
    fn element(
        &mut self,
        f: LocalDefId,
        body: &Body<'tcx>,
        op: &Operand<'tcx>,
        region: &FxHashSet<Obj>,
    ) -> bool {
        let ty = op.ty(body, self.tcx);
        let mut changed = false;
        if is_ptr(ty) {
            let value = self.operand_value(f, body, op);
            let cell = self.ty_id(ty);
            for &obj in region {
                changed |= self.store(Key::Cell(obj, cell), &value.objs);
            }
        } else if self.carries_ptr(ty, 0) {
            let from = self.operand_memory(f, body, op);
            changed |= self.copy_memory(&from, region);
        }
        changed
    }

    /// The value of `&place` / `&raw place`.
    fn address_value(&mut self, f: LocalDefId, body: &Body<'tcx>, place: Place<'tcx>) -> Value {
        let last = place
            .projection
            .iter()
            .rposition(|p| matches!(p, ProjectionElem::Deref));
        let (mut value, from) = match last {
            Some(0) => (self.local_value(f, place.local), 1),
            Some(k) => {
                let prefix = Place {
                    local: place.local,
                    projection: self.tcx.mk_place_elems(&place.projection[..k]),
                };
                (self.load_value(f, body, prefix), k + 1)
            }
            None => {
                let obj = Obj::Stack(f, place.local);
                let id = self.ty_id(body.local_decls[place.local].ty);
                self.obj_types.entry(obj).or_default().insert(id);
                (Value::objs([obj]), 0)
            }
        };
        let path = self.field_path(body, place, from);
        value.objs = self.members(value.objs, &path);
        value
    }

    /// R4: an address-taken pointer local and its memory cell are one.
    fn sync_addr_taken(&mut self, f: LocalDefId, body: &Body<'tcx>) -> bool {
        let mut changed = false;
        let locals: Vec<Local> = self
            .addr_taken
            .iter()
            .filter(|(g, _)| *g == f)
            .map(|&(_, l)| l)
            .collect();
        // 3.5: what was stored through `Top` may be in the local's memory too.
        let wild = self.wild();
        for local in locals {
            let obj = Obj::Stack(f, local);
            let cell = self.ty_id(body.local_decls[local].ty);
            let objs = self.points.get(&(f, local)).cloned().unwrap_or_default();
            changed |= self.store(Key::Cell(obj, cell), &objs);
            let mut stored = wild.clone();
            let mut vias = FxHashSet::default();
            if !wild.is_subset(&objs) {
                vias.insert(Via::Unknown);
            }
            for key in self.held.get(&obj).into_iter().flatten() {
                let more = self.contents.get(key).cloned().unwrap_or_default();
                if !more.is_subset(&objs) {
                    vias.insert(match *key {
                        Key::Field(_, did, index) => Via::Field(did, index),
                        Key::Cell(_, ty) => Via::Cell(ty),
                        Key::Init(_) => Via::Unknown,
                    });
                }
                stored.extend(more);
            }
            if !stored.is_subset(&objs) {
                changed |= self.add_value(
                    (f, local),
                    Value {
                        objs: stored,
                        retained: true,
                        vias,
                        params: FxHashSet::default(),
                    },
                );
            }
        }
        changed
    }

    /// The program functions a call may reach: its callee, or, through a function
    /// pointer, every address-taken function of the pointer's signature.
    fn call_targets(&self, body: &Body<'tcx>, block: BasicBlock) -> Vec<LocalDefId> {
        let tcx = self.tcx;
        let TerminatorKind::Call { func, args, .. } = &body.basic_blocks[block].terminator().kind
        else {
            return vec![];
        };
        if let Some(c) = func.constant() {
            return match c.ty().kind() {
                TyKind::FnDef(target, _) => target
                    .as_local()
                    .filter(|g| self.functions.contains(g))
                    .into_iter()
                    .collect(),
                _ => vec![],
            };
        }
        let sig = match func.ty(body, tcx).kind() {
            TyKind::FnPtr(sig_tys, _) => {
                Some(tcx.erase_regions(sig_tys.skip_binder().inputs_and_output))
            }
            _ => None,
        };
        self.address_taken
            .iter()
            .copied()
            .filter(|g| match sig {
                Some(sig) => {
                    tcx.erase_regions(tcx.fn_sig(*g).skip_binder().skip_binder().inputs_and_output)
                        == sig
                }
                None => {
                    tcx.mir_drops_elaborated_and_const_checked(*g)
                        .borrow()
                        .arg_count
                        == args.len()
                }
            })
            .collect()
    }

    /// The foreign functions a call through a function pointer may reach.
    fn foreign_targets(&self, body: &Body<'tcx>, block: BasicBlock) -> Vec<DefId> {
        let tcx = self.tcx;
        let TerminatorKind::Call { func, .. } = &body.basic_blocks[block].terminator().kind else {
            return vec![];
        };
        if func.constant().is_some() {
            return vec![];
        }
        let TyKind::FnPtr(sig_tys, _) = func.ty(body, tcx).kind() else { return vec![] };
        let sig = tcx.erase_regions(sig_tys.skip_binder().inputs_and_output);
        self.foreign_taken
            .iter()
            .copied()
            .filter(|&d| {
                tcx.erase_regions(tcx.fn_sig(d).skip_binder().skip_binder().inputs_and_output)
                    == sig
            })
            .collect()
    }

    /// A call through a function pointer whose every possible target is an allocator.
    fn indirect_alloc(&self, body: &Body<'tcx>, block: BasicBlock) -> bool {
        if !self.on(Rule::AllocatorHook) {
            return false;
        }
        let foreign = self.foreign_targets(body, block);
        !foreign.is_empty()
            && foreign
                .iter()
                .all(|&d| matches!(self.tcx.item_name(d).as_str(), "malloc" | "calloc"))
            && self
                .call_targets(body, block)
                .iter()
                .all(|g| self.allocators.contains(g))
    }

    /// Is the call at `block` an allocation: a wrapper or a hook whose every target
    /// allocates (P5)?
    fn allocating_call(&self, body: &Body<'tcx>, block: BasicBlock) -> bool {
        let targets = self.call_targets(body, block);
        // 2.7: a foreign target that does not allocate makes the call not an allocation.
        if self.on(Rule::JointTargets)
            && !self
                .foreign_targets(body, block)
                .iter()
                .all(|&d| matches!(self.tcx.item_name(d).as_str(), "malloc" | "calloc"))
        {
            return false;
        }
        let hooks = self.on(Rule::AllocatorHook) || Self::direct_call(body, block);
        (hooks && !targets.is_empty() && targets.iter().all(|t| self.allocators.contains(t)))
            || self.indirect_alloc(body, block)
    }

    /// Allocator wrappers: functions whose result is only a fresh allocation or null,
    /// through copies and casts, and whose fresh value escapes by the return alone (R2).
    fn find_allocators(&mut self) {
        let tcx = self.tcx;
        let functions = self.functions.clone();
        loop {
            let mut changed = false;
            for &g in &functions {
                if self.allocators.contains(&g) {
                    continue;
                }
                let body = self.body(g);
                let mut fresh: FxHashSet<Local> = FxHashSet::default();
                let mut other: FxHashSet<Local> = FxHashSet::default();
                for i in 1..=body.arg_count {
                    other.insert(Local::from_usize(i));
                }
                loop {
                    let mut grew = false;
                    for (block, data) in body.basic_blocks.iter_enumerated() {
                        for statement in &data.statements {
                            let StatementKind::Assign(box (dst, rvalue)) = &statement.kind else {
                                continue;
                            };
                            if !dst.projection.is_empty() {
                                continue;
                            }
                            let source = match rvalue {
                                Rvalue::Use(op) | Rvalue::Cast(_, op, _) => match op.place() {
                                    Some(place) if place.projection.is_empty() => Some(place.local),
                                    Some(_) => None,
                                    None => {
                                        let zero = op.constant().is_some_and(|c| {
                                            c.const_
                                                .try_to_scalar_int()
                                                .is_some_and(|value| value.is_null())
                                        });
                                        if zero {
                                            continue;
                                        }
                                        None
                                    }
                                },
                                _ => None,
                            };
                            match source {
                                Some(src) => {
                                    if fresh.contains(&src) {
                                        grew |= fresh.insert(dst.local);
                                    }
                                    if other.contains(&src) {
                                        grew |= other.insert(dst.local);
                                    }
                                }
                                None => grew |= other.insert(dst.local),
                            }
                        }
                        let Some(call) = as_call(data.terminator(), tcx) else { continue };
                        let dst = call.destination;
                        if !dst.projection.is_empty() {
                            continue;
                        }
                        let alloc = match &call.func {
                            CallKind::LibC(name) => {
                                matches!(name.as_str(), "malloc" | "calloc" | "strdup")
                            }
                            CallKind::RustLib(did) => {
                                if matches!(tcx.item_name(*did).as_str(), "null" | "null_mut") {
                                    continue;
                                }
                                false
                            }
                            CallKind::FreeStanding(_)
                            | CallKind::Impl(_)
                            | CallKind::Closure
                            | CallKind::Dynamic => self.allocating_call(&body, block),
                        };
                        if alloc {
                            grew |= fresh.insert(dst.local);
                        } else {
                            grew |= other.insert(dst.local);
                        }
                    }
                    if !grew {
                        break;
                    }
                }
                let ret = Local::from_usize(0);
                if fresh.contains(&ret)
                    && !other.contains(&ret)
                    && (!self.on(Rule::WrapperEscape) || !self.fresh_escapes(&body, &fresh))
                {
                    self.allocators.insert(g);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
    }

    /// R2: does a fresh value (or one derived from it) leave the wrapper other than by
    /// its return: stored into memory, passed to a call that may keep it, address-taken,
    /// or placed into an aggregate?
    fn fresh_escapes(&self, body: &Body<'tcx>, fresh: &FxHashSet<Local>) -> bool {
        let tcx = self.tcx;
        let mut family = fresh.clone();
        loop {
            let mut grew = false;
            for data in body.basic_blocks.iter() {
                for statement in &data.statements {
                    let StatementKind::Assign(box (dst, rvalue)) = &statement.kind else {
                        continue;
                    };
                    if !dst.projection.is_empty() {
                        continue;
                    }
                    let source = match rvalue {
                        Rvalue::Use(op) | Rvalue::Cast(_, op, _) => local_of(op),
                        Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => {
                            matches!(place.projection.first(), Some(ProjectionElem::Deref))
                                .then_some(place.local)
                        }
                        Rvalue::BinaryOp(BinOp::Offset, box (base, _)) => local_of(base),
                        _ => None,
                    };
                    if source.is_some_and(|s| family.contains(&s)) {
                        grew |= family.insert(dst.local);
                    }
                }
                if let Some(call) = as_call(data.terminator(), tcx)
                    && let CallKind::RustLib(did) = &call.func
                    && DERIVING.contains(&tcx.item_name(*did).as_str())
                    && call
                        .args
                        .first()
                        .and_then(|a| local_of(&a.node))
                        .is_some_and(|l| family.contains(&l))
                {
                    grew |= family.insert(call.destination.local);
                }
            }
            if !grew {
                break;
            }
        }
        let mentions = |op: &Operand<'tcx>| {
            op.place()
                .is_some_and(|p| p.projection.is_empty() && family.contains(&p.local))
        };
        for data in body.basic_blocks.iter() {
            for statement in &data.statements {
                let StatementKind::Assign(box (dst, rvalue)) = &statement.kind else { continue };
                let escapes = match rvalue {
                    Rvalue::Use(op) | Rvalue::Cast(_, op, _) => {
                        !dst.projection.is_empty() && mentions(op)
                    }
                    Rvalue::Aggregate(_, ops) => ops.iter().any(mentions),
                    Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => {
                        place.projection.is_empty() && family.contains(&place.local)
                    }
                    _ => false,
                };
                if escapes {
                    return true;
                }
            }
            if let Some(call) = as_call(data.terminator(), tcx) {
                for (j, arg) in call.args.iter().enumerate() {
                    if !mentions(&arg.node) {
                        continue;
                    }
                    // A C library call that only reads or writes through the pointer
                    // does not keep it; a Rust pointer method derives from it.
                    let keeps = match &call.func {
                        CallKind::LibC(name) => match contract_of(name.as_str()) {
                            Some(c) => {
                                c.store.is_some_and(|(_, v)| v == j)
                                    || c.callback
                                    || (name.as_str() == "strtok" && j == 0)
                            }
                            None => true,
                        },
                        CallKind::RustLib(_) => false,
                        CallKind::FreeStanding(_)
                        | CallKind::Impl(_)
                        | CallKind::Closure
                        | CallKind::Dynamic => true,
                    };
                    if keeps {
                        return true;
                    }
                }
            }
        }
        false
    }

    /// The flow-insensitive fixpoint.
    fn solve_points(&mut self) {
        let functions = self.functions.clone();
        for &f in &functions {
            if !self.exposed.contains(&f)
                || (self.called.contains(&f) && !self.handed_callbacks.contains(&f))
            {
                continue;
            }
            let body = self.body(f);
            for i in 1..=body.arg_count {
                let local = Local::from_usize(i);
                if self.options.closed {
                    // R816-1: a callback outside code calls is unknown library code's;
                    // an entry's argument is a fresh object of the program's client.
                    if self.called.contains(&f) {
                        if is_ptr(body.local_decls[local].ty)
                            || self.carries_ptr(body.local_decls[local].ty, 0)
                        {
                            let top = self.top();
                            self.add_value((f, local), top);
                        }
                    } else if let Some(pointee) = body.local_decls[local].ty.builtin_deref(true) {
                        let obj = self.fresh_obj(u32::MAX, FreshWay::Arg(f, i), Some(pointee));
                        self.points.entry((f, local)).or_default().insert(obj);
                    } else if self.carries_ptr(body.local_decls[local].ty, 0) {
                        let obj = self.fresh_obj(u32::MAX, FreshWay::Arg(f, i), None);
                        let Obj::Fresh(id) = obj else { unreachable!() };
                        self.fresh_backed
                            .entry(Obj::Stack(f, local))
                            .or_default()
                            .insert(id);
                    }
                    continue;
                }
                if let Some(pointee) = body.local_decls[local].ty.builtin_deref(true) {
                    let id = self.ty_id(pointee);
                    let obj = Obj::External(id);
                    self.obj_types.entry(obj).or_default().insert(id);
                    self.points.entry((f, local)).or_default().insert(obj);
                } else if self.carries_ptr(body.local_decls[local].ty, 0) {
                    // An aggregate an outside caller passes by value holds anything.
                    let top = self.top().objs;
                    self.store(Key::Init(Obj::Stack(f, local)), &top);
                }
            }
        }
        for &f in &functions {
            let arg_count = self.body(f).arg_count;
            for i in 1..=arg_count {
                self.from_param
                    .entry((f, Local::from_usize(i)))
                    .or_default()
                    .insert(i);
            }
        }
        let trace = std::env::var("CRAT_E5C_HOLD_TRACE").is_ok();
        let mut round = 0usize;
        loop {
            let mut changed = false;
            let mut grew: Vec<LocalDefId> = vec![];
            for &f in &functions {
                let body = self.body(f);
                let c = self.flow_body(f, &body);
                if c && trace {
                    grew.push(f);
                }
                changed |= c;
            }
            round += 1;
            if trace {
                let points: usize = self.points.values().map(|s| s.len()).sum();
                let contents: usize = self.contents.values().map(|s| s.len()).sum();
                eprintln!(
                    "E5C_HOLD_TRACE round {round}: changed in {} fns (first {:?}), fresh {}, points {points}, contents {contents}, fresh_backed {}",
                    grew.len(),
                    grew.first().map(|g| self.tcx.def_path_str(g.to_def_id())),
                    self.fresh.len(),
                    self.fresh_backed.len()
                );
            }
            if !changed {
                break;
            }
        }
    }

    /// One body, exhaustively over the statement and terminator kinds.
    fn flow_body(&mut self, f: LocalDefId, body: &Body<'tcx>) -> bool {
        let mut changed = false;
        for (block, data) in body.basic_blocks.iter_enumerated() {
            for statement in &data.statements {
                match &statement.kind {
                    StatementKind::Assign(box (dst, rvalue)) => {
                        changed |= self.assign(f, body, *dst, rvalue);
                    }
                    StatementKind::Intrinsic(box NonDivergingIntrinsic::CopyNonOverlapping(c)) => {
                        if self.on(Rule::CopyCarry) {
                            let from = self.operand_value(f, body, &c.src).objs;
                            let to = self.operand_value(f, body, &c.dst).objs;
                            changed |= self.copy_memory(&from, &to);
                        }
                    }
                    StatementKind::Intrinsic(box NonDivergingIntrinsic::Assume(_))
                    | StatementKind::FakeRead(..)
                    | StatementKind::SetDiscriminant { .. }
                    | StatementKind::Deinit(_)
                    | StatementKind::StorageLive(_)
                    | StatementKind::StorageDead(_)
                    | StatementKind::Retag(..)
                    | StatementKind::PlaceMention(_)
                    | StatementKind::AscribeUserType(..)
                    | StatementKind::Coverage(_)
                    | StatementKind::ConstEvalCounter
                    | StatementKind::Nop
                    | StatementKind::BackwardIncompatibleDropHint { .. } => {}
                }
            }
            changed |= self.flow_terminator(f, body, block);
        }
        if self.on(Rule::AddressTaken) {
            changed |= self.sync_addr_taken(f, body);
        }
        changed | std::mem::take(&mut self.dirty)
    }

    fn flow_terminator(&mut self, f: LocalDefId, body: &Body<'tcx>, block: BasicBlock) -> bool {
        let terminator = body.basic_blocks[block].terminator();
        match &terminator.kind {
            TerminatorKind::Call { .. } | TerminatorKind::TailCall { .. } => {
                self.flow_call(f, body, block)
            }
            TerminatorKind::InlineAsm { operands, .. } => {
                let mut changed = false;
                for operand in operands.iter() {
                    let place = match operand {
                        InlineAsmOperand::Out { place, .. } => *place,
                        InlineAsmOperand::InOut { out_place, .. } => *out_place,
                        InlineAsmOperand::In { .. }
                        | InlineAsmOperand::Const { .. }
                        | InlineAsmOperand::SymFn { .. }
                        | InlineAsmOperand::SymStatic { .. }
                        | InlineAsmOperand::Label { .. } => None,
                    };
                    if let Some(place) = place {
                        let top = self.top();
                        changed |= self.put(f, body, place, top);
                    }
                }
                changed
            }
            TerminatorKind::Yield { resume_arg, .. } => {
                let top = self.top();
                self.put(f, body, *resume_arg, top)
            }
            TerminatorKind::Goto { .. }
            | TerminatorKind::SwitchInt { .. }
            | TerminatorKind::UnwindResume
            | TerminatorKind::UnwindTerminate(_)
            | TerminatorKind::Return
            | TerminatorKind::Unreachable
            | TerminatorKind::Drop { .. }
            | TerminatorKind::Assert { .. }
            | TerminatorKind::CoroutineDrop
            | TerminatorKind::FalseEdge { .. }
            | TerminatorKind::FalseUnwind { .. } => false,
        }
    }

    fn flow_call(&mut self, f: LocalDefId, body: &Body<'tcx>, block: BasicBlock) -> bool {
        let tcx = self.tcx;
        let data = &body.basic_blocks[block];
        let Some(call) = as_call(data.terminator(), tcx) else { return false };
        let mut changed = false;
        let dst = call.destination;
        let dst_ty = dst.ty(body, tcx).ty;
        let targets: Vec<LocalDefId> = self.call_targets(body, block);
        // Bind the arguments to every target's parameters: pointers, aggregates by
        // value (R7) and byte provenance (R8).
        for &g in &targets {
            let callee_args = tcx
                .mir_drops_elaborated_and_const_checked(g)
                .borrow()
                .arg_count;
            for (j, arg) in call.args.iter().enumerate().take(callee_args) {
                let param = (g, Local::from_usize(j + 1));
                let ty = arg.node.ty(body, tcx);
                if is_ptr(ty) {
                    let objs = self.operand_value(f, body, &arg.node).objs;
                    changed |= self.add_value(param, Value::objs(objs));
                } else if ty.is_integral() {
                    let sources = self.int_operand(f, body, &arg.node);
                    if !sources.is_empty() {
                        let set = self.byte_from.entry(param).or_default();
                        let before = set.len();
                        set.extend(sources);
                        changed |= set.len() != before;
                    }
                } else if self.on(Rule::ByValue) && self.carries_ptr(ty, 0) {
                    let from = self.operand_memory(f, body, &arg.node);
                    changed |= self
                        .copy_memory(&from, &FxHashSet::from_iter([Obj::Stack(param.0, param.1)]));
                }
            }
        }
        // The result.
        match &call.func {
            CallKind::LibC(name) => {
                changed |= self.flow_foreign(f, body, block, &call, name.as_str());
            }
            CallKind::RustLib(did) => {
                let name = tcx.item_name(*did);
                let name = name.as_str();
                let first = call.args.first().map(|a| a.node.clone());
                if is_ptr(dst_ty) {
                    let value = if matches!(name, "null" | "null_mut") {
                        Value::default()
                    } else if DERIVING.contains(&name)
                        && let Some(first) = &first
                    {
                        let mut value = self.operand_value(f, body, first);
                        match name {
                            "cast" | "cast_mut" | "cast_const" | "as_ptr" | "as_mut_ptr" => {
                                let from = first.ty(body, tcx);
                                self.member_cast(
                                    f,
                                    body,
                                    dst,
                                    local_of(first),
                                    from,
                                    dst_ty,
                                    &mut value,
                                );
                            }
                            "sub" | "wrapping_sub" => {
                                self.member_offset(f, body, dst, first, None, &mut value);
                            }
                            _ => {
                                let offset = call.args.get(1).map(|a| a.node.clone());
                                self.member_offset(
                                    f,
                                    body,
                                    dst,
                                    first,
                                    offset.as_ref().or(None),
                                    &mut value,
                                );
                            }
                        }
                        value
                    } else if matches!(name, "expect" | "unwrap")
                        && let Some(first) = &first
                    {
                        // An `Option`'s payload: what its memory holds.
                        let memory = self.operand_memory(f, body, first);
                        let mut value = Value {
                            retained: true,
                            ..Default::default()
                        };
                        value.vias.insert(Via::Unknown);
                        for obj in memory {
                            for key in self.held.get(&obj).cloned().into_iter().flatten() {
                                value
                                    .objs
                                    .extend(self.contents.get(&key).into_iter().flatten().copied());
                            }
                        }
                        value
                    } else {
                        self.top()
                    };
                    changed |= self.put(f, body, dst, value);
                } else if dst_ty.is_integral() {
                    let mut sources = FxHashSet::default();
                    for arg in call.args.iter() {
                        sources.extend(self.int_operand(f, body, &arg.node));
                    }
                    changed |= self.assign_int(f, body, dst, sources);
                } else if self.carries_ptr(dst_ty, 0) && !RUST_INERT.contains(&name) {
                    let region = self.base_objects(f, body, dst);
                    let top = self.top().objs;
                    for obj in region {
                        changed |= self.store(Key::Init(obj), &top);
                    }
                }
            }
            CallKind::FreeStanding(_)
            | CallKind::Impl(_)
            | CallKind::Closure
            | CallKind::Dynamic => {
                if is_ptr(dst_ty) && self.allocating_call(body, block) {
                    let site = Obj::Alloc(f, block);
                    // R2b: the caller's site object takes the wrapper's object's contents.
                    if self.on(Rule::WrapperContents) {
                        let inner: FxHashSet<Obj> = targets
                            .iter()
                            .flat_map(|&g| {
                                self.points
                                    .get(&(g, Local::from_usize(0)))
                                    .cloned()
                                    .unwrap_or_default()
                            })
                            .collect();
                        for &obj in &inner {
                            let types = self.obj_types.get(&obj).cloned().unwrap_or_default();
                            self.obj_types.entry(site).or_default().extend(types);
                        }
                        changed |= self.copy_memory(&inner, &FxHashSet::from_iter([site]));
                    }
                    changed |= self.put(f, body, dst, Value::objs([site]));
                } else if !targets.is_empty() {
                    for &g in &targets {
                        let ret = (g, Local::from_usize(0));
                        if is_ptr(dst_ty) {
                            let mut value = self.local_value(g, Local::from_usize(0));
                            let params = std::mem::take(&mut value.params);
                            changed |= self.put(f, body, dst, value);
                            // A return derived from a parameter derives from the argument.
                            for j in params {
                                if let Some(arg) = call.args.get(j - 1)
                                    && is_ptr(arg.node.ty(body, tcx))
                                {
                                    let v = self.operand_value(f, body, &arg.node);
                                    changed |= self.put(f, body, dst, v);
                                }
                            }
                        } else if dst_ty.is_integral() {
                            let sources = self.byte_from.get(&ret).cloned().unwrap_or_default();
                            changed |= self.assign_int(f, body, dst, sources);
                        } else if self.on(Rule::ByValue) && self.carries_ptr(dst_ty, 0) {
                            changed |= self.assign_memory(
                                f,
                                body,
                                dst,
                                FxHashSet::from_iter([Obj::Stack(g, Local::from_usize(0))]),
                            );
                        }
                    }
                }
                // A function pointer: also the foreign functions it may be (2.7); with no
                // target at all, anything.
                if matches!(call.func, CallKind::Closure | CallKind::Dynamic)
                    && !(is_ptr(dst_ty) && self.allocating_call(body, block))
                    && (targets.is_empty() || self.on(Rule::JointTargets))
                {
                    let foreign = self.foreign_targets(body, block);
                    if foreign.is_empty() {
                        if targets.is_empty() && is_ptr(dst_ty) {
                            let top = self.top();
                            changed |= self.put(f, body, dst, top);
                        }
                    } else {
                        for d in foreign {
                            let name = tcx.item_name(d);
                            changed |= self.flow_foreign(f, body, block, &call, name.as_str());
                        }
                    }
                }
            }
        }
        changed
    }

    /// A C library call by its contract (R9); an unlisted one is `Top`.
    fn flow_foreign(
        &mut self,
        f: LocalDefId,
        body: &Body<'tcx>,
        block: BasicBlock,
        call: &Call<'_, 'tcx>,
        name: &str,
    ) -> bool {
        let tcx = self.tcx;
        let dst = call.destination;
        let dst_ty = dst.ty(body, tcx).ty;
        let mut changed = false;
        let contract = if self.on(Rule::ForeignEffects) {
            contract_of(name)
        } else {
            Some(contract(&[], Eff::None, Ret::None))
        };
        let Some(contract) = contract else {
            // Unlisted: its pointer arguments' objects may now hold anything, and its
            // result is anything.
            let top = self.top().objs;
            for arg in call.args.iter() {
                if is_ptr(arg.node.ty(body, tcx)) {
                    let objs = self.operand_value(f, body, &arg.node).objs;
                    for obj in self.roots(objs) {
                        changed |= self.store(Key::Init(obj), &top);
                    }
                }
            }
            if is_ptr(dst_ty) {
                let value = self.top();
                changed |= self.put(f, body, dst, value);
            }
            return changed;
        };
        // M1: a pointer that reaches an output (a `%p` conversion; output read from memory
        // holding pointers) may come back through any input in the same run: once one
        // has, every library write may write pointers, so it stores `Top`.
        if self.on(Rule::RoundTrip) {
            let printf = matches!(
                name,
                "printf" | "fprintf" | "sprintf" | "snprintf" | "printw" | "mvprintw"
            );
            for (j, arg) in call.args.iter().enumerate() {
                let eff = contract.args.get(j).copied().unwrap_or(contract.rest);
                let ty = arg.node.ty(body, tcx);
                if !is_ptr(ty) {
                    continue;
                }
                let output = matches!(name, "fwrite" | "write" | "fputs" | "puts");
                if matches!(eff, Eff::Read | Eff::ReadWrite)
                    && !self.exposed_output
                    && (output || printf)
                {
                    let value = self.operand_value(f, body, &arg.node).objs;
                    let objs = self.roots(value);
                    let holds_pointers = objs.iter().any(|o| {
                        *o == Obj::Top
                            || self
                                .held
                                .get(o)
                                .into_iter()
                                .flatten()
                                .any(|k| self.contents.get(k).is_some_and(|c| !c.is_empty()))
                    });
                    let printed = printf && j >= contract.args.len() && {
                        let index = match name {
                            "printf" | "printw" => 0,
                            "fprintf" | "sprintf" => 1,
                            _ => 2,
                        };
                        call.args.get(index).is_none_or(|fmt| {
                            self.literal_bytes(body, &fmt.node, 0)
                                .is_none_or(|bytes| bytes.windows(2).any(|w| w == b"%p"))
                        })
                    };
                    if (output && holds_pointers) || printed {
                        self.exposed_output = true;
                        changed = true;
                        if std::env::var("CRAT_E5C_HOLD_TRACE").is_ok() {
                            eprintln!(
                                "E5C_HOLD_TRACE exposure {name} arg {j} in {} (output {output}, printed {printed})",
                                tcx.def_path_str(f.to_def_id())
                            );
                        }
                    }
                }
                if matches!(eff, Eff::Write | Eff::ReadWrite) && self.exposed_output {
                    let top = self.top().objs;
                    let value = self.operand_value(f, body, &arg.node).objs;
                    for obj in self.roots(value) {
                        changed |= self.store(Key::Init(obj), &top);
                    }
                }
            }
        }
        if let Some((to, from)) = contract.copy
            && let (Some(to), Some(from)) = (call.args.get(to), call.args.get(from))
            && self.on(Rule::CopyCarry)
        {
            let to = self.operand_value(f, body, &to.node).objs;
            let from = self.operand_value(f, body, &from.node).objs;
            changed |= self.copy_memory(&from, &to);
        }
        if let Some((target, value)) = contract.store
            && let (Some(target), Some(value)) = (call.args.get(target), call.args.get(value))
        {
            let value = self.operand_value(f, body, &value.node);
            let targets = self.operand_value(f, body, &target.node).objs;
            if let Some(ty) = target.node.ty(body, tcx).builtin_deref(true) {
                let cell = self.ty_id(ty);
                for obj in self.roots(targets) {
                    changed |= self.store(Key::Cell(obj, cell), &value.objs);
                }
            }
        }
        if self.options.close_n2
            && name == "glob"
            && let Some(target) = call.args.get(3)
        {
            let lib = Obj::Opaque(f, block);
            let objs = self.operand_value(f, body, &target.node).objs;
            for obj in self.roots(objs) {
                changed |= self.store(Key::Init(obj), &FxHashSet::from_iter([lib]));
            }
        }
        if name == "strtok"
            && let Some(first) = call.args.first()
        {
            let objs = self.operand_value(f, body, &first.node).objs;
            let before = self.strtok.len();
            self.strtok.extend(objs);
            changed |= self.strtok.len() != before;
        }
        if is_ptr(dst_ty) {
            let value = match contract.ret {
                Ret::None => self.top(),
                Ret::Alloc => Value::objs([Obj::Alloc(f, block)]),
                Ret::Realloc => {
                    let mut value = Value::objs([Obj::Alloc(f, block)]);
                    if let Some(first) = call.args.first() {
                        value.join(self.operand_value(f, body, &first.node));
                    }
                    value
                }
                Ret::Arg(i) => match call.args.get(i) {
                    Some(arg) => self.operand_value(f, body, &arg.node),
                    None => self.top(),
                },
                Ret::Opaque => self.opaque(f, block, dst_ty),
                Ret::Strtok => Value {
                    objs: self.strtok.clone(),
                    retained: true,
                    vias: FxHashSet::from_iter([Via::Opaque]),
                    params: FxHashSet::default(),
                },
            };
            changed |= self.put(f, body, dst, value);
        }
        changed
    }

    /// Accesses through retained pointers, and through parameters, closed over the
    /// call graph.
    fn solve_accesses(&mut self) {
        let functions = self.functions.clone();
        loop {
            let mut changed = false;
            for &f in &functions {
                let body = self.body(f);
                let (acc, params) = self.body_accesses(f, &body);
                let set = self.acc.entry(f).or_default();
                let before = set.len();
                set.extend(acc);
                changed |= set.len() != before;
                for (j, (read, write)) in params {
                    let entry = self.param_acc.entry((f, j)).or_default();
                    let next = (entry.0 | read, entry.1 | write);
                    if next != *entry {
                        *entry = next;
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
        }
    }

    /// The bytes of a literal a pointer operand points to (`b"..\0".as_ptr() as *const _`).
    fn literal_bytes(&self, body: &Body<'tcx>, op: &Operand<'tcx>, depth: u8) -> Option<Vec<u8>> {
        if depth > 8 {
            return None;
        }
        match op {
            Operand::Constant(c) => {
                // 3.7: from the pointer's own offset into the allocation.
                let (alloc, start) = match c.const_.try_to_scalar() {
                    Some(Scalar::Ptr(ptr, _)) => {
                        let (provenance, offset) = ptr.into_parts();
                        match self.tcx.global_alloc(provenance.alloc_id()) {
                            GlobalAlloc::Memory(alloc) => (alloc, offset.bytes_usize()),
                            _ => return None,
                        }
                    }
                    _ => match c.const_ {
                        rustc_middle::mir::Const::Val(
                            rustc_middle::mir::ConstValue::Slice { data, .. },
                            _,
                        ) => (data, 0),
                        _ => return None,
                    },
                };
                let inner = alloc.inner();
                if start > inner.len() {
                    return None;
                }
                Some(
                    inner
                        .inspect_with_uninit_and_ptr_outside_interpreter(start..inner.len())
                        .to_vec(),
                )
            }
            Operand::Copy(place) | Operand::Move(place) => {
                if !place.projection.is_empty() {
                    return None;
                }
                let mut found: Option<Vec<u8>> = None;
                let mut defs = 0;
                for data in body.basic_blocks.iter() {
                    for statement in &data.statements {
                        if let StatementKind::Assign(box (dst, rvalue)) = &statement.kind
                            && dst.local == place.local
                        {
                            defs += 1;
                            found = match rvalue {
                                Rvalue::Use(next) | Rvalue::Cast(_, next, _) => {
                                    self.literal_bytes(body, next, depth + 1)
                                }
                                _ => None,
                            };
                        }
                    }
                    if let TerminatorKind::Call {
                        destination,
                        args,
                        func,
                        ..
                    } = &data.terminator().kind
                        && destination.local == place.local
                    {
                        defs += 1;
                        found = match func.constant().map(|c| *c.ty().kind()) {
                            // 3.7: only a cast keeps the literal's start; an offset moves it.
                            Some(TyKind::FnDef(d, _))
                                if !d.is_local()
                                    && matches!(
                                        self.tcx.item_name(d).as_str(),
                                        "cast"
                                            | "cast_mut"
                                            | "cast_const"
                                            | "as_ptr"
                                            | "as_mut_ptr"
                                    ) =>
                            {
                                args.first()
                                    .and_then(|a| self.literal_bytes(body, &a.node, depth + 1))
                            }
                            _ => None,
                        };
                    }
                }
                if defs == 1 { found } else { None }
            }
        }
    }

    /// 2.8: may a formatted-output call write through its pointer varargs (`%n`)? Only a
    /// literal format without a `%n` conversion says no.
    fn format_writes(&self, body: &Body<'tcx>, call: &Call<'_, 'tcx>, name: &str) -> bool {
        let index = match name {
            "printf" | "printw" | "sscanf" => 0,
            "fprintf" | "sprintf" | "fscanf" => 1,
            "snprintf" | "mvprintw" => 2,
            _ => return false,
        };
        if !self.on(Rule::FormatWrites) {
            return false;
        }
        let Some(bytes) = call
            .args
            .get(index)
            .and_then(|a| self.literal_bytes(body, &a.node, 0))
        else {
            return true;
        };
        let mut i = 0;
        while i < bytes.len() {
            if bytes[i] == b'%' {
                let mut j = i + 1;
                while j < bytes.len() && b"-+ #0123456789.*hlLqjzt'".contains(&bytes[j]) {
                    j += 1;
                }
                if j < bytes.len() && bytes[j] == b'n' {
                    return true;
                }
                i = j + 1;
            } else {
                i += 1;
            }
        }
        false
    }

    /// A pointer argument's effect in a foreign call: its contract's, with 2.8's writes;
    /// an unlisted function's argument is read and written.
    fn arg_effect(&self, body: &Body<'tcx>, call: &Call<'_, 'tcx>, name: &str, j: usize) -> Eff {
        let contract = if self.on(Rule::ForeignEffects) {
            contract_of(name)
        } else {
            Some(contract(&[], Eff::None, Ret::None))
        };
        match contract {
            Some(c) => match c.args.get(j) {
                Some(&eff) => eff,
                None if self.format_writes(body, call, name) => Eff::ReadWrite,
                None => c.rest,
            },
            None => Eff::ReadWrite,
        }
    }

    /// The foreign functions whose effects a call has, by name; `""` is an unlisted one.
    fn foreign_effects(
        &self,
        body: &Body<'tcx>,
        block: BasicBlock,
        call: &Call<'_, 'tcx>,
    ) -> Vec<String> {
        let tcx = self.tcx;
        match &call.func {
            CallKind::LibC(name) => vec![name.to_string()],
            CallKind::Closure | CallKind::Dynamic
                if self.call_targets(body, block).is_empty() || self.on(Rule::JointTargets) =>
            {
                let names: Vec<String> = self
                    .foreign_targets(body, block)
                    .iter()
                    .map(|&d| tcx.item_name(d).to_string())
                    .collect();
                if names.is_empty() && self.call_targets(body, block).is_empty() {
                    vec![String::new()]
                } else {
                    names
                }
            }
            CallKind::RustLib(did) => {
                let name = tcx.item_name(*did);
                let name = name.as_str();
                if DERIVING.contains(&name)
                    || RUST_INERT.contains(&name)
                    || matches!(name, "null" | "null_mut" | "expect" | "unwrap")
                {
                    vec![]
                } else {
                    vec![String::new()]
                }
            }
            CallKind::FreeStanding(_)
            | CallKind::Impl(_)
            | CallKind::Closure
            | CallKind::Dynamic => {
                vec![]
            }
        }
    }

    /// The accesses one body makes through retained pointers (its own and its
    /// callees'), and through its parameters; exhaustive over the kinds that read or
    /// write through a place.
    fn body_accesses(
        &self,
        f: LocalDefId,
        body: &Body<'tcx>,
    ) -> (FxHashSet<Access>, FxHashMap<usize, (bool, bool)>) {
        let tcx = self.tcx;
        let mut acc: FxHashSet<Access> = FxHashSet::default();
        let mut inherited: Vec<Access> = Vec::new();
        let mut params: FxHashMap<usize, (bool, bool)> = FxHashMap::default();
        // An access through `local`.
        let mut through =
            |acc: &mut FxHashSet<Access>, local: Local, write: bool, location: Location| {
                if self.retained.contains(&(f, local)) {
                    let unresolved = FxHashSet::from_iter([Via::Unresolved]);
                    let vias = self
                        .vias
                        .get(&(f, local))
                        .filter(|set| !set.is_empty())
                        .unwrap_or(&unresolved);
                    for &obj in self.points.get(&(f, local)).into_iter().flatten() {
                        for &via in vias {
                            acc.insert(Access {
                                obj,
                                write,
                                at: (f, location),
                                via,
                                by: local,
                            });
                        }
                    }
                    // (T) does not lean on points-to: an access through a retained
                    // pointer counts by its type even where no object is known.
                    if self.options.by_types
                        && self
                            .points
                            .get(&(f, local))
                            .is_none_or(|objs| objs.is_empty())
                    {
                        for &via in vias {
                            acc.insert(Access {
                                obj: Obj::Anon(u32::MAX),
                                write,
                                at: (f, location),
                                via,
                                by: local,
                            });
                        }
                    }
                }
                for &j in self.from_param.get(&(f, local)).into_iter().flatten() {
                    let entry = params.entry(j).or_default();
                    if write {
                        entry.1 = true;
                    } else {
                        entry.0 = true;
                    }
                }
            };
        let top_access = |acc: &mut FxHashSet<Access>, location: Location| {
            acc.insert(Access {
                obj: Obj::Top,
                write: true,
                at: (f, location),
                via: Via::Unknown,
                by: Local::from_usize(0),
            });
        };
        for (block, data) in body.basic_blocks.iter_enumerated() {
            for (statement_index, statement) in data.statements.iter().enumerate() {
                let location = Location {
                    block,
                    statement_index,
                };
                // A place accessed: through its first dereference (MIR keeps it first).
                let mut places: Vec<(Place<'tcx>, bool)> = Vec::new();
                match &statement.kind {
                    StatementKind::Assign(box (dst, rvalue)) => {
                        places.push((*dst, true));
                        match rvalue {
                            Rvalue::Use(op)
                            | Rvalue::Cast(_, op, _)
                            | Rvalue::UnaryOp(_, op)
                            | Rvalue::Repeat(op, _)
                            | Rvalue::ShallowInitBox(op, _)
                            | Rvalue::WrapUnsafeBinder(op, _) => {
                                places.extend(op.place().map(|p| (p, false)));
                            }
                            Rvalue::CopyForDeref(place)
                            | Rvalue::Len(place)
                            | Rvalue::Discriminant(place) => places.push((*place, false)),
                            Rvalue::BinaryOp(_, box (a, b)) => {
                                places.extend(a.place().map(|p| (p, false)));
                                places.extend(b.place().map(|p| (p, false)));
                            }
                            Rvalue::Aggregate(_, ops) => {
                                places.extend(
                                    ops.iter().filter_map(|op| op.place()).map(|p| (p, false)),
                                );
                            }
                            // An address computes, it does not access.
                            Rvalue::Ref(..)
                            | Rvalue::RawPtr(..)
                            | Rvalue::ThreadLocalRef(_)
                            | Rvalue::NullaryOp(..) => {}
                        }
                    }
                    StatementKind::Intrinsic(box NonDivergingIntrinsic::CopyNonOverlapping(c)) => {
                        if let Some(l) = local_of(&c.src) {
                            through(&mut acc, l, false, location);
                        }
                        if let Some(l) = local_of(&c.dst) {
                            through(&mut acc, l, true, location);
                        }
                    }
                    StatementKind::SetDiscriminant { place, .. } | StatementKind::Deinit(place) => {
                        places.push((**place, true));
                    }
                    StatementKind::Intrinsic(box NonDivergingIntrinsic::Assume(_))
                    | StatementKind::FakeRead(..)
                    | StatementKind::StorageLive(_)
                    | StatementKind::StorageDead(_)
                    | StatementKind::Retag(..)
                    | StatementKind::PlaceMention(_)
                    | StatementKind::AscribeUserType(..)
                    | StatementKind::Coverage(_)
                    | StatementKind::ConstEvalCounter
                    | StatementKind::Nop
                    | StatementKind::BackwardIncompatibleDropHint { .. } => {}
                }
                for (place, write) in places {
                    if matches!(place.projection.first(), Some(ProjectionElem::Deref)) {
                        through(&mut acc, place.local, write, location);
                    }
                }
            }
            let location = Location {
                block,
                statement_index: data.statements.len(),
            };
            let mut places: Vec<(Place<'tcx>, bool)> = Vec::new();
            match &data.terminator().kind {
                TerminatorKind::Call { .. } | TerminatorKind::TailCall { .. } => {
                    let call = as_call(data.terminator(), tcx).expect("a call");
                    places.push((call.destination, true));
                    places.extend(
                        call.args
                            .iter()
                            .filter_map(|a| a.node.place())
                            .map(|p| (p, false)),
                    );
                    for g in self.call_targets(body, block) {
                        if g != f
                            && let Some(callee) = self.acc.get(&g)
                        {
                            inherited.extend(callee.iter().copied());
                        }
                        for (j, arg) in call.args.iter().enumerate() {
                            let Some(local) = local_of(&arg.node) else { continue };
                            let Some(&(r, w)) = self.param_acc.get(&(g, j + 1)) else { continue };
                            if r {
                                through(&mut acc, local, false, location);
                            }
                            if w {
                                through(&mut acc, local, true, location);
                            }
                        }
                    }
                    // Foreign effects, by contract (R9).
                    for name in self.foreign_effects(body, block, &call) {
                        let contract = if self.on(Rule::ForeignEffects) {
                            contract_of(&name)
                        } else {
                            Some(contract(&[], Eff::None, Ret::None))
                        };
                        // 2.9: `strtok` reads and writes the buffer it remembers.
                        if name == "strtok" && self.on(Rule::StrtokState) {
                            for &obj in &self.strtok {
                                acc.insert(Access {
                                    obj,
                                    write: true,
                                    at: (f, location),
                                    via: Via::Opaque,
                                    by: Local::from_usize(0),
                                });
                            }
                        }
                        for (j, arg) in call.args.iter().enumerate() {
                            let Some(local) = local_of(&arg.node) else { continue };
                            if !is_ptr(body.local_decls[local].ty) {
                                continue;
                            }
                            let eff = self.arg_effect(body, &call, &name, j);
                            if matches!(eff, Eff::Read | Eff::ReadWrite) {
                                through(&mut acc, local, false, location);
                            }
                            if matches!(eff, Eff::Write | Eff::ReadWrite) {
                                through(&mut acc, local, true, location);
                            }
                        }
                        // A function the call may call back (glob's error function), or
                        // an unlisted call: the accesses of every function item passed.
                        // M2: `exit` runs the handlers registered with the library.
                        if name == "exit" && self.on(Rule::Callbacks) {
                            for g in &self.handed_callbacks {
                                if let Some(callee) = self.acc.get(g) {
                                    inherited.extend(callee.iter().copied());
                                }
                            }
                        }
                        if contract.as_ref().is_none_or(|c| c.callback) {
                            // H5: through locals too (c2rust passes `Some(f)`).
                            let items = if self.on(Rule::Callbacks) {
                                self.fn_items_of(body)
                            } else {
                                FxHashMap::default()
                            };
                            for arg in call.args.iter() {
                                for d in self.fn_items_in(&arg.node, &items) {
                                    if let Some(g) = d.as_local()
                                        && let Some(callee) = self.acc.get(&g)
                                    {
                                        inherited.extend(callee.iter().copied());
                                    }
                                }
                            }
                        }
                        if contract.is_none() && self.on(Rule::TopFlows) {
                            // An unlisted call may write anywhere it can reach.
                            top_access(&mut acc, location);
                        }
                    }
                }
                TerminatorKind::SwitchInt { discr: op, .. }
                | TerminatorKind::Assert { cond: op, .. } => {
                    places.extend(op.place().map(|p| (p, false)));
                }
                TerminatorKind::Drop { place, .. } => places.push((*place, true)),
                TerminatorKind::InlineAsm { .. } | TerminatorKind::Yield { .. } => {
                    if self.on(Rule::TopFlows) {
                        top_access(&mut acc, location);
                    }
                }
                TerminatorKind::Goto { .. }
                | TerminatorKind::UnwindResume
                | TerminatorKind::UnwindTerminate(_)
                | TerminatorKind::Return
                | TerminatorKind::Unreachable
                | TerminatorKind::CoroutineDrop
                | TerminatorKind::FalseEdge { .. }
                | TerminatorKind::FalseUnwind { .. } => {}
            }
            for (place, write) in places {
                if matches!(place.projection.first(), Some(ProjectionElem::Deref)) {
                    through(&mut acc, place.local, write, location);
                }
            }
        }
        acc.extend(inherited);
        (acc, params)
    }

    fn is_byte(&self, ty: Ty<'tcx>) -> bool {
        match ty.kind() {
            TyKind::Int(rustc_middle::ty::IntTy::I8)
            | TyKind::Uint(rustc_middle::ty::UintTy::U8) => true,
            TyKind::Adt(adt, _) => self.tcx.item_name(adt.did()).as_str() == "c_void",
            TyKind::Array(element, _) | TyKind::Slice(element) => self.is_byte(*element),
            _ => false,
        }
    }

    /// 2.4: two types equal modulo the signedness of integers (C11 §6.5p7).
    fn same_ty(&self, a: Ty<'tcx>, b: Ty<'tcx>) -> bool {
        if a == b {
            return true;
        }
        if !self.on(Rule::Signedness) {
            return false;
        }
        use rustc_middle::ty::{IntTy as I, UintTy as U};
        let unsigned = |t: Ty<'tcx>| match t.kind() {
            TyKind::Int(I::I8) | TyKind::Uint(U::U8) => Some(8),
            TyKind::Int(I::I16) | TyKind::Uint(U::U16) => Some(16),
            TyKind::Int(I::I32) | TyKind::Uint(U::U32) => Some(32),
            TyKind::Int(I::I64) | TyKind::Uint(U::U64) => Some(64),
            TyKind::Int(I::I128) | TyKind::Uint(U::U128) => Some(128),
            TyKind::Int(I::Isize) | TyKind::Uint(U::Usize) => Some(0),
            _ => None,
        };
        matches!((unsigned(a), unsigned(b)), (Some(x), Some(y)) if x == y)
    }

    fn contains(&self, outer: Ty<'tcx>, inner: Ty<'tcx>, depth: usize) -> bool {
        if depth > 8 {
            return false;
        }
        match outer.kind() {
            TyKind::Adt(adt, args) if adt.is_struct() || adt.is_union() => {
                adt.all_fields().any(|field| {
                    let ty = self.tcx.erase_regions(field.ty(self.tcx, args));
                    self.same_ty(ty, inner) || self.contains(ty, inner, depth + 1)
                })
            }
            TyKind::Array(element, _) => {
                self.same_ty(*element, inner) || self.contains(*element, inner, depth + 1)
            }
            TyKind::Tuple(items) => items
                .iter()
                .any(|ty| self.same_ty(ty, inner) || self.contains(ty, inner, depth + 1)),
            _ => false,
        }
    }

    fn types_of(&self, obj: Obj) -> FxHashSet<TyId> {
        match obj {
            Obj::Static(id) | Obj::External(id) => FxHashSet::from_iter([id]),
            _ => self.obj_types.get(&obj).cloned().unwrap_or_default(),
        }
    }

    /// May the two objects be the same object (or one inside the other)?
    fn overlap(&self, a: Obj, b: Obj) -> bool {
        if a == b || a == Obj::Top || b == Obj::Top {
            return true;
        }
        // Members of one object overlap only along one path; an outside object meets a
        // member only as (a part of) the member's own type.
        if matches!(a, Obj::Sub(_)) || matches!(b, Obj::Sub(_)) {
            let (root_a, root_b) = (self.root(a), self.root(b));
            if root_a == root_b {
                let (pa, pb) = (self.path(a), self.path(b));
                let n = pa.len().min(pb.len());
                return pa[..n] == pb[..n];
            }
            let (member, other) = if matches!(a, Obj::Sub(_)) {
                (a, b)
            } else {
                (b, a)
            };
            if matches!(other, Obj::External(_) | Obj::Opaque(..))
                && let Obj::Sub(id) = member
                && let Some(ty) = self.sub_types[id as usize]
            {
                return self.overlap(root_a, root_b)
                    && self.types_meet_with(
                        &FxHashSet::from_iter([ty]),
                        &self.types_of(other),
                        // H1: the outside object may be the member's container.
                        self.on(Rule::Containers),
                        self.program_bytes(self.root(member)),
                    );
            }
            return self.overlap(root_a, root_b);
        }
        // R816-1: a fresh object is no other object.
        if matches!(a, Obj::Fresh(_)) || matches!(b, Obj::Fresh(_)) {
            return false;
        }
        let outside = |o: Obj| matches!(o, Obj::External(_) | Obj::Opaque(..));
        // The library's memory is never a program object.
        let library = |o: Obj| matches!(o, Obj::Opaque(..)) && self.on(Rule::LibraryMemory);
        match (outside(a), outside(b)) {
            (false, false) => false,
            // The library's object is a whole object of its type: an outside object may
            // be it or a part of it, never contain it.
            (true, true) if library(a) && !library(b) => self.types_meet(a, b, false),
            (true, true) if library(b) && !library(a) => self.types_meet(b, a, false),
            (true, true) => self.types_meet(a, b, true),
            (false, true) => !library(b) && self.program_meets(a, b),
            (true, false) => !library(a) && self.program_meets(b, a),
        }
    }

    /// A program object and an outside one (2.3): only an escaped program object, and
    /// then an outside byte pointer meets it whatever its type.
    fn program_meets(&self, program: Obj, outside: Obj) -> bool {
        if !self.on(Rule::Escape) {
            return self.types_meet(program, outside, false);
        }
        self.is_escaped(program)
            && self.types_meet_with(
                &self.types_of(program),
                &self.types_of(outside),
                // H1: an outside aggregate lvalue may access a program object of one of
                // its members' types (C11 6.5p7's aggregate clause).
                self.on(Rule::Containers),
                !self.options.program_bytes_disjoint,
            )
    }

    /// Under 2.3 a program object's bytes always meet an outside byte pointer.
    fn program_bytes(&self, program: Obj) -> bool {
        self.on(Rule::Escape)
            && !self.options.program_bytes_disjoint
            && !matches!(program, Obj::External(_) | Obj::Opaque(..) | Obj::Top)
    }

    /// `whole`'s types against `part`'s: equal, or `whole` contains `part`; both ways
    /// when `either`. An object never typed is a byte buffer.
    fn types_meet(&self, whole: Obj, part: Obj, either: bool) -> bool {
        self.types_meet_sets(&self.types_of(whole), &self.types_of(part), either)
    }

    fn types_meet_sets(&self, tw: &FxHashSet<TyId>, tp: &FxHashSet<TyId>, either: bool) -> bool {
        self.types_meet_with(tw, tp, either, false)
    }

    /// `bytes_meet`: a byte type in `tp` (the outside pointer's) meets any type in `tw`
    /// (an escaped program object under 2.3; R1 is about outside objects only). A program
    /// byte object and an outside typed pointer stay apart (C's effective types, R542).
    fn types_meet_with(
        &self,
        tw: &FxHashSet<TyId>,
        tp: &FxHashSet<TyId>,
        either: bool,
        bytes_meet: bool,
    ) -> bool {
        let (tw, tp) = (tw.clone(), tp.clone());
        let byte_only = |set: &FxHashSet<TyId>| {
            set.is_empty() || set.iter().all(|&t| self.is_byte(self.types[t]))
        };
        let has_byte = |set: &FxHashSet<TyId>| {
            set.is_empty() || set.iter().any(|&t| self.is_byte(self.types[t]))
        };
        if byte_only(&tw) || byte_only(&tp) {
            // 2.3: an outside byte pointer reaches any escaped program object.
            if bytes_meet && has_byte(&tp) {
                return true;
            }
            // R1: an outside byte object meets a typed one only without the premise.
            return (has_byte(&tw) && has_byte(&tp)) || !self.r1();
        }
        tw.iter().any(|&w| {
            tp.iter().any(|&p| {
                let (tw, tp) = (self.types[w], self.types[p]);
                if self.is_byte(tw) || self.is_byte(tp) {
                    return (bytes_meet && self.is_byte(tp))
                        || (self.is_byte(tw) && self.is_byte(tp))
                        || !self.r1();
                }
                self.same_ty(tw, tp)
                    || self.contains(tw, tp, 0)
                    || (either && self.contains(tp, tw, 0))
            })
        })
    }

    /// The pointer stores in `f` whose value is derived from parameter `formal`.
    fn derived_stores(
        &self,
        f: LocalDefId,
        body: &Body<'tcx>,
        formal: usize,
    ) -> Vec<(Location, Place<'tcx>)> {
        let derived = |l: Local| {
            self.from_param
                .get(&(f, l))
                .is_some_and(|params| params.contains(&formal))
        };
        self.derived_stores_by(body, &derived)
    }

    /// era-5c 145a AGG: everything a value of `seed` reaches inside the body through
    /// copies, casts, aggregates and field reads (no dereference), to a fixpoint.
    fn wide_family(&self, body: &Body<'tcx>, seed: &FxHashSet<Local>) -> FxHashSet<Local> {
        let mut family = seed.clone();
        if !self.on(Rule::WideStores) {
            return family;
        }
        loop {
            let before = family.len();
            for data in body.basic_blocks.iter() {
                for statement in &data.statements {
                    let StatementKind::Assign(box (dst, rvalue)) = &statement.kind else {
                        continue;
                    };
                    if !dst.projection.is_empty() {
                        continue;
                    }
                    let in_family = |op: &Operand<'tcx>| {
                        op.place().is_some_and(|place| {
                            family.contains(&place.local)
                                && !place
                                    .projection
                                    .iter()
                                    .any(|p| matches!(p, ProjectionElem::Deref))
                        })
                    };
                    let reaches = match rvalue {
                        Rvalue::Use(op) | Rvalue::Cast(_, op, _) => in_family(op),
                        Rvalue::Aggregate(_, ops) => ops.iter().any(in_family),
                        _ => false,
                    };
                    if reaches {
                        family.insert(dst.local);
                    }
                }
            }
            if family.len() == before {
                return family;
            }
        }
    }

    /// H6 (a): aggregate locals that carry a value `derived` holds, to a fixpoint.
    fn carriers_of(&self, body: &Body<'tcx>, derived: &dyn Fn(Local) -> bool) -> FxHashSet<Local> {
        let mut carriers: FxHashSet<Local> = FxHashSet::default();
        if self.on(Rule::WideStores) {
            loop {
                let before = carriers.len();
                for data in body.basic_blocks.iter() {
                    for statement in &data.statements {
                        let StatementKind::Assign(box (dst, rvalue)) = &statement.kind else {
                            continue;
                        };
                        if !dst.projection.is_empty() {
                            continue;
                        }
                        let carries = match rvalue {
                            Rvalue::Aggregate(_, ops) => ops.iter().any(|op| {
                                local_of(op).is_some_and(|l| derived(l) || carriers.contains(&l))
                            }),
                            Rvalue::Use(op) | Rvalue::Cast(_, op, _) => {
                                local_of(op).is_some_and(|l| carriers.contains(&l))
                            }
                            _ => false,
                        };
                        if carries {
                            carriers.insert(dst.local);
                        }
                    }
                }
                if carriers.len() == before {
                    break;
                }
            }
        }
        carriers
    }

    /// The stores of a value `derived` holds (a formal's family, or a local's: era-5c
    /// 145 H2), and the stores of a pointer field of it (H5: `(*g).px = s.p`).
    fn derived_stores_by(
        &self,
        body: &Body<'tcx>,
        derived: &dyn Fn(Local) -> bool,
    ) -> Vec<(Location, Place<'tcx>)> {
        let tcx = self.tcx;
        let carriers = self.carriers_of(body, derived);
        // era-5c 145 H5: a value read out of a derived aggregate's field (`_3 = s.p`, no
        // dereference) is derived, to a fixpoint.
        let mut read: FxHashSet<Local> = FxHashSet::default();
        if self.on(Rule::WideStores) {
            loop {
                let before = read.len();
                for data in body.basic_blocks.iter() {
                    for statement in &data.statements {
                        let StatementKind::Assign(box (dst, rvalue)) = &statement.kind else {
                            continue;
                        };
                        if !dst.projection.is_empty() {
                            continue;
                        }
                        if let Rvalue::Use(op) | Rvalue::Cast(_, op, _) = rvalue
                            && let Some(place) = op.place()
                            && !place
                                .projection
                                .iter()
                                .any(|p| matches!(p, ProjectionElem::Deref))
                            && (derived(place.local)
                                || carriers.contains(&place.local)
                                || read.contains(&place.local))
                        {
                            read.insert(dst.local);
                        }
                    }
                }
                if read.len() == before {
                    break;
                }
            }
        }
        let derived = |l: Local| derived(l) || read.contains(&l);
        let mut out = vec![];
        for (block, data) in body.basic_blocks.iter_enumerated() {
            for (statement_index, statement) in data.statements.iter().enumerate() {
                let StatementKind::Assign(box (dst, rvalue)) = &statement.kind else { continue };
                if dst.projection.is_empty() {
                    continue;
                }
                let location = Location {
                    block,
                    statement_index,
                };
                // H5: a pointer field of an aggregate value (`s.p`, no dereference).
                let field_of = |op: &Operand<'tcx>| {
                    op.place().filter(|place| {
                        self.on(Rule::WideStores)
                            && !place.projection.is_empty()
                            && !place
                                .projection
                                .iter()
                                .any(|p| matches!(p, ProjectionElem::Deref))
                    })
                };
                let stored = match rvalue {
                    Rvalue::Use(op) | Rvalue::Cast(_, op, _) => {
                        local_of(op).is_some_and(|l| {
                            (is_ptr(dst.ty(body, tcx).ty) && derived(l)) || carriers.contains(&l)
                        }) || field_of(op).is_some_and(|place| {
                            is_ptr(dst.ty(body, tcx).ty)
                                && (derived(place.local) || carriers.contains(&place.local))
                        })
                    }
                    Rvalue::Aggregate(_, ops) if self.on(Rule::WideStores) => {
                        ops.iter().any(|op| {
                            local_of(op).is_some_and(|l| derived(l) || carriers.contains(&l))
                        })
                    }
                    _ => false,
                };
                if stored {
                    out.push((location, *dst));
                }
            }
            // H6 (b): a C library function that stores a pointer derived from an argument
            // (`strtoul`'s end pointer), or an unlisted one, given the formal.
            if self.on(Rule::WideStores)
                && let Some(call) = as_call(data.terminator(), tcx)
                && let CallKind::LibC(name) = &call.func
            {
                let mentions = |i: usize| {
                    call.args
                        .get(i)
                        .and_then(|a| local_of(&a.node))
                        .is_some_and(|l| derived(l) || carriers.contains(&l))
                };
                let at = Location {
                    block,
                    statement_index: data.statements.len(),
                };
                let target = |i: usize| {
                    call.args
                        .get(i)
                        .and_then(|a| local_of(&a.node))
                        .map(|l| tcx.mk_place_deref(Place::from(l)))
                };
                match contract_of(name.as_str()) {
                    Some(c) => {
                        if let Some((to, from)) = c.store
                            && mentions(from)
                            && let Some(place) = target(to)
                        {
                            out.push((at, place));
                        }
                    }
                    None => {
                        if let Some(i) = (0..call.args.len()).find(|&i| mentions(i))
                            && let Some(place) = target(i)
                        {
                            out.push((at, place));
                        }
                    }
                }
            }
        }
        out
    }

    /// 2.12: does a value of `locals` escape into memory: stored, placed into an
    /// aggregate, its address taken, or passed to a formal its callee stores?
    fn escapes(
        &self,
        body: &Body<'tcx>,
        locals: &FxHashSet<Local>,
        stored_formals: &FxHashSet<(LocalDefId, usize)>,
    ) -> bool {
        if !self.stores_of(body, locals).is_empty() {
            return true;
        }
        let mentions = |op: &Operand<'tcx>| local_of(op).is_some_and(|l| locals.contains(&l));
        for (block, data) in body.basic_blocks.iter_enumerated() {
            for statement in &data.statements {
                if let StatementKind::Assign(box (_, rvalue)) = &statement.kind {
                    match rvalue {
                        Rvalue::Aggregate(_, ops) if ops.iter().any(mentions) => return true,
                        Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place)
                            if place.projection.is_empty() && locals.contains(&place.local) =>
                        {
                            return true;
                        }
                        _ => {}
                    }
                }
            }
            if !stored_formals.is_empty()
                && let Some(call) = as_call(data.terminator(), self.tcx)
            {
                for g in self.call_targets(body, block) {
                    for (j, arg) in call.args.iter().enumerate() {
                        if mentions(&arg.node) && stored_formals.contains(&(g, j + 1)) {
                            return true;
                        }
                    }
                }
            }
        }
        false
    }

    /// The pointer stores in `body` whose value is one of `locals`.
    fn stores_of(
        &self,
        body: &Body<'tcx>,
        locals: &FxHashSet<Local>,
    ) -> Vec<(Location, Place<'tcx>)> {
        let mut out = vec![];
        for (block, data) in body.basic_blocks.iter_enumerated() {
            for (statement_index, statement) in data.statements.iter().enumerate() {
                let StatementKind::Assign(box (dst, rvalue)) = &statement.kind else { continue };
                if dst.projection.is_empty() || !is_ptr(dst.ty(body, self.tcx).ty) {
                    continue;
                }
                let source = match rvalue {
                    Rvalue::Use(op) | Rvalue::Cast(_, op, _) => local_of(op),
                    _ => None,
                };
                if source.is_some_and(|l| locals.contains(&l)) {
                    out.push((
                        Location {
                            block,
                            statement_index,
                        },
                        *dst,
                    ));
                }
            }
        }
        out
    }

    /// The `Unknown` extents: functions whose extent loads a cell of a mixed object.
    fn unknown_extents(&self) -> FxHashSet<LocalDefId> {
        if !self.on(Rule::Unknown) {
            return FxHashSet::default();
        }
        let mut unknown: FxHashSet<LocalDefId> = self
            .cell_loads
            .iter()
            .filter(|(_, holder, _)| self.mixed(*holder))
            .map(|&(f, _, _)| f)
            .collect();
        loop {
            let mut grew = false;
            for &f in &self.functions {
                if unknown.contains(&f) {
                    continue;
                }
                let body = self.body(f);
                if body.basic_blocks.indices().any(|b| {
                    self.call_targets(&body, b)
                        .iter()
                        .any(|g| unknown.contains(g))
                }) {
                    unknown.insert(f);
                    grew = true;
                }
            }
            if !grew {
                return unknown;
            }
        }
    }

    /// The definitions of `body`'s locals: `dst` from `Some(src)` when it derives from
    /// `src` (copies, casts, offsets, addresses through it, deriving calls, and (R12) a
    /// callee's or a C library function's result derived from an argument), `None`
    /// otherwise.
    fn derivations(&self, body: &Body<'tcx>) -> Vec<(Local, Option<Local>)> {
        let tcx = self.tcx;
        let mut defs: Vec<(Local, Option<Local>)> = Vec::new();
        for (block, data) in body.basic_blocks.iter_enumerated() {
            for statement in &data.statements {
                let StatementKind::Assign(box (dst, rvalue)) = &statement.kind else { continue };
                if !dst.projection.is_empty() {
                    continue;
                }
                let source = match rvalue {
                    Rvalue::Use(op) | Rvalue::Cast(_, op, _) => local_of(op),
                    Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => {
                        matches!(place.projection.first(), Some(ProjectionElem::Deref))
                            .then_some(place.local)
                    }
                    Rvalue::BinaryOp(BinOp::Offset, box (base, _)) => local_of(base),
                    _ => None,
                };
                defs.push((dst.local, source));
            }
            let Some(call) = as_call(data.terminator(), tcx) else { continue };
            if !call.destination.projection.is_empty() {
                continue;
            }
            let dst = call.destination.local;
            let arg = |j: usize| call.args.get(j).and_then(|a| local_of(&a.node));
            let mut sources: Vec<Local> = Vec::new();
            match &call.func {
                CallKind::RustLib(did) if DERIVING.contains(&tcx.item_name(*did).as_str()) => {
                    sources.extend(arg(0));
                }
                CallKind::LibC(name) if self.on(Rule::ReturnedAlias) => {
                    if let Some(Contract {
                        ret: Ret::Arg(i), ..
                    }) = contract_of(name.as_str())
                    {
                        sources.extend(arg(i));
                    }
                }
                CallKind::FreeStanding(_)
                | CallKind::Impl(_)
                | CallKind::Closure
                | CallKind::Dynamic
                    if self.on(Rule::ReturnedAlias) =>
                {
                    // 2.5: a callee's return may also not derive from the argument.
                    defs.push((dst, None));
                    for g in self.call_targets(body, block) {
                        for &j in self
                            .from_param
                            .get(&(g, Local::from_usize(0)))
                            .into_iter()
                            .flatten()
                        {
                            sources.extend(arg(j - 1));
                        }
                    }
                }
                CallKind::RustLib(_)
                | CallKind::LibC(_)
                | CallKind::FreeStanding(_)
                | CallKind::Impl(_)
                | CallKind::Closure
                | CallKind::Dynamic => {}
            }
            if sources.is_empty() {
                defs.push((dst, None));
            }
            for s in sources {
                defs.push((dst, Some(s)));
            }
        }
        defs
    }

    /// The locals each local's value may derive from, transitively.
    fn bases_of(&self, body: &Body<'tcx>) -> FxHashMap<Local, FxHashSet<Local>> {
        let edges: Vec<(Local, Local)> = self
            .derivations(body)
            .into_iter()
            .filter_map(|(d, s)| s.map(|s| (d, s)))
            .collect();
        let mut bases: FxHashMap<Local, FxHashSet<Local>> = FxHashMap::default();
        loop {
            let mut changed = false;
            for &(dst, src) in &edges {
                let mut add: FxHashSet<Local> = bases.get(&src).cloned().unwrap_or_default();
                add.insert(src);
                let set = bases.entry(dst).or_default();
                let before = set.len();
                set.extend(add);
                changed |= set.len() != before;
            }
            if !changed {
                return bases;
            }
        }
    }

    /// R11: the locals that must derive from `local`: every definition of each derives
    /// from `local` or another of them (a greatest fixpoint, so loops stay in).
    fn must_family(
        &self,
        body: &Body<'tcx>,
        local: Local,
        defs: &[(Local, Option<Local>)],
    ) -> FxHashSet<Local> {
        let mut by_dst: FxHashMap<Local, Vec<Option<Local>>> = FxHashMap::default();
        for &(d, s) in defs {
            by_dst.entry(d).or_default().push(s);
        }
        let mut family: FxHashSet<Local> = by_dst
            .iter()
            .filter(|(d, sources)| {
                **d != local && d.as_usize() > body.arg_count && sources.iter().all(|s| s.is_some())
            })
            .map(|(&d, _)| d)
            .collect();
        family.insert(local);
        loop {
            let before = family.len();
            let keep: FxHashSet<Local> = family
                .iter()
                .copied()
                .filter(|&m| {
                    m == local
                        || by_dst.get(&m).is_some_and(|sources| {
                            sources
                                .iter()
                                .all(|s| s.is_some_and(|s| family.contains(&s)))
                        })
                })
                .collect();
            family = keep;
            if family.len() == before {
                return family;
            }
        }
    }
}

/// The fields `(struct, index)` into which `body` stores a pointer derived from the
/// store's own base: a pointer into the object that holds it.
fn self_fields<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    bases: &FxHashMap<Local, FxHashSet<Local>>,
    out: &mut FxHashSet<(DefId, usize)>,
    wide: bool,
) {
    // era-5c 145 H4: an address of a local's own place (`&mut h.x`, no dereference)
    // has that local as a base, through copies and casts, to a fixpoint.
    let mut addr: FxHashMap<Local, FxHashSet<Local>> = FxHashMap::default();
    if wide {
        loop {
            let mut grew = false;
            for data in body.basic_blocks.iter() {
                for statement in &data.statements {
                    let StatementKind::Assign(box (dst, rvalue)) = &statement.kind else {
                        continue;
                    };
                    if !dst.projection.is_empty() {
                        continue;
                    }
                    let from: FxHashSet<Local> = match rvalue {
                        Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place)
                            if !place
                                .projection
                                .iter()
                                .any(|p| matches!(p, ProjectionElem::Deref)) =>
                        {
                            FxHashSet::from_iter([place.local])
                        }
                        Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => {
                            addr.get(&place.local).cloned().unwrap_or_default()
                        }
                        Rvalue::Use(op) | Rvalue::Cast(_, op, _) => local_of(op)
                            .and_then(|l| addr.get(&l).cloned())
                            .unwrap_or_default(),
                        _ => FxHashSet::default(),
                    };
                    if !from.is_empty() {
                        let set = addr.entry(dst.local).or_default();
                        let before = set.len();
                        set.extend(from);
                        grew |= set.len() != before;
                    }
                }
            }
            if !grew {
                break;
            }
        }
    }
    let with = |local: Local| {
        let mut set = bases.get(&local).cloned().unwrap_or_default();
        set.extend(addr.get(&local).into_iter().flatten().copied());
        set.insert(local);
        set
    };
    // era-5c 145a SLOT: a local holding the address of a struct field of a local's own
    // place (`slot = &raw mut h.q`), through copies and casts: `*slot = v` stores `h.q`.
    let mut field_addr: FxHashMap<Local, (Local, DefId, usize)> = FxHashMap::default();
    if wide {
        for _ in 0..4 {
            for data in body.basic_blocks.iter() {
                for statement in &data.statements {
                    let StatementKind::Assign(box (dst, rvalue)) = &statement.kind else {
                        continue;
                    };
                    if !dst.projection.is_empty() {
                        continue;
                    }
                    let found = match rvalue {
                        Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place)
                            if !place
                                .projection
                                .iter()
                                .any(|p| matches!(p, ProjectionElem::Deref)) =>
                        {
                            match place.projection.last() {
                                Some(ProjectionElem::Field(index, _)) => {
                                    let parent = Place {
                                        local: place.local,
                                        projection: tcx.mk_place_elems(
                                            &place.projection[..place.projection.len() - 1],
                                        ),
                                    };
                                    match parent.ty(body, tcx).ty.kind() {
                                        TyKind::Adt(adt, _) if adt.is_struct() => {
                                            Some((place.local, adt.did(), index.index()))
                                        }
                                        _ => None,
                                    }
                                }
                                _ => None,
                            }
                        }
                        Rvalue::Use(op) | Rvalue::Cast(_, op, _) => {
                            local_of(op).and_then(|l| field_addr.get(&l).copied())
                        }
                        _ => None,
                    };
                    if let Some(found) = found {
                        field_addr.insert(dst.local, found);
                    }
                }
            }
        }
    }
    for data in body.basic_blocks.iter() {
        for statement in &data.statements {
            let StatementKind::Assign(box (dst, rvalue)) = &statement.kind else { continue };
            // era-5c 145a SLOT: `*slot = v`, `slot` the address of `base.field`.
            if let [ProjectionElem::Deref] = dst.projection.as_slice()
                && let Some(&(base, did, index)) = field_addr.get(&dst.local)
            {
                let value = match rvalue {
                    Rvalue::Use(op) | Rvalue::Cast(_, op, _) => local_of(op),
                    Rvalue::RawPtr(_, place) | Rvalue::Ref(_, _, place) => Some(place.local),
                    _ => None,
                };
                if let Some(value) = value
                    && !with(value).is_disjoint(&with(base))
                {
                    out.insert((did, index));
                }
                continue;
            }
            // era-5c 145 H4: a stack struct's own field (`h.q = …`) as well as a
            // pointee's (`(*s).q = …`).
            if !wide && !matches!(dst.projection.first(), Some(ProjectionElem::Deref)) {
                continue;
            }
            let Some(ProjectionElem::Field(index, _)) = dst.projection.last() else { continue };
            let parent = Place {
                local: dst.local,
                projection: tcx.mk_place_elems(&dst.projection[..dst.projection.len() - 1]),
            };
            let TyKind::Adt(adt, _) = parent.ty(body, tcx).ty.kind() else { continue };
            let value = match rvalue {
                Rvalue::Use(op) | Rvalue::Cast(_, op, _) => local_of(op),
                // era-5c 145 H4: an address of a place of the same base (`&raw mut h.x`).
                Rvalue::RawPtr(_, place) | Rvalue::Ref(_, _, place) if wide => Some(place.local),
                _ => None,
            };
            if let Some(value) = value
                && !with(value).is_disjoint(&with(dst.local))
            {
                out.insert((adt.did(), index.index()));
            }
        }
    }
}

/// How the object an access reaches is reachable through memory.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum Shape {
    /// A field of it holds a pointer into it, stored from its own base.
    SelfRef,
    /// It holds an object that holds it.
    Cycle,
    /// A field of it holds an object of its own abstract site.
    Recursive,
    Other,
}

impl Shape {
    pub(crate) fn label(self) -> &'static str {
        match self {
            Shape::SelfRef => "self",
            Shape::Cycle => "cycle",
            Shape::Recursive => "recursive",
            Shape::Other => "other",
        }
    }
}

struct Shapes {
    self_holders: FxHashSet<Obj>,
    children: FxHashMap<Obj, FxHashSet<Obj>>,
}

impl Shapes {
    fn new(relation: &Relation<'_>, fields: &FxHashSet<(DefId, usize)>) -> Self {
        let mut self_holders = FxHashSet::default();
        let mut children: FxHashMap<Obj, FxHashSet<Obj>> = FxHashMap::default();
        for (key, objs) in &relation.contents {
            // Shapes are of whole objects: a pointer to a member points into its root.
            let objs = &relation.roots(objs.iter().copied());
            if let Key::Field(holder, did, index) = *key
                && objs.contains(&holder)
                && fields.contains(&(did, index))
            {
                self_holders.insert(holder);
            }
            children
                .entry(key.holder())
                .or_default()
                .extend(objs.iter().copied());
        }
        Shapes {
            self_holders,
            children,
        }
    }

    fn of(&self, obj: Obj) -> Shape {
        if self.self_holders.contains(&obj) {
            return Shape::SelfRef;
        }
        let held = self.children.get(&obj);
        if held.into_iter().flatten().any(|&q| {
            q != obj
                && self
                    .children
                    .get(&q)
                    .is_some_and(|back| back.contains(&obj))
        }) {
            return Shape::Cycle;
        }
        if held.is_some_and(|set| set.contains(&obj)) {
            return Shape::Recursive;
        }
        Shape::Other
    }
}

/// What the access does to the subject's memory.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum AccessKind {
    Write,
    Read,
}

/// Why the subject is held.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum HoldKind {
    /// An access through a retained pointer in the subject's extent may reach it.
    Access,
    /// A formal: a value derived from it is stored into memory (the witness is the
    /// store's location); wave-6o's return permit reads this kind.
    DerivedStore,
}

/// One reason a subject is held.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct Hold {
    pub(crate) kind: HoldKind,
    pub(crate) access: AccessKind,
    pub(crate) shape: Shape,
    /// `Struct.field`, `elem:<ty>`, `opaque`, `unresolved` or `unknown`.
    pub(crate) retaining_place: String,
    /// `fn | retaining place | file:line`.
    pub(crate) witness: String,
}

/// The check's verdict for one subject.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Verdict {
    Clear,
    Held(Vec<Hold>),
    /// The relation cannot see the subject's access set (an unmodelled kind, or a mixed
    /// object's cell loaded in its extent). Held, fail-closed.
    Unknown,
}

impl Verdict {
    /// Does the check withdraw the subject's safe decision?
    pub(crate) fn withdraws(&self) -> bool {
        !matches!(self, Verdict::Clear)
    }

    /// The census receipt of (E) (R826-1): `evident:<rule>:<retaining place> | <witness>`
    /// of the first hold, the rule one of `derived-store`, `self-reference`, `cycle`.
    pub(crate) fn evident_receipt(&self) -> Option<String> {
        let Verdict::Held(holds) = self else { return None };
        holds.first().map(|hold| {
            let rule = match (hold.kind, hold.shape) {
                (HoldKind::DerivedStore, _) => "derived-store",
                (HoldKind::Access, Shape::SelfRef) => "self-reference",
                (HoldKind::Access, Shape::Cycle) => "cycle",
                (HoldKind::Access, Shape::Recursive | Shape::Other) => "other",
            };
            format!("evident:{rule}:{} | {}", hold.retaining_place, hold.witness)
        })
    }

    /// The receipt detail: `<kind>:<witness>` of the first hold, or `unknown`.
    pub(crate) fn receipt(&self) -> Option<String> {
        match self {
            Verdict::Clear => None,
            Verdict::Unknown => Some("unknown".to_owned()),
            Verdict::Held(holds) => holds.first().map(|hold| {
                format!(
                    "{}:{}",
                    match hold.kind {
                        HoldKind::Access => match hold.access {
                            AccessKind::Write => "write",
                            AccessKind::Read => "read",
                        },
                        HoldKind::DerivedStore => "derived-store",
                    },
                    hold.witness
                )
            }),
        }
    }
}

/// The identity of a MIR body (R13): its owner, its locals' types and its whole text.
pub(crate) fn body_identity(body: &Body<'_>) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut h = std::collections::hash_map::DefaultHasher::new();
    format!("{:?}", body.source.def_id()).hash(&mut h);
    body.arg_count.hash(&mut h);
    for decl in body.local_decls.iter() {
        format!("{:?}", decl.ty).hash(&mut h);
    }
    for data in body.basic_blocks.iter() {
        format!("{:?}", data.statements).hash(&mut h);
        format!("{:?}", data.terminator().kind).hash(&mut h);
    }
    h.finish()
}

/// The check over one crate: a verdict for every raw-pointer formal and local.
pub(crate) struct RetainedAccessCheck {
    verdicts: FxHashMap<(LocalDefId, Local), Verdict>,
    bodies: FxHashMap<LocalDefId, u64>,
    /// The container-of sites (item 4's corpus scan): locals made by an unbounded offset
    /// of a member's byte view.
    container_of: Vec<(LocalDefId, Local)>,
    /// Subjects Clear only under P8 (`OutsideByteViewDiscipline`, relay 176): the
    /// receipt `premise=outside-byte-view`.
    premised: FxHashSet<(LocalDefId, Local)>,
}

impl RetainedAccessCheck {
    /// The check under the model's field kinds: a retaining field the model decides
    /// `Ref` or `Owning` is not a raw retaining place (132 §2's guard).
    /// The check of record (R826-1, USER: "(E)로 가자"): the evident shapes, held by
    /// rule, in the closed world (R816-1). Everything else stands under P9
    /// `RetainedAccessFreedom`. M1's round trip is off: it feeds only holds outside the
    /// evident shapes, which P9 covers by statement (era-5c 143 §6).
    pub(crate) fn compute(
        program: &RustProgram<'_>,
        slots: &CrateSlots,
        model: &FxHashMap<SlotRef, SlotKind>,
    ) -> Self {
        Self::compute_options(
            program,
            &Self::model_fields(slots, model),
            Options::of_record(),
        )
    }

    /// The model's field kinds as the raw guard reads them: a retaining field the
    /// model decides `Ref` or `Owning` is not a raw retaining place (132 §2).
    fn model_fields<'m>(
        slots: &'m CrateSlots,
        model: &'m FxHashMap<SlotRef, SlotKind>,
    ) -> impl Fn(DefId, usize) -> bool + 'm {
        move |did: DefId, index: usize| {
            let Some(struct_did) = did.as_local() else { return true };
            let kind = slots
                .field_slots
                .slot_for_field_depth(
                    crate::analyses::borrow_ownership::slots::StructFieldSlot {
                        struct_did,
                        field_index: index,
                    },
                    0,
                )
                .map(SlotRef::Field)
                .and_then(|slot| model.get(&slot).copied());
            !matches!(kind, Some(SlotKind::Ref | SlotKind::Owning))
        }
    }

    /// The check with the raw-field predicate given.
    pub(crate) fn compute_with(
        program: &RustProgram<'_>,
        field_raw: &dyn Fn(DefId, usize) -> bool,
    ) -> Self {
        Self::compute_options(program, field_raw, Options::default())
    }

    /// The check with `fault` removed: the witnesses' faults.
    pub(crate) fn compute_faulted(
        program: &RustProgram<'_>,
        field_raw: &dyn Fn(DefId, usize) -> bool,
        fault: Option<Rule>,
    ) -> Self {
        Self::compute_options(
            program,
            field_raw,
            Options {
                fault,
                ..Options::default()
            },
        )
    }

    pub(crate) fn compute_options(
        program: &RustProgram<'_>,
        field_raw: &dyn Fn(DefId, usize) -> bool,
        options: Options,
    ) -> Self {
        let tcx = program.tcx;
        let relation = Relation::new(program, options);
        let on = |rule: Rule| relation.on(rule);
        let unknown = relation.unknown_extents();
        let mut fields = FxHashSet::default();
        for &f in &program.functions {
            let body = relation.body(f);
            let bases = relation.bases_of(&body);
            self_fields(tcx, &body, &bases, &mut fields, on(Rule::SelfStores));
        }
        let shapes = Shapes::new(&relation, &fields);
        let mut spans: FxHashMap<(LocalDefId, Location), String> = FxHashMap::default();
        let mut line_of = |f: LocalDefId, location: Location| -> String {
            spans
                .entry((f, location))
                .or_insert_with(|| {
                    let body = relation.body(f);
                    let span = body.source_info(location).span.source_callsite();
                    let pos = tcx.sess.source_map().lookup_char_pos(span.lo());
                    format!("{}:{}", pos.file.name.prefer_local(), pos.line)
                })
                .clone()
        };
        let place_name = |via: Via| -> String {
            match via {
                Via::Field(did, index) => {
                    let adt = tcx.adt_def(did);
                    let field = adt
                        .all_fields()
                        .nth(index)
                        .map_or_else(|| format!("{index}"), |field| field.name.to_string());
                    format!("{}.{field}", tcx.item_name(did))
                }
                Via::Cell(ty) => format!("elem:{}", relation.types[ty]),
                Via::Opaque => "opaque".to_owned(),
                Via::Unresolved => "unresolved".to_owned(),
                Via::Unknown => "unknown".to_owned(),
            }
        };
        let raw_via = |via: Via| match via {
            Via::Field(did, index) => !on(Rule::RawGuard) || field_raw(did, index),
            Via::Cell(_) | Via::Opaque | Via::Unresolved | Via::Unknown => true,
        };
        // era-5c 145a TOP: an access through `Top` has no shape of its own; it reaches the
        // subject, so the subject's own evident shape is the hold's.
        let top_shape = |mut hold: Hold, objs: &FxHashSet<Obj>, access: &Access| {
            if access.obj == Obj::Top
                && on(Rule::TopShape)
                && !matches!(hold.shape, Shape::SelfRef | Shape::Cycle)
                && let Some(shape) = objs
                    .iter()
                    .map(|&o| shapes.of(relation.root(o)))
                    .find(|shape| matches!(shape, Shape::SelfRef | Shape::Cycle))
            {
                hold.shape = shape;
            }
            hold
        };
        let hold_of =
            |access: &Access, line_of: &mut dyn FnMut(LocalDefId, Location) -> String| Hold {
                kind: HoldKind::Access,
                access: if access.write {
                    AccessKind::Write
                } else {
                    AccessKind::Read
                },
                shape: shapes.of(relation.root(access.obj)),
                retaining_place: place_name(access.via),
                witness: format!(
                    "{} | {} | {}",
                    tcx.def_path_str(access.at.0.to_def_id()),
                    place_name(access.via),
                    line_of(access.at.0, access.at.1)
                ),
            };
        // A hold that rests on `Top` (either side) is an unknown one.
        let unknown_hold = |objs: &FxHashSet<Obj>, access: &Access| {
            access.obj == Obj::Top || objs.contains(&Obj::Top)
        };
        let mut verdicts = FxHashMap::default();
        let mut premised: FxHashSet<(LocalDefId, Local)> = FxHashSet::default();
        let mut bodies = FxHashMap::default();
        // The formals a function stores a derived value of (2.12's callee side).
        let mut stored_formals: FxHashSet<(LocalDefId, usize)> = FxHashSet::default();
        for &f in &program.functions {
            let body = relation.body(f);
            for i in 1..=body.arg_count {
                if !relation.derived_stores(f, &body, i).is_empty() {
                    stored_formals.insert((f, i));
                }
            }
        }
        // H6 (c): the formals whose value a callee stores into memory, through any chain of
        // callees (seeded by real stores only; closed over the call edges below).
        let mut memory_stored: FxHashSet<(LocalDefId, usize)> = stored_formals.clone();
        // 3.8: a formal whose derivations escape the callee's frame (into an aggregate,
        // its address taken, or to another stored formal) is stored too. One pass makes
        // each formal's own escape and its call edges (callee, argument position); the
        // closure runs over the edges.
        if on(Rule::EscapingExtent) && on(Rule::AggregateTransfer) {
            let none = FxHashSet::default();
            let mut edges: FxHashMap<(LocalDefId, usize), Vec<(LocalDefId, usize)>> =
                FxHashMap::default();
            let mut work: Vec<(LocalDefId, usize)> = stored_formals.iter().copied().collect();
            for &f in &program.functions {
                let body = relation.body(f);
                let bases = relation.bases_of(&body);
                let calls: Vec<(BasicBlock, Vec<LocalDefId>)> = body
                    .basic_blocks
                    .indices()
                    .filter(|&b| as_call(body.basic_blocks[b].terminator(), tcx).is_some())
                    .map(|b| (b, relation.call_targets(&body, b)))
                    .collect();
                for i in 1..=body.arg_count {
                    let formal = Local::from_usize(i);
                    let mut derived: FxHashSet<Local> = bases
                        .iter()
                        .filter(|(_, b)| b.contains(&formal))
                        .map(|(&l, _)| l)
                        .collect();
                    derived.insert(formal);
                    // era-5c 145 H5: an aggregate built from the formal carries it to a callee.
                    let carried = relation.carriers_of(&body, &|l: Local| derived.contains(&l));
                    derived.extend(carried);
                    // era-5c 145a AGG: and field reads of them, to a fixpoint.
                    let reached = relation.wide_family(&body, &derived);
                    derived.extend(reached);
                    if !stored_formals.contains(&(f, i)) && relation.escapes(&body, &derived, &none)
                    {
                        stored_formals.insert((f, i));
                        work.push((f, i));
                    }
                    for (b, targets) in &calls {
                        let call =
                            as_call(body.basic_blocks[*b].terminator(), tcx).expect("a call");
                        for (j, arg) in call.args.iter().enumerate() {
                            if local_of(&arg.node).is_some_and(|l| derived.contains(&l)) {
                                for &g in targets {
                                    edges.entry((g, j + 1)).or_default().push((f, i));
                                }
                            }
                        }
                    }
                }
            }
            // A callee's stored formal makes every caller's formal passed there stored.
            while let Some(stored) = work.pop() {
                for &caller in edges.get(&stored).into_iter().flatten() {
                    if stored_formals.insert(caller) {
                        work.push(caller);
                    }
                }
            }
            if on(Rule::WideStores) {
                let mut work: Vec<(LocalDefId, usize)> = memory_stored.iter().copied().collect();
                while let Some(stored) = work.pop() {
                    for &caller in edges.get(&stored).into_iter().flatten() {
                        if memory_stored.insert(caller) {
                            work.push(caller);
                        }
                    }
                }
            }
        }
        for &f in &program.functions {
            let body = relation.body(f);
            bodies.insert(f, body_identity(&body));
            let in_extent: Vec<Access> = relation
                .acc
                .get(&f)
                .into_iter()
                .flatten()
                .copied()
                .collect();
            // Formals: protected for the whole call, so the extent is the function's.
            for i in 1..=body.arg_count {
                let local = Local::from_usize(i);
                if !body.local_decls[local].ty.is_raw_ptr() {
                    continue;
                }
                let objs = relation
                    .points
                    .get(&(f, local))
                    .cloned()
                    .unwrap_or_default();
                let mutable = relation.param_acc.get(&(f, i)).is_some_and(|&(_, w)| w);
                let mut holds: Vec<Hold> = vec![];
                let mut unknowns = false;
                let mut p8 = false;
                for a in &in_extent {
                    if !raw_via(a.via) || !(a.write || (mutable && on(Rule::MutRead))) {
                        continue;
                    }
                    let pointee = body.local_decls[local].ty.builtin_deref(true);
                    if !relation.meets(&objs, pointee, a) {
                        p8 |= !relation.options.by_types && relation.meets_without_p8(&objs, a.obj);
                        continue;
                    }
                    if unknown_hold(&objs, a) {
                        unknowns = true;
                        // era-5c 145 H1: (E) keeps an evident shape all the same.
                        if relation.options.evident && on(Rule::EvidentUnknown) {
                            holds.push(top_shape(hold_of(a, &mut line_of), &objs, a));
                        }
                    } else {
                        holds.push(hold_of(a, &mut line_of));
                    }
                }
                if on(Rule::DerivedStore) {
                    let stores = relation.derived_stores(f, &body, i);
                    // H6 (c): a callee keeps it in memory.
                    if stores.is_empty() && memory_stored.contains(&(f, i)) {
                        holds.push(Hold {
                            kind: HoldKind::DerivedStore,
                            access: AccessKind::Write,
                            shape: Shape::Other,
                            retaining_place: "callee-store".to_owned(),
                            witness: format!(
                                "{} | callee-store | {}",
                                tcx.def_path_str(f.to_def_id()),
                                line_of(f, Location::START)
                            ),
                        });
                    }
                    for (location, dst) in stores {
                        let place = match dst.projection.last() {
                            Some(ProjectionElem::Field(field, _)) => {
                                let parent = Place {
                                    local: dst.local,
                                    projection: tcx.mk_place_elems(
                                        &dst.projection[..dst.projection.len() - 1],
                                    ),
                                };
                                match parent.ty(&*body, tcx).ty.kind() {
                                    TyKind::Adt(adt, _) => {
                                        place_name(Via::Field(adt.did(), field.index()))
                                    }
                                    _ => "elem".to_owned(),
                                }
                            }
                            _ => format!("elem:{}", dst.ty(&*body, tcx).ty),
                        };
                        holds.push(Hold {
                            kind: HoldKind::DerivedStore,
                            access: AccessKind::Write,
                            shape: Shape::Other,
                            retaining_place: place.clone(),
                            witness: format!(
                                "{} | {} | {}",
                                tcx.def_path_str(f.to_def_id()),
                                place,
                                line_of(f, location)
                            ),
                        });
                    }
                }
                let verdict =
                    Self::finish(&relation.options, holds, unknowns || unknown.contains(&f));
                // P8's receipt: Clear only because of the premise.
                if p8 && verdict == Verdict::Clear {
                    premised.insert((f, local));
                }
                verdicts.insert((f, local), verdict);
            }
            // Locals: an access at a statement where the local, or a local derived from
            // it, is live; only the local's must-derived family is not foreign.
            let defs = relation.derivations(&body);
            let bases = relation.bases_of(&body);
            let mut written: FxHashSet<Local> = FxHashSet::default();
            for (block, data) in body.basic_blocks.iter_enumerated() {
                for statement in &data.statements {
                    if let StatementKind::Assign(box (dst, _)) = &statement.kind
                        && matches!(dst.projection.first(), Some(ProjectionElem::Deref))
                    {
                        written.insert(dst.local);
                    }
                    if let StatementKind::Intrinsic(box NonDivergingIntrinsic::CopyNonOverlapping(
                        c,
                    )) = &statement.kind
                        && on(Rule::ForeignMutability)
                        && let Some(l) = local_of(&c.dst)
                    {
                        written.insert(l);
                    }
                }
                if let Some(call) = as_call(data.terminator(), tcx) {
                    // 2.6: a foreign or unknown call's writes make a local mutable too.
                    if on(Rule::ForeignMutability) {
                        for name in relation.foreign_effects(&body, block, &call) {
                            for (j, arg) in call.args.iter().enumerate() {
                                if let Some(l) = local_of(&arg.node)
                                    && is_ptr(body.local_decls[l].ty)
                                    && matches!(
                                        relation.arg_effect(&body, &call, &name, j),
                                        Eff::Write | Eff::ReadWrite
                                    )
                                {
                                    written.insert(l);
                                }
                            }
                        }
                    }
                    if matches!(
                        call.destination.projection.first(),
                        Some(ProjectionElem::Deref)
                    ) {
                        written.insert(call.destination.local);
                    }
                    for g in relation.call_targets(&body, block) {
                        for (j, arg) in call.args.iter().enumerate() {
                            if let Some(l) = local_of(&arg.node)
                                && relation.param_acc.get(&(g, j + 1)).is_some_and(|&(_, w)| w)
                            {
                                written.insert(l);
                            }
                        }
                    }
                }
            }
            let mut at: FxHashMap<BasicBlock, Vec<Access>> = FxHashMap::default();
            for access in &in_extent {
                if access.at.0 == f {
                    at.entry(access.at.1.block).or_default().push(*access);
                }
            }
            // H5: a C library call that may call back (a callback contract, an unlisted
            // function) runs the functions handed to it at that call.
            let items = if on(Rule::Callbacks) {
                relation.fn_items_of(&body)
            } else {
                FxHashMap::default()
            };
            let mut recursive_at: FxHashMap<BasicBlock, Vec<Access>> = FxHashMap::default();
            for block in body.basic_blocks.indices() {
                for g in relation.call_targets(&body, block) {
                    if g != f {
                        at.entry(block)
                            .or_default()
                            .extend(relation.acc.get(&g).into_iter().flatten().copied());
                    } else if relation.options.close_n1 {
                        // era-5c 145a REC: another activation's accesses, which the
                        // subject's own family does not cover.
                        recursive_at
                            .entry(block)
                            .or_default()
                            .extend(relation.acc.get(&g).into_iter().flatten().copied());
                    }
                }
                if on(Rule::Callbacks)
                    && let Some(call) = as_call(body.basic_blocks[block].terminator(), tcx)
                    && let CallKind::LibC(name) = &call.func
                    && name.as_str() == "exit"
                {
                    for g in relation.handed_callbacks.iter().filter(|&&g| g != f) {
                        at.entry(block)
                            .or_default()
                            .extend(relation.acc.get(g).into_iter().flatten().copied());
                    }
                }
                if on(Rule::Callbacks)
                    && let Some(call) = as_call(body.basic_blocks[block].terminator(), tcx)
                    && let CallKind::LibC(name) = &call.func
                    && contract_of(name.as_str()).is_none_or(|c| c.callback)
                {
                    for arg in call.args.iter() {
                        for d in relation.fn_items_in(&arg.node, &items) {
                            if let Some(g) = d.as_local()
                                && g != f
                            {
                                at.entry(block)
                                    .or_default()
                                    .extend(relation.acc.get(&g).into_iter().flatten().copied());
                            }
                        }
                    }
                }
            }
            let mut live = MaybeLiveLocals
                .iterate_to_fixpoint(tcx, &body, None)
                .into_results_cursor(&body);
            let mut live_at: FxHashMap<BasicBlock, FxHashSet<Local>> = FxHashMap::default();
            for (block, data) in body.basic_blocks.iter_enumerated() {
                let set = live_at.entry(block).or_default();
                live.seek_to_block_start(block);
                set.extend(live.get().iter());
                live.seek_to_block_end(block);
                set.extend(live.get().iter());
                if on(Rule::StatementLiveness) {
                    for statement_index in 0..=data.statements.len() {
                        let location = Location {
                            block,
                            statement_index,
                        };
                        live.seek_before_primary_effect(location);
                        set.extend(live.get().iter());
                        live.seek_after_primary_effect(location);
                        set.extend(live.get().iter());
                    }
                }
            }
            for local in body.local_decls.indices().skip(body.arg_count + 1) {
                if !body.local_decls[local].ty.is_raw_ptr() {
                    continue;
                }
                let objs = relation
                    .points
                    .get(&(f, local))
                    .cloned()
                    .unwrap_or_default();
                let mut derived: FxHashSet<Local> = bases
                    .iter()
                    .filter(|(_, set)| set.contains(&local))
                    .map(|(&m, _)| m)
                    .collect();
                derived.insert(local);
                let family: FxHashSet<Local> = if on(Rule::MustDerive) {
                    relation.must_family(&body, local, &defs)
                } else {
                    let mut roots: FxHashSet<Local> =
                        bases.get(&local).cloned().unwrap_or_default();
                    roots.insert(local);
                    body.local_decls
                        .indices()
                        .filter(|m| {
                            let mut set = bases.get(m).cloned().unwrap_or_default();
                            set.insert(*m);
                            !set.is_disjoint(&roots)
                        })
                        .collect()
                };
                let mutable = !written.is_disjoint(&derived);
                // 2.12: a value of the local carried in memory or an aggregate outlives
                // the local's liveness: the extent is the whole function.
                let everywhere =
                    on(Rule::EscapingExtent) && relation.escapes(&body, &derived, &stored_formals);
                let mut holds: Vec<Hold> = vec![];
                // A local's derived value stored into memory outlives its loan as a raw
                // child of it (era-5c 140 §5: brotli's `h#488`, `h->symbol_lists = &h->…`).
                if on(Rule::DerivedStore) {
                    let mut stores = relation.stores_of(&body, &derived);
                    if on(Rule::LocalWideStores) {
                        // era-5c 145 H2: a local's derived stores are a formal's.
                        let wide =
                            relation.derived_stores_by(&body, &|l: Local| derived.contains(&l));
                        for store in wide {
                            if !stores.contains(&store) {
                                stores.push(store);
                            }
                        }
                        // ... and a callee that stores what it is passed.
                        let carriers = relation.wide_family(&body, &derived);
                        for (block, data) in body.basic_blocks.iter_enumerated() {
                            let Some(call) = as_call(data.terminator(), tcx) else { continue };
                            let targets = relation.call_targets(&body, block);
                            for (j, arg) in call.args.iter().enumerate() {
                                let passed = local_of(&arg.node)
                                    .filter(|l| derived.contains(l) || carriers.contains(l));
                                if let Some(l) = passed
                                    && targets.iter().any(|&g| memory_stored.contains(&(g, j + 1)))
                                {
                                    let location = Location {
                                        block,
                                        statement_index: data.statements.len(),
                                    };
                                    stores.push((location, Place::from(l)));
                                }
                            }
                        }
                    }
                    for (location, dst) in stores {
                        let place = match dst.projection.last() {
                            Some(ProjectionElem::Field(field, _)) => {
                                let parent = Place {
                                    local: dst.local,
                                    projection: tcx.mk_place_elems(
                                        &dst.projection[..dst.projection.len() - 1],
                                    ),
                                };
                                match parent.ty(&*body, tcx).ty.kind() {
                                    TyKind::Adt(adt, _) => {
                                        place_name(Via::Field(adt.did(), field.index()))
                                    }
                                    _ => "elem".to_owned(),
                                }
                            }
                            _ => format!("elem:{}", dst.ty(&*body, tcx).ty),
                        };
                        holds.push(Hold {
                            kind: HoldKind::DerivedStore,
                            access: AccessKind::Write,
                            shape: Shape::Other,
                            retaining_place: place.clone(),
                            witness: format!(
                                "{} | {} | {}",
                                tcx.def_path_str(f.to_def_id()),
                                place,
                                line_of(f, location)
                            ),
                        });
                    }
                }
                let mut unknowns = false;
                let mut p8 = false;
                let mut seen: FxHashSet<Access> = FxHashSet::default();
                let blocks: FxHashSet<BasicBlock> =
                    at.keys().chain(recursive_at.keys()).copied().collect();
                for block in &blocks {
                    if !everywhere && live_at[block].is_disjoint(&derived) {
                        continue;
                    }
                    let own = at.get(block).into_iter().flatten().map(|a| (a, true));
                    let other = recursive_at
                        .get(block)
                        .into_iter()
                        .flatten()
                        .map(|a| (a, false));
                    for (a, own) in own.chain(other) {
                        if (own && a.at.0 == f && family.contains(&a.by))
                            || !raw_via(a.via)
                            || !(a.write || (mutable && on(Rule::MutRead)))
                            || !seen.insert(*a)
                        {
                            continue;
                        }
                        let pointee = body.local_decls[local].ty.builtin_deref(true);
                        if !relation.meets(&objs, pointee, a) {
                            p8 |= !relation.options.by_types
                                && relation.meets_without_p8(&objs, a.obj);
                            continue;
                        }
                        if unknown_hold(&objs, a) {
                            unknowns = true;
                            // era-5c 145 H1: (E) keeps an evident shape all the same.
                            if relation.options.evident && on(Rule::EvidentUnknown) {
                                holds.push(top_shape(hold_of(a, &mut line_of), &objs, a));
                            }
                        } else {
                            holds.push(hold_of(a, &mut line_of));
                        }
                    }
                }
                let verdict =
                    Self::finish(&relation.options, holds, unknowns || unknown.contains(&f));
                // P8's receipt: Clear only because of the premise.
                if p8 && verdict == Verdict::Clear {
                    premised.insert((f, local));
                }
                verdicts.insert((f, local), verdict);
            }
        }
        let mut container_of: Vec<_> = relation.container_of.iter().copied().collect();
        container_of.sort_by_key(|&(f, local)| (f.local_def_index, local));
        RetainedAccessCheck {
            verdicts,
            bodies,
            container_of,
            premised,
        }
    }

    /// (E): only the evident shapes hold, and nothing is Unknown.
    fn finish(options: &Options, mut holds: Vec<Hold>, unknown: bool) -> Verdict {
        if options.evident {
            holds.retain(|h| {
                h.kind == HoldKind::DerivedStore || matches!(h.shape, Shape::SelfRef | Shape::Cycle)
            });
            return Self::verdict(holds, false);
        }
        Self::verdict(holds, unknown)
    }

    fn verdict(mut holds: Vec<Hold>, unknown: bool) -> Verdict {
        if holds.is_empty() {
            return if unknown {
                Verdict::Unknown
            } else {
                Verdict::Clear
            };
        }
        holds.sort();
        holds.dedup();
        Verdict::Held(holds)
    }

    /// The verdict of formal `index` (1-based, as `Local`) of `f`; `None` for a
    /// parameter that is not a raw pointer.
    pub(crate) fn formal(&self, f: LocalDefId, index: usize) -> Option<&Verdict> {
        self.verdicts.get(&(f, Local::from_usize(index)))
    }

    /// The verdict of local `local` of `f`'s `mir_drops_elaborated_and_const_checked`
    /// body; `None` for a local that is not a raw pointer.
    pub(crate) fn local(&self, f: LocalDefId, local: Local) -> Option<&Verdict> {
        self.verdicts.get(&(f, local))
    }

    /// Assert that `body` is the body the check read for `f`.
    pub(crate) fn assert_body(&self, f: LocalDefId, body: &Body<'_>) {
        assert_eq!(
            self.bodies.get(&f).copied(),
            Some(body_identity(body)),
            "the retained-access check read another body of {f:?}"
        );
    }

    /// Every verdict, for the receipt tables.
    pub(crate) fn verdicts(&self) -> impl Iterator<Item = (&(LocalDefId, Local), &Verdict)> {
        self.verdicts.iter()
    }

    /// `premise=outside-byte-view` for a subject Clear only under P8.
    pub(crate) fn premise(&self, f: LocalDefId, local: Local) -> Option<&'static str> {
        self.premised
            .contains(&(f, local))
            .then_some("premise=outside-byte-view")
    }

    pub(crate) fn container_of_sites(&self) -> &[(LocalDefId, Local)] {
        &self.container_of
    }
}
