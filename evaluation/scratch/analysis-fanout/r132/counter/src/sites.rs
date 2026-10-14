//! sites — analysis-fanout r132 (relay 132): the RAW-TO-SAFE CONVERSION SITES of one crate (`--sites`).
//!
//! A site is a place in the program's own code where a safe pointer value (a reference, an `Option` of one, a slice
//! reference, a `Box` / `Box<[T]>`) is produced from a raw pointer. The rules, the MIR reasoning and the toy's expected
//! rows are in r132/DESIGN.md; this header defines the columns of `sites.tsv`.
//!
//! MIR: `mir_promoted` of every fn / method / closure body (`hir_body_owners`), cloned before borrowck steals it, the
//! same phase as T2's `full_*` columns. Not optimized MIR: there `ReferencePropagation` folds c2rust's
//! `&mut *p as *mut T` (`_t = &mut (*_p); _r = &raw mut (*_t)`) into `_r = &raw mut (*_p)` and deletes the reference,
//! so neither the site nor its exclusion would be visible. `mir_promoted` = `mir_built` + const promotion (a
//! dereference of a run-time pointer is never promoted) + `SimplifyCfg`; its `FakeRead(ForLet)` statements (removed only
//! after borrowck) are what tells a `let` from an assignment. Cleanup (unwind) blocks are skipped everywhere: a
//! drop-and-replace (`x = v` where x needs drop) assigns v in its unwind block too, which is not where v goes.
//!
//! columns:
//!   file, line, col   the site's span (the macro call site when the span is from an expansion), the file relative to
//!                     the crate root's directory
//!   fn                `def_path_str` of the body (a closure: `f::{closure#0}`)
//!   kind              a:ref | a:mut-ref        an `Rvalue::Ref` (fake borrows skipped) whose place holds a Deref whose
//!                                               base is a raw pointer (`&mut *p`, `&*p.offset(k)`, `&mut (*p).f`,
//!                                               `&mut *(*s).q`, `(*p).m()`'s autoref)
//!                     b:ptr-as_ref | b:ptr-as_mut | b:ptr-as_uninit_* | b:ptr-as_ref_unchecked | b:ptr-as_mut_unchecked
//!                     b:box-from_raw | b:box-from_raw_in | b:box-from_non_null*
//!                     b:slice-from_raw_parts | b:slice-from_raw_parts_mut
//!                     b:nonnull-as_ref | b:nonnull-as_mut | b:nonnull-as_uninit_*
//!                     x:transmute (raw -> safe only) | x:cstr-from_ptr | x:vec-/string-from_raw_parts |
//!                     x:rc-/arc-from_raw | x:str-from_raw_parts        (outside the relay's list; reported, never
//!                                                                       counted with a / b)
//!                     h                        a call of a program-local WRAPPER: a function with a non-excluded
//!                                              site (any kind, h included) whose pointer is one of its own raw
//!                                              formals and whose value reaches its return place (directly or as a
//!                                              field of the returned struct); a fixpoint (a wrapper of a wrapper)
//!   call              the callee (b / x / h); `-` for a
//!   src_ty            the raw pointer's type (a: the base of the LAST raw Deref; b / x / h: the pointer argument)
//!   prod_ty           the produced value's type
//!   dest              where the safe value goes, following it through compiler temporaries (moves, reborrows,
//!                     `Some(..)`, a `Some` payload read, `Option::unwrap / expect / unwrap_unchecked`):
//!                     call-arg | decl | assign | return | field-store | other
//!                     (a temporary's `Drop` after its one moving use is not a use: mir_built drops aggregate / assignment
//!                     operand temporaries at scope end even when moved; only call arguments are unscheduled)
//!   dest_detail       call-arg: the callee; decl / assign: the variable; field-store: `Struct.field` (`@raw` when the
//!                     store goes through a raw pointer; `init:Struct.field>DEST` for a struct / enum / union literal and
//!                     where it goes; a union names its ACTIVE field); other: deref-use | drop | store-deref |
//!                     elem-store | `elem:tuple.N>DEST` / `elem:array>DEST` / `elem:array-repeat>DEST` /
//!                     `elem:closure-capture>DEST` (an element of a tuple / array / closure aggregate) | observed-only |
//!                     unused | multi-use:<uses> | ...
//!                     decl = a `let` write (the next non-trivial statement is `FakeRead(ForLet)`) or the single
//!                     definition of a binding that has an initializer / match place (`if let Some(r) = ..`,
//!                     `let ref mut fresh0 = ..`); `let r; r = ..` (no initializer) is assign
//!   formal_ty         call-arg: the callee's formal type (instantiated); `...` past a C variadic's formals
//!   formal_safe       safe | raw | generic | other | variadic (depth-0 form of the formal, T1's forms)
//!   via               the temporaries' steps, `>`-joined (reborrow, Some, match-some, unwrap, rawptr-of-deref,
//!                     method-to-raw:<name>, ...)
//!   excluded          yes when the safe value's only use, through temporaries, goes straight back to a raw pointer:
//!                     `&raw (*t)` (the `&T -> *T` coercion and the coercion cast), a `Cast` to a raw type, or the
//!                     receiver (argument 0) of a core / std / alloc METHOD `as_ptr / as_mut_ptr / as_ptr_range /
//!                     as_mut_ptr_range` whose result is raw (c2rust's `(*b).vals.as_mut_ptr()`); dest then describes
//!                     where the RAW value went
//!   excl_reason       rawptr-of-deref | rawptr-of-subplace | cast-to-raw | method-to-raw
//!   null_dom          a null test of the same pointer dominates the site: the non-null successor S of a `SwitchInt` on
//!                     `is_null(q)` / `q == null` / `q != null` / `discriminant(q.as_ref())` / `q.as_ref().is_some()` /
//!                     `.is_none()` has one predecessor and dominates the site's block, and q and the site's pointer
//!                     resolve (through temporaries, pointer casts, `cast()`, and `Option::as_ref / as_mut / as_deref /
//!                     as_deref_mut` + `unwrap / expect` of the same receiver place) to the same place:
//!                     yes            the place is equal AND its value is unchanged: no write of the root local on any
//!                                    path from the test's read to the site, and, when the place holds a Deref or the
//!                                    root's address is taken, no store through a Deref, no Drop, no inline asm and no
//!                                    call other than the pure std accessors (`pure_call`) on those paths; the site's
//!                                    own reads come after S
//!                     yes-place      the place is equal, the value proof fails (e.g. `p = (*p).next` on a loop path)
//!                     yes-base / yes-base-place   the same two, the site's pointer being an offset (`offset / add /
//!                                    sub / wrapping_* / byte_*`) of the tested place
//!                     no | n/a (a NonNull receiver)
//!   null_test         the dominating test: `is_null@LINE` | `eq-null@` | `ne-null@` | `opt-discr@` | `opt-is_some@` |
//!                     `opt-is_none@`
//!   raw_derefs        a: the number of raw-pointer Derefs in the place; b / x / h: 0
//!   post_raw_derefs   a: the number of non-raw Derefs AFTER the last raw Deref (`&mut *(*p).r` with r: &mut T, or
//!                     `&(*(*p).b).x` with b: Box<S>, = 1: a reborrow of a safe pointer LOADED through a raw one); 0
//!   in_wrapper        yes when THIS row makes its function a wrapper (not excluded, reaches the return place, pointer
//!                     = one of the function's raw formals); a wrapper's other rows say no
//!   macro             yes when the site's span comes from a macro expansion
//!
//! `sites-status.txt` (written by main.rs): `ok\t<rows>` or `panic\t<message>` (the pass runs under catch_unwind, so a
//! panic here never loses T1 / T2's output).

use std::{
    collections::{HashMap, HashSet},
    fmt::Write as _,
    path::Path,
};

use rustc_hir::def::DefKind;
use rustc_middle::{
    mir::{
        AggregateKind, BasicBlock, BinOp, BindingForm, Body, BorrowKind, CastKind, FakeReadCause, Local, LocalInfo,
        LocalKind, Location, Operand, Place, PlaceElem, PlaceRef, ProjectionElem, RETURN_PLACE, Rvalue, Statement,
        StatementKind, Terminator, TerminatorKind, UnOp, VarDebugInfoContents,
        visit::{PlaceContext, Visitor as MirVisitor},
    },
    ty::{self, Ty, TyCtxt},
};
use rustc_span::{
    FileName, Span,
    def_id::{DefId, LocalDefId},
    sym,
};

// ---------------------------------------------------------------------------------------------------------------
// bodies

/// Every fn / method / closure body's `mir_promoted`, cloned (call before `tcx.analysis`, which steals it).
pub fn clone_bodies<'tcx>(tcx: TyCtxt<'tcx>) -> Vec<(LocalDefId, Body<'tcx>)> {
    tcx.hir_body_owners()
        .filter(|&d| matches!(tcx.def_kind(d), DefKind::Fn | DefKind::AssocFn | DefKind::Closure))
        .map(|d| (d, tcx.mir_promoted(d).0.borrow().clone()))
        .collect()
}

// ---------------------------------------------------------------------------------------------------------------
// std callees

const OFFSET: &[&str] =
    &["offset", "add", "sub", "wrapping_offset", "wrapping_add", "wrapping_sub", "byte_offset", "byte_add", "byte_sub"];

enum Owner {
    /// an inherent method of `*const T` / `*mut T`
    Raw,
    /// an inherent method of the named ADT (`Box`, `NonNull`, `Option`, `Vec`, `CStr`, ...)
    Adt(String),
    /// a free function, by its `def_path_str`
    Free(String),
    Other,
}

/// A core / std / alloc function: its owner and its name.
fn std_fn(tcx: TyCtxt<'_>, def: DefId) -> Option<(Owner, String)> {
    if !matches!(tcx.crate_name(def.krate).as_str(), "core" | "std" | "alloc") {
        return None;
    }
    let name = tcx.opt_item_name(def)?.to_string();
    let owner = match tcx.impl_of_method(def) {
        Some(imp) => match tcx.type_of(imp).instantiate_identity().kind() {
            ty::RawPtr(..) => Owner::Raw,
            ty::Adt(a, _) => Owner::Adt(tcx.item_name(a.did()).to_string()),
            _ => Owner::Other,
        },
        None => Owner::Free(tcx.def_path_str(def)),
    };
    Some((owner, name))
}

/// The b / x kind of a callee, if it is one.
fn conv_kind(tcx: TyCtxt<'_>, def: DefId) -> Option<String> {
    let (owner, n) = std_fn(tcx, def)?;
    let n = n.as_str();
    match owner {
        Owner::Raw => matches!(
            n,
            "as_ref"
                | "as_mut"
                | "as_uninit_ref"
                | "as_uninit_mut"
                | "as_uninit_slice"
                | "as_uninit_slice_mut"
                | "as_ref_unchecked"
                | "as_mut_unchecked"
        )
        .then(|| format!("b:ptr-{n}")),
        Owner::Adt(a) => match (a.as_str(), n) {
            ("NonNull", "as_ref" | "as_mut" | "as_uninit_ref" | "as_uninit_mut" | "as_uninit_slice" | "as_uninit_slice_mut") => {
                Some(format!("b:nonnull-{n}"))
            }
            ("Box", "from_raw" | "from_raw_in" | "from_non_null" | "from_non_null_in") => Some(format!("b:box-{n}")),
            ("Vec" | "String", "from_raw_parts" | "from_raw_parts_in") => Some(format!("x:{}-{n}", a.to_lowercase())),
            ("Rc" | "Arc", "from_raw" | "from_raw_in") => Some(format!("x:{}-{n}", a.to_lowercase())),
            ("CStr", "from_ptr") => Some("x:cstr-from_ptr".into()),
            _ => None,
        },
        Owner::Free(path) => match n {
            "from_raw_parts" | "from_raw_parts_mut" if path.contains("slice") => Some(format!("b:slice-{n}")),
            "from_raw_parts" | "from_raw_parts_mut" if path.contains("str") => Some(format!("x:str-{n}")),
            "transmute" | "transmute_unchecked" => Some("x:transmute".into()),
            _ => None,
        },
        Owner::Other => None,
    }
}

/// `Option::unwrap / expect / unwrap_unchecked`: the safe value passes through to the call's destination.
fn passthrough(tcx: TyCtxt<'_>, def: DefId) -> bool {
    matches!(std_fn(tcx, def), Some((Owner::Adt(a), n))
        if a == "Option" && matches!(n.as_str(), "unwrap" | "expect" | "unwrap_unchecked"))
}

/// A core / std / alloc METHOD returning a raw pointer derived from its receiver (`<[T]>::as_mut_ptr`, `str::as_ptr`,
/// `Vec::as_mut_ptr`, `MaybeUninit::as_ptr`, `<[T]>::as_ptr_range`, ...): a reference whose only use is this receiver
/// goes straight back to raw (c2rust's `(*b).vals.as_mut_ptr()`, the method form of `&mut (*b).vals as *mut _`).
fn method_to_raw(tcx: TyCtxt<'_>, def: DefId) -> bool {
    tcx.impl_of_method(def).is_some()
        && matches!(std_fn(tcx, def), Some((_, n))
            if matches!(n.as_str(), "as_ptr" | "as_mut_ptr" | "as_ptr_range" | "as_mut_ptr_range"))
}

/// A raw pointer, or a `Range` of raw pointers (`as_ptr_range`).
fn returns_raw<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> bool {
    ty.is_raw_ptr()
        || matches!(ty.kind(), ty::Adt(a, args)
            if tcx.item_name(a.did()).as_str() == "Range" && args.types().next().is_some_and(|t| t.is_raw_ptr()))
}

/// A std call that writes no memory (the null-dominance value proof lets it pass between the test and the site): the
/// raw-pointer arithmetic / conversion methods, `Option`'s accessors and the conversions this pass counts.
fn pure_call(tcx: TyCtxt<'_>, func: &Operand<'_>) -> bool {
    let Some((def, _)) = func.const_fn_def() else { return false };
    let Some((owner, n)) = std_fn(tcx, def) else { return false };
    let n = n.as_str();
    match owner {
        Owner::Raw => {
            OFFSET.contains(&n)
                || matches!(
                    n,
                    "is_null"
                        | "cast"
                        | "cast_mut"
                        | "cast_const"
                        | "as_ref"
                        | "as_mut"
                        | "addr"
                        | "offset_from"
                        | "with_addr"
                        | "expose_provenance"
                )
        }
        Owner::Adt(a) => match a.as_str() {
            "Option" => matches!(
                n,
                "as_ref"
                    | "as_mut"
                    | "as_deref"
                    | "as_deref_mut"
                    | "unwrap"
                    | "expect"
                    | "unwrap_unchecked"
                    | "is_some"
                    | "is_none"
            ),
            "Box" => n == "from_raw",
            "NonNull" => matches!(n, "as_ref" | "as_mut" | "as_ptr" | "new_unchecked"),
            _ => false,
        },
        Owner::Free(path) => {
            (path.contains("ptr") && matches!(n, "null" | "null_mut"))
                || (path.contains("slice") && matches!(n, "from_raw_parts" | "from_raw_parts_mut"))
        }
        Owner::Other => matches!(n, "as_ptr" | "as_mut_ptr" | "len"),
    }
}

struct Callee<'tcx> {
    def: Option<DefId>,
    name: String,
    inputs: Vec<Ty<'tcx>>,
    variadic: bool,
}

fn callee_of<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>, func: &Operand<'tcx>) -> Callee<'tcx> {
    let fty = func.ty(body, tcx);
    match fty.kind() {
        ty::FnDef(def, args) => {
            let sig = tcx.fn_sig(*def).instantiate(tcx, *args).skip_binder();
            Callee { def: Some(*def), name: tcx.def_path_str(*def), inputs: sig.inputs().to_vec(), variadic: sig.c_variadic }
        }
        ty::FnPtr(sig_tys, _) => {
            let io = sig_tys.skip_binder().inputs_and_output;
            let n = io.len().saturating_sub(1);
            Callee { def: None, name: "<fn-ptr>".into(), inputs: io.iter().take(n).collect(), variadic: false }
        }
        _ => Callee { def: None, name: format!("<{fty}>"), inputs: Vec::new(), variadic: false },
    }
}

/// The depth-0 form of a type in T1's vocabulary: safe | raw | generic | other.
fn safety<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> &'static str {
    let mut layers = Vec::new();
    crate::walk(tcx, ty, 0, "-", &mut layers);
    match layers.iter().find(|l| l.depth == 0 && l.ctx == "-") {
        Some(l) if l.form.contains("raw") || l.form.contains("nonnull") => "raw",
        Some(_) => "safe",
        None if matches!(ty.kind(), ty::Param(_)) => "generic",
        None => "other",
    }
}

// ---------------------------------------------------------------------------------------------------------------
// the use index: how each local's value is used

#[derive(Clone)]
enum Use<'tcx> {
    /// `dst = copy/move t` (also `CopyForDeref`, an unsizing pointer coercion)
    Move(Place<'tcx>, Location),
    /// `dst = &(mut) (*t)`
    Reborrow(Place<'tcx>, Location),
    /// `dst = Option::Some(.., t, ..)`
    Wrap(Place<'tcx>, Location, String),
    /// `dst = move (t as Some).0`
    Unwrap(Place<'tcx>, Location),
    /// `dst = Struct { .., f: t, .. }` (`false`), or an element of a tuple / array / closure aggregate (`true`)
    FieldInit(Place<'tcx>, Location, String, bool),
    /// `dst = &raw (*t)` / `dst = t as *T`: straight back to a raw pointer
    ToRaw(Place<'tcx>, Location, &'static str),
    /// argument `idx` of the call terminating the block at `Location`
    Arg(Location, usize),
    Drop,
    DerefUse(&'static str),
    Other(&'static str),
    /// a read that does not move the value on (a discriminant, a shared borrow of the whole temporary, a switch)
    Observe,
}

impl Use<'_> {
    fn tag(&self) -> &'static str {
        match self {
            Use::Move(..) => "move",
            Use::Reborrow(..) => "reborrow",
            Use::Wrap(..) => "wrap",
            Use::Unwrap(..) => "unwrap",
            Use::FieldInit(..) => "field-init",
            Use::ToRaw(..) => "to-raw",
            Use::Arg(..) => "call-arg",
            Use::Drop => "drop",
            Use::DerefUse(_) => "deref-use",
            Use::Other(w) => *w,
            Use::Observe => "observe",
        }
    }

    /// The use moves the value out. After it, a `Drop` of the temporary is a no-op (drop elaboration removes it later),
    /// so the chase does not count that `Drop` as a second use.
    fn moves(&self) -> bool {
        matches!(self, Use::Move(..) | Use::Wrap(..) | Use::Unwrap(..) | Use::FieldInit(..) | Use::Arg(..))
    }
}

type Uses<'tcx> = HashMap<Local, Vec<Use<'tcx>>>;

fn add<'tcx>(m: &mut Uses<'tcx>, l: Local, u: Use<'tcx>) {
    m.entry(l).or_default().push(u);
}

/// A read of `p`: `whole` when `p` is the bare local; a Deref-first projection uses the pointee; a `Some` payload
/// read is `unwrap` where offered.
fn read<'tcx>(m: &mut Uses<'tcx>, p: Place<'tcx>, whole: Use<'tcx>, unwrap: Option<Use<'tcx>>) {
    let proj = &p.projection[..];
    let u = if proj.is_empty() {
        whole
    } else if matches!(proj[0], ProjectionElem::Deref) {
        Use::DerefUse("deref-use")
    } else if proj.len() == 2
        && matches!(proj[0], ProjectionElem::Downcast(_, v) if v.as_usize() == 1)
        && matches!(proj[1], ProjectionElem::Field(f, _) if f.as_usize() == 0)
    {
        unwrap.unwrap_or(Use::Other("payload"))
    } else {
        Use::Other("projection")
    };
    add(m, p.local, u);
}

fn op<'tcx>(m: &mut Uses<'tcx>, o: &Operand<'tcx>, whole: Use<'tcx>, unwrap: Option<Use<'tcx>>) {
    if let Some(p) = o.place() {
        read(m, p, whole, unwrap);
    }
}

struct Collect<'a, 'tcx> {
    out: &'a mut Vec<Place<'tcx>>,
}

impl<'tcx> MirVisitor<'tcx> for Collect<'_, 'tcx> {
    fn visit_place(&mut self, place: &Place<'tcx>, _: PlaceContext, _: Location) {
        self.out.push(*place);
    }
}

fn rvalue_uses<'tcx>(tcx: TyCtxt<'tcx>, m: &mut Uses<'tcx>, lhs: Place<'tcx>, rv: &Rvalue<'tcx>, loc: Location) {
    match rv {
        Rvalue::Use(o) => op(m, o, Use::Move(lhs, loc), Some(Use::Unwrap(lhs, loc))),
        Rvalue::Repeat(o, _) => op(m, o, Use::FieldInit(lhs, loc, "array-repeat".into(), true), None),
        Rvalue::Ref(_, bk, p) => {
            let proj = &p.projection[..];
            let u = if proj.is_empty() {
                if matches!(bk, BorrowKind::Shared | BorrowKind::Fake(_)) {
                    Use::Observe
                } else {
                    Use::Other("mut-borrow-of-value")
                }
            } else if matches!(proj[0], ProjectionElem::Deref) {
                if matches!(bk, BorrowKind::Fake(_)) {
                    Use::Observe
                } else if proj.len() == 1 {
                    Use::Reborrow(lhs, loc)
                } else {
                    Use::DerefUse("subplace-borrow")
                }
            } else {
                Use::Other("projection-borrow")
            };
            add(m, p.local, u);
        }
        Rvalue::RawPtr(_, p) => {
            let proj = &p.projection[..];
            let u = if proj.is_empty() {
                Use::Other("rawptr-of-value")
            } else if matches!(proj[0], ProjectionElem::Deref) {
                Use::ToRaw(lhs, loc, if proj.len() == 1 { "rawptr-of-deref" } else { "rawptr-of-subplace" })
            } else {
                Use::Other("rawptr-of-projection")
            };
            add(m, p.local, u);
        }
        Rvalue::Cast(kind, o, ty) => {
            let whole = if ty.is_raw_ptr() {
                Use::ToRaw(lhs, loc, "cast-to-raw")
            } else if matches!(kind, CastKind::PointerCoercion(..)) {
                Use::Move(lhs, loc)
            } else {
                Use::Other("cast")
            };
            op(m, o, whole, None);
        }
        Rvalue::BinaryOp(_, ab) => {
            op(m, &ab.0, Use::Other("binop"), None);
            op(m, &ab.1, Use::Other("binop"), None);
        }
        Rvalue::UnaryOp(_, o) => op(m, o, Use::Other("unop"), None),
        Rvalue::Discriminant(p) => read(m, *p, Use::Observe, None),
        Rvalue::CopyForDeref(p) => read(m, *p, Use::Move(lhs, loc), None),
        Rvalue::Aggregate(k, ops) => {
            for (i, o) in ops.iter().enumerate() {
                let whole = match &**k {
                    AggregateKind::Adt(did, v, _, _, active) => {
                        if tcx.is_diagnostic_item(sym::Option, *did) && v.as_usize() == 1 {
                            Use::Wrap(lhs, loc, "Some".into())
                        } else {
                            // a union literal has one operand, for its ACTIVE field (mir/syntax.rs:1552)
                            let fi = active.map(|f| f.as_usize()).unwrap_or(i);
                            let f = tcx
                                .adt_def(*did)
                                .variant(*v)
                                .fields
                                .iter()
                                .nth(fi)
                                .map(|f| f.name.to_string())
                                .unwrap_or_else(|| fi.to_string());
                            Use::FieldInit(lhs, loc, format!("{}.{f}", tcx.item_name(*did)), false)
                        }
                    }
                    AggregateKind::Tuple => Use::FieldInit(lhs, loc, format!("tuple.{i}"), true),
                    AggregateKind::Array(_) => Use::FieldInit(lhs, loc, "array".into(), true),
                    AggregateKind::Closure(..) => Use::FieldInit(lhs, loc, "closure-capture".into(), true),
                    _ => Use::Other("aggregate"),
                };
                op(m, o, whole, None);
            }
        }
        _ => {
            let mut ps = Vec::new();
            Collect { out: &mut ps }.visit_rvalue(rv, loc);
            for p in ps {
                read(m, p, Use::Other("rvalue"), None);
            }
        }
    }
}

fn index_uses<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> Uses<'tcx> {
    let mut m: Uses<'tcx> = HashMap::new();
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        // the unwind paths are not where a value goes: a drop-and-replace assigns its value in both
        if data.is_cleanup {
            continue;
        }
        for (i, st) in data.statements.iter().enumerate() {
            let loc = Location { block: bb, statement_index: i };
            match &st.kind {
                StatementKind::Assign(b) => {
                    let (lhs, rv) = &**b;
                    if !lhs.projection.is_empty() && matches!(lhs.projection[0], ProjectionElem::Deref) {
                        add(&mut m, lhs.local, Use::DerefUse("store-through"));
                    }
                    rvalue_uses(tcx, &mut m, *lhs, rv, loc);
                }
                StatementKind::FakeRead(..)
                | StatementKind::PlaceMention(..)
                | StatementKind::AscribeUserType(..)
                | StatementKind::StorageLive(_)
                | StatementKind::StorageDead(_)
                | StatementKind::Retag(..)
                | StatementKind::Coverage(..)
                | StatementKind::BackwardIncompatibleDropHint { .. }
                | StatementKind::Nop => {}
                _ => {
                    let mut ps = Vec::new();
                    Collect { out: &mut ps }.visit_statement(st, loc);
                    for p in ps {
                        add(&mut m, p.local, Use::Other("statement"));
                    }
                }
            }
        }
        let loc = Location { block: bb, statement_index: data.statements.len() };
        let term = data.terminator();
        match &term.kind {
            TerminatorKind::Call { func, args, .. } | TerminatorKind::TailCall { func, args, .. } => {
                if let Some(p) = func.place() {
                    add(&mut m, p.local, Use::Other("callee"));
                }
                for (i, a) in args.iter().enumerate() {
                    if let Some(p) = a.node.place() {
                        read(&mut m, p, Use::Arg(loc, i), None);
                    }
                }
            }
            TerminatorKind::Drop { place, .. } => {
                let u = if place.projection.is_empty() {
                    Use::Drop
                } else if matches!(place.projection[0], ProjectionElem::Deref) {
                    Use::DerefUse("drop-pointee")
                } else {
                    Use::Other("drop-part")
                };
                add(&mut m, place.local, u);
            }
            TerminatorKind::SwitchInt { discr, .. } => {
                if let Some(p) = discr.place() {
                    add(&mut m, p.local, Use::Observe);
                }
            }
            TerminatorKind::Assert { cond, .. } => {
                if let Some(p) = cond.place() {
                    add(&mut m, p.local, Use::Observe);
                }
            }
            _ => {
                let mut ps = Vec::new();
                Collect { out: &mut ps }.visit_terminator(term, loc);
                for p in ps {
                    if p.local != RETURN_PLACE {
                        add(&mut m, p.local, Use::Other("terminator"));
                    }
                }
            }
        }
    }
    m
}

// ---------------------------------------------------------------------------------------------------------------
// the per-body context

#[derive(Clone, Copy)]
enum Def {
    Stmt(Location),
    Call(Location),
}

#[derive(Clone, Copy)]
enum WLoc {
    /// the value was written by the statement at this location
    Stmt(Location),
    /// the value was written by a call returning to this block
    Call(Option<BasicBlock>),
}

enum NN {
    /// non-null when the switched bool equals this
    Bool(bool),
    /// non-null on this discriminant value (`Some` = 1)
    Discr(u128),
}

/// One step of a canonical place: a MIR projection, or the payload of an `Option` reached through an accessor chain.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Step<'tcx> {
    P(PlaceElem<'tcx>),
    /// `(*Option::unwrap(Option::as_ref(&o)))` = o's `Some` payload (`as_mut` likewise; `as_deref(_mut)` adds a `Deref`)
    Payload,
}

/// A pointer value resolved to the place it was read from.
struct Canon<'tcx> {
    local: Local,
    proj: Vec<Step<'tcx>>,
    /// the value is an `offset`-family result of the place (`yes-base`)
    offset: bool,
    /// the definitions walked, in walking order (the last one is the earliest read of the place)
    chain: Vec<Location>,
}

struct Fact<'tcx> {
    s: BasicBlock,
    local: Local,
    proj: Vec<Step<'tcx>>,
    kind: &'static str,
    line: usize,
    /// where the tested place was read (the start of the value proof)
    from: Location,
}

#[derive(Default, Clone)]
struct Dest {
    dest: String,
    detail: String,
    formal_ty: String,
    formal_safe: String,
    via: Vec<String>,
    excluded: Option<&'static str>,
    /// the value reaches the return place (directly, or as a field / element of the returned aggregate)
    ret: bool,
}

struct SiteRow {
    span: Span,
    kind: String,
    call: String,
    src_ty: String,
    prod_ty: String,
    raw_derefs: usize,
    post_raw_derefs: usize,
    dest: Dest,
    null_dom: String,
    null_test: String,
    /// the pointer resolves to raw formal number `i` of the body (for the wrapper rule)
    src_arg: Option<usize>,
}

struct Cx<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    did: LocalDefId,
    body: &'a Body<'tcx>,
    uses: Uses<'tcx>,
    defs: HashMap<Local, Vec<Def>>,
    names: HashMap<Local, String>,
    /// locals whose own storage is borrowed (a `Ref` / `RawPtr` of a place rooted at it with no Deref)
    addr_taken: HashSet<Local>,
    facts: Vec<Fact<'tcx>>,
}

fn esc(s: &str) -> String {
    s.replace(['\t', '\n', '\r'], " ")
}

fn line_of(tcx: TyCtxt<'_>, sp: Span) -> usize {
    let sp = if sp.from_expansion() { sp.source_callsite() } else { sp };
    tcx.sess.source_map().lookup_char_pos(sp.lo()).line
}

fn short(path: &str) -> String {
    path.rsplit("::").next().unwrap_or(path).to_owned()
}

fn has_deref(p: &Place<'_>) -> bool {
    p.projection.iter().any(|e| matches!(e, ProjectionElem::Deref))
}

impl<'a, 'tcx> Cx<'a, 'tcx> {
    fn new(tcx: TyCtxt<'tcx>, did: LocalDefId, body: &'a Body<'tcx>) -> Self {
        let uses = index_uses(tcx, body);
        let mut defs: HashMap<Local, Vec<Def>> = HashMap::new();
        let mut addr_taken = HashSet::new();
        for (bb, data) in body.basic_blocks.iter_enumerated() {
            if data.is_cleanup {
                continue;
            }
            for (i, st) in data.statements.iter().enumerate() {
                if let StatementKind::Assign(b) = &st.kind {
                    if b.0.projection.is_empty() {
                        defs.entry(b.0.local).or_default().push(Def::Stmt(Location { block: bb, statement_index: i }));
                    }
                    match &b.1 {
                        Rvalue::Ref(_, bk, p) if !matches!(bk, BorrowKind::Fake(_)) && !has_deref(p) => {
                            addr_taken.insert(p.local);
                        }
                        Rvalue::RawPtr(_, p) if !has_deref(p) => {
                            addr_taken.insert(p.local);
                        }
                        _ => {}
                    }
                }
            }
            if let TerminatorKind::Call { destination, .. } = &data.terminator().kind
                && destination.projection.is_empty()
            {
                let loc = Location { block: bb, statement_index: data.statements.len() };
                defs.entry(destination.local).or_default().push(Def::Call(loc));
            }
        }
        let mut names = HashMap::new();
        for info in &body.var_debug_info {
            if let VarDebugInfoContents::Place(p) = &info.value
                && let Some(l) = p.as_local()
            {
                names.entry(l).or_insert_with(|| info.name.to_string());
            }
        }
        let mut cx = Cx { tcx, did, body, uses, defs, names, addr_taken, facts: Vec::new() };
        cx.facts = cx.null_facts();
        cx
    }

    fn stmt(&self, loc: Location) -> &'a Statement<'tcx> {
        &self.body.basic_blocks[loc.block].statements[loc.statement_index]
    }

    fn single_def(&self, l: Local) -> Option<Def> {
        match self.defs.get(&l).map(Vec::as_slice) {
            Some([d]) => Some(*d),
            _ => None,
        }
    }

    fn is_temp(&self, l: Local) -> bool {
        matches!(self.body.local_kind(l), LocalKind::Temp) && !self.body.local_decls[l].is_user_variable()
    }

    fn name(&self, l: Local) -> String {
        self.names.get(&l).cloned().unwrap_or_else(|| format!("_{}", l.as_usize()))
    }

    /// A user binding with an initializer or a match place (`let x = ..`, `if let Some(x) = ..`, `let ref mut x = ..`);
    /// false for `let x;` (builder/block.rs:283 passes `None`) and for a guard's `if let` (matches/mod.rs:801).
    fn bound_with_place(&self, l: Local) -> bool {
        matches!(self.body.local_decls[l].local_info(), LocalInfo::User(BindingForm::Var(v)) if v.opt_match_place.is_some())
    }

    /// The core / std / alloc callee and first argument of the call terminating `loc.block`.
    fn call_at(&self, loc: Location) -> Option<(DefId, Option<Place<'tcx>>)> {
        let TerminatorKind::Call { func, args, .. } = &self.body.basic_blocks[loc.block].terminator().kind else {
            return None;
        };
        let (def, _) = func.const_fn_def()?;
        Some((def, args.first().and_then(|a| a.node.place())))
    }

    // ----- pointer identity

    /// `l = Option::unwrap / expect / unwrap_unchecked(t1)`, `t1 = Option::as_ref / as_mut / as_deref / as_deref_mut(t2)`,
    /// `t2 = &(mut) base`: (base, whether the accessor dereferences the payload, the three definitions).
    /// CROWN's `(*node.as_deref().unwrap()).nw` and `(*node.as_deref_mut().unwrap()).nw` are then the same place.
    fn accessor(&self, l: Local) -> Option<(Place<'tcx>, bool, [Location; 3])> {
        let Def::Call(l1) = self.single_def(l)? else { return None };
        let (d1, a1) = self.call_at(l1)?;
        match std_fn(self.tcx, d1)? {
            (Owner::Adt(a), n) if a == "Option" && matches!(n.as_str(), "unwrap" | "expect" | "unwrap_unchecked") => {}
            _ => return None,
        }
        let t1 = a1?;
        if !t1.projection.is_empty() || !self.is_temp(t1.local) {
            return None;
        }
        let Def::Call(l2) = self.single_def(t1.local)? else { return None };
        let (d2, a2) = self.call_at(l2)?;
        let deref = match std_fn(self.tcx, d2)? {
            (Owner::Adt(a), n) if a == "Option" => match n.as_str() {
                "as_deref" | "as_deref_mut" => true,
                "as_ref" | "as_mut" => false,
                _ => return None,
            },
            _ => return None,
        };
        let t2 = a2?;
        if !t2.projection.is_empty() || !self.is_temp(t2.local) {
            return None;
        }
        let Def::Stmt(l3) = self.single_def(t2.local)? else { return None };
        let StatementKind::Assign(b) = &self.stmt(l3).kind else { return None };
        match &b.1 {
            Rvalue::Ref(_, bk, base) if !matches!(bk, BorrowKind::Fake(_)) => Some((*base, deref, [l1, l2, l3])),
            _ => None,
        }
    }

    /// The place a pointer value comes from: through single-definition temporaries, `Use`, pointer casts,
    /// `CopyForDeref`, `cast / cast_mut / cast_const`, and (for a `Deref` of an accessor result) the `Option`
    /// accessor chain of `accessor`; `offset`-family calls are followed and reported (`offset`).
    fn canon(&self, local: Local, proj: &[PlaceElem<'tcx>]) -> Canon<'tcx> {
        let mut c = Canon { local, proj: proj.iter().map(|e| Step::P(*e)).collect(), offset: false, chain: Vec::new() };
        for _ in 0..16 {
            if !self.is_temp(c.local) {
                break;
            }
            if !c.proj.is_empty() {
                if !matches!(c.proj[0], Step::P(ProjectionElem::Deref)) {
                    break;
                }
                let Some((base, deref, locs)) = self.accessor(c.local) else { break };
                let mut p: Vec<Step<'tcx>> = base.projection.iter().map(Step::P).collect();
                p.push(Step::Payload);
                if deref {
                    p.push(Step::P(ProjectionElem::Deref));
                }
                p.extend_from_slice(&c.proj[1..]);
                c.local = base.local;
                c.proj = p;
                c.chain.extend(locs);
                continue;
            }
            let Some(d) = self.single_def(c.local) else { break };
            let next = match d {
                Def::Stmt(loc) => {
                    let StatementKind::Assign(b) = &self.stmt(loc).kind else { break };
                    let q = match &b.1 {
                        Rvalue::Use(o) | Rvalue::Cast(CastKind::PtrToPtr | CastKind::PointerCoercion(..), o, _) => {
                            match o.place() {
                                Some(q) => q,
                                None => break,
                            }
                        }
                        Rvalue::CopyForDeref(q) => *q,
                        _ => break,
                    };
                    c.chain.push(loc);
                    q
                }
                Def::Call(loc) => {
                    let Some((def, a0)) = self.call_at(loc) else { break };
                    match std_fn(self.tcx, def) {
                        Some((Owner::Raw, n)) if OFFSET.contains(&n.as_str()) => c.offset = true,
                        Some((Owner::Raw, n)) if matches!(n.as_str(), "cast" | "cast_mut" | "cast_const") => {}
                        _ => break,
                    }
                    let Some(q) = a0 else { break };
                    c.chain.push(loc);
                    q
                }
            };
            c.local = next.local;
            c.proj = next.projection.iter().map(Step::P).collect();
        }
        c
    }

    // ----- null tests

    fn is_null_op(&self, o: &Operand<'tcx>, depth: usize) -> bool {
        if depth > 8 {
            return false;
        }
        match o {
            Operand::Constant(c) => c.const_.try_to_scalar_int().is_some_and(|s| s.is_null()),
            Operand::Copy(p) | Operand::Move(p) => {
                if !p.projection.is_empty() {
                    return false;
                }
                match self.single_def(p.local) {
                    Some(Def::Stmt(loc)) => match &self.stmt(loc).kind {
                        StatementKind::Assign(b) => match &b.1 {
                            Rvalue::Use(i) | Rvalue::Cast(_, i, _) => self.is_null_op(i, depth + 1),
                            _ => false,
                        },
                        _ => false,
                    },
                    Some(Def::Call(loc)) => match self.call_at(loc).and_then(|(d, _)| std_fn(self.tcx, d)) {
                        Some((Owner::Free(path), n)) => path.contains("ptr") && (n == "null" || n == "null_mut"),
                        _ => false,
                    },
                    None => false,
                }
            }
        }
    }

    /// `l` defined by `q.as_ref()` / `q.as_mut()`: q and the call's location.
    fn option_source(&self, l: Local) -> Option<(Place<'tcx>, Location)> {
        let Def::Call(loc) = self.single_def(l)? else { return None };
        let (def, a0) = self.call_at(loc)?;
        match std_fn(self.tcx, def)? {
            (Owner::Raw, n) if n == "as_ref" || n == "as_mut" => Some((a0?, loc)),
            _ => None,
        }
    }

    /// `l = &t` (a borrow of a whole local): t.
    fn ref_target(&self, l: Local) -> Option<Local> {
        let Def::Stmt(loc) = self.single_def(l)? else { return None };
        let StatementKind::Assign(b) = &self.stmt(loc).kind else { return None };
        match &b.1 {
            Rvalue::Ref(_, _, p) if p.projection.is_empty() => Some(p.local),
            _ => None,
        }
    }

    /// The bool / discriminant local `l` as a null test: the tested pointer, the test's kind, the non-null outcome and
    /// the location that consumes the tested pointer.
    fn test_of(&self, l: Local, neg: bool, depth: usize) -> Option<(Place<'tcx>, &'static str, NN, Location)> {
        if depth > 8 {
            return None;
        }
        match self.single_def(l)? {
            Def::Stmt(loc) => {
                let StatementKind::Assign(b) = &self.stmt(loc).kind else { return None };
                match &b.1 {
                    Rvalue::UnaryOp(UnOp::Not, o) => {
                        let p = o.place()?;
                        if !p.projection.is_empty() {
                            return None;
                        }
                        self.test_of(p.local, !neg, depth + 1)
                    }
                    Rvalue::Use(o) => {
                        let p = o.place()?;
                        if !p.projection.is_empty() {
                            return None;
                        }
                        self.test_of(p.local, neg, depth + 1)
                    }
                    Rvalue::BinaryOp(bop, ab) if matches!(bop, BinOp::Eq | BinOp::Ne) => {
                        let (a, c) = (&ab.0, &ab.1);
                        let ptr = if self.is_null_op(c, 0) {
                            a
                        } else if self.is_null_op(a, 0) {
                            c
                        } else {
                            return None;
                        };
                        if !ptr.ty(self.body, self.tcx).is_raw_ptr() {
                            return None;
                        }
                        let eq = matches!(bop, BinOp::Eq);
                        // `q == null` is non-null when false; `q != null` when true
                        Some((ptr.place()?, if eq { "eq-null" } else { "ne-null" }, NN::Bool(!eq ^ neg), loc))
                    }
                    Rvalue::Discriminant(p) => {
                        if neg || !p.projection.is_empty() {
                            return None;
                        }
                        let (q, at) = self.option_source(p.local)?;
                        Some((q, "opt-discr", NN::Discr(1), at))
                    }
                    _ => None,
                }
            }
            Def::Call(loc) => {
                let (def, a0) = self.call_at(loc)?;
                let (owner, n) = std_fn(self.tcx, def)?;
                match (owner, n.as_str()) {
                    // `q.is_null()` is non-null when false
                    (Owner::Raw, "is_null") => Some((a0?, "is_null", NN::Bool(neg), loc)),
                    (Owner::Adt(a), "is_some" | "is_none") if a == "Option" => {
                        let r = a0?;
                        if !r.projection.is_empty() {
                            return None;
                        }
                        let opt = self.ref_target(r.local)?;
                        let some = n == "is_some";
                        let (q, at) = self.option_source(opt)?;
                        Some((q, if some { "opt-is_some" } else { "opt-is_none" }, NN::Bool(some ^ neg), at))
                    }
                    _ => None,
                }
            }
        }
    }

    /// Every null test's non-null successor S (with one predecessor), keyed by the tested pointer's place.
    fn null_facts(&self) -> Vec<Fact<'tcx>> {
        let mut out = Vec::new();
        let preds = self.body.basic_blocks.predecessors();
        for (bb, data) in self.body.basic_blocks.iter_enumerated() {
            if data.is_cleanup {
                continue;
            }
            let term = data.terminator();
            let TerminatorKind::SwitchInt { discr, targets } = &term.kind else { continue };
            let Some(p) = discr.place() else { continue };
            if !p.projection.is_empty() {
                continue;
            }
            let Some((ptr, kind, nn, at)) = self.test_of(p.local, false, 0) else { continue };
            let want: u128 = match nn {
                NN::Bool(b) => b as u128,
                NN::Discr(v) => v,
            };
            let s = targets.iter().find(|(v, _)| *v == want).map(|(_, t)| t).unwrap_or_else(|| targets.otherwise());
            if preds[s].len() != 1 {
                continue;
            }
            let c = self.canon(ptr.local, &ptr.projection[..]);
            let from = c.chain.last().copied().unwrap_or(at);
            out.push(Fact { s, local: c.local, proj: c.proj, kind, line: line_of(self.tcx, term.source_info.span), from });
        }
        out
    }

    /// null_dom, null_test and the raw-formal index of a site's pointer (`at`: the site's statement or call).
    fn null_info(&self, at: Location, local: Local, proj: &[PlaceElem<'tcx>]) -> (String, String, Option<usize>) {
        let c = self.canon(local, proj);
        let src_arg = (c.proj.is_empty()
            && matches!(self.body.local_kind(c.local), LocalKind::Arg)
            && self.body.local_decls[c.local].ty.is_raw_ptr())
        .then(|| c.local.as_usize() - 1);
        let dom = self.body.basic_blocks.dominators();
        // `dominates` asserts its second node is reachable (rustc_data_structures dominators/mod.rs:384)
        if !dom.is_reachable(at.block) {
            return ("no".into(), "-".into(), src_arg);
        }
        let strict = c.proj.iter().any(|s| matches!(s, Step::P(ProjectionElem::Deref))) || self.addr_taken.contains(&c.local);
        let mut place_only: Option<String> = None;
        for f in &self.facts {
            if f.local != c.local || f.proj != c.proj || !dom.dominates(f.s, at.block) {
                continue;
            }
            let test = format!("{}@{}", f.kind, f.line);
            // the value proof: the site's own reads come after the test passed, and nothing on a path from the test's
            // read to the site can change the place's value
            let after = c.chain.iter().all(|l| dom.is_reachable(l.block) && dom.dominates(f.s, l.block));
            if after && self.clear(f.from, at, c.local, strict) {
                return (if c.offset { "yes-base" } else { "yes" }.into(), test, src_arg);
            }
            place_only.get_or_insert(test);
        }
        match place_only {
            Some(t) => (if c.offset { "yes-base-place" } else { "yes-place" }.into(), t, src_arg),
            None => ("no".into(), "-".into(), src_arg),
        }
    }

    // ----- the value proof

    /// Blocks reachable from `start`'s successors (`forward`) or predecessors, never entering `barrier` (re-entering
    /// the test's block re-reads the pointer) or a cleanup block.
    fn reach(&self, start: BasicBlock, forward: bool, barrier: BasicBlock) -> HashSet<BasicBlock> {
        let bbs = &self.body.basic_blocks;
        let preds = bbs.predecessors();
        let next = |b: BasicBlock| -> Vec<BasicBlock> {
            if forward { bbs[b].terminator().successors().collect() } else { preds[b].to_vec() }
        };
        let mut seen = HashSet::new();
        let mut stack = next(start);
        while let Some(b) = stack.pop() {
            if b == barrier || bbs[b].is_cleanup || !seen.insert(b) {
                continue;
            }
            stack.extend(next(b));
        }
        seen
    }

    /// No statement or terminator on any path from just after `from` to just before `to` can change the value of the
    /// place rooted at `root` (`strict`: the place holds a Deref, or `root`'s address is taken).
    fn clear(&self, from: Location, to: Location, root: Local, strict: bool) -> bool {
        let end = |b: BasicBlock| self.body.basic_blocks[b].statements.len() + 1;
        if from.block == to.block {
            // a path leaving the block re-enters at its top and passes `from` again before `to`
            return from.statement_index < to.statement_index
                && self.seg_ok(from.block, from.statement_index + 1, to.statement_index, root, strict);
        }
        if !self.seg_ok(from.block, from.statement_index + 1, end(from.block), root, strict) {
            return false;
        }
        let fwd = self.reach(from.block, true, from.block);
        if !fwd.contains(&to.block) {
            return false;
        }
        let bwd = self.reach(to.block, false, from.block);
        for &b in fwd.intersection(&bwd) {
            if b != to.block && !self.seg_ok(b, 0, end(b), root, strict) {
                return false;
            }
        }
        if !self.seg_ok(to.block, 0, to.statement_index, root, strict) {
            return false;
        }
        // a cycle through the site's block that avoids the test: the rest of the block is on a path too
        !(self.reach(to.block, true, from.block).contains(&to.block)
            && !self.seg_ok(to.block, to.statement_index + 1, end(to.block), root, strict))
    }

    /// Statements `lo..hi` of block `b` (index `len` = the terminator) change nothing the place depends on.
    fn seg_ok(&self, b: BasicBlock, lo: usize, hi: usize, root: Local, strict: bool) -> bool {
        let data = &self.body.basic_blocks[b];
        let n = data.statements.len();
        if data.statements.iter().take(hi.min(n)).skip(lo).any(|st| self.kills_stmt(st, root, strict)) {
            return false;
        }
        !(lo <= n && n < hi && self.kills_term(data.terminator(), root, strict))
    }

    fn kills_place(&self, p: &Place<'tcx>, root: Local, strict: bool) -> bool {
        p.local == root || (strict && has_deref(p))
    }

    fn kills_stmt(&self, st: &Statement<'tcx>, root: Local, strict: bool) -> bool {
        match &st.kind {
            StatementKind::Assign(b) => self.kills_place(&b.0, root, strict),
            StatementKind::SetDiscriminant { place, .. } | StatementKind::Deinit(place) => {
                self.kills_place(place, root, strict)
            }
            StatementKind::StorageLive(l) | StatementKind::StorageDead(l) => *l == root,
            StatementKind::Intrinsic(_) => strict,
            _ => false,
        }
    }

    fn kills_term(&self, t: &Terminator<'tcx>, root: Local, strict: bool) -> bool {
        match &t.kind {
            TerminatorKind::Call { func, destination, .. } => {
                self.kills_place(destination, root, strict) || (strict && !pure_call(self.tcx, func))
            }
            TerminatorKind::Drop { place, .. } => place.local == root || strict,
            TerminatorKind::InlineAsm { .. } | TerminatorKind::Yield { .. } | TerminatorKind::TailCall { .. } => true,
            _ => false,
        }
    }

    // ----- destinations

    /// `l` (a user variable) written at `w` by a `let`: the next non-trivial statement is `FakeRead(ForLet, l)`.
    fn is_let_write(&self, l: Local, w: WLoc) -> bool {
        let (bb, start) = match w {
            WLoc::Stmt(loc) => (loc.block, loc.statement_index + 1),
            WLoc::Call(Some(t)) => (t, 0),
            WLoc::Call(None) => return false,
        };
        for st in self.body.basic_blocks[bb].statements.iter().skip(start) {
            match &st.kind {
                StatementKind::FakeRead(b) => {
                    let (cause, p) = &**b;
                    return matches!(cause, FakeReadCause::ForLet(_)) && p.local == l && p.projection.is_empty();
                }
                StatementKind::StorageLive(_)
                | StatementKind::StorageDead(_)
                | StatementKind::AscribeUserType(..)
                | StatementKind::PlaceMention(..)
                | StatementKind::Retag(..)
                | StatementKind::Coverage(..)
                | StatementKind::BackwardIncompatibleDropHint { .. }
                | StatementKind::Nop => continue,
                _ => return false,
            }
        }
        false
    }

    fn store_kind(&self, p: Place<'tcx>) -> (String, String) {
        let proj = &p.projection[..];
        let (mut field, mut deref, mut elem, mut raw) = (None, false, false, false);
        for (i, e) in proj.iter().enumerate() {
            let base = PlaceRef { local: p.local, projection: &proj[..i] }.ty(self.body, self.tcx);
            match e {
                ProjectionElem::Deref => {
                    deref = true;
                    raw |= base.ty.is_raw_ptr();
                }
                ProjectionElem::Field(f, _) => {
                    field = Some(match base.ty.kind() {
                        ty::Adt(adt, _) => {
                            let v = match base.variant_index {
                                Some(v) => adt.variant(v),
                                None if !adt.is_enum() => adt.non_enum_variant(),
                                None => continue,
                            };
                            let n = v.fields.iter().nth(f.as_usize()).map(|fd| fd.name.to_string());
                            format!("{}.{}", self.tcx.item_name(adt.did()), n.unwrap_or_else(|| f.as_usize().to_string()))
                        }
                        _ => format!("tuple.{}", f.as_usize()),
                    });
                }
                ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. } | ProjectionElem::Subslice { .. } => {
                    elem = true
                }
                _ => {}
            }
        }
        match field {
            Some(f) => ("field-store".into(), if raw { format!("{f}@raw") } else { f }),
            None if elem => ("other".into(), "elem-store".into()),
            None if deref => ("other".into(), "store-deref".into()),
            None => ("other".into(), "projection".into()),
        }
    }

    /// Follow the produced value from the place it was first written to.
    fn chase(&self, start: Place<'tcx>, w0: WLoc, depth: usize) -> Dest {
        let mut d = Dest::default();
        let (mut cur, mut w) = (start, w0);
        for _ in 0..64 {
            if !cur.projection.is_empty() {
                (d.dest, d.detail) = self.store_kind(cur);
                return d;
            }
            let l = cur.local;
            if l == RETURN_PLACE {
                d.dest = "return".into();
                d.ret = true;
                return d;
            }
            if matches!(self.body.local_kind(l), LocalKind::Arg) {
                d.dest = "assign".into();
                d.detail = self.name(l);
                return d;
            }
            if self.body.local_decls[l].is_user_variable() {
                let decl = self.is_let_write(l, w)
                    || (self.defs.get(&l).is_some_and(|v| v.len() == 1) && self.bound_with_place(l));
                d.dest = if decl { "decl" } else { "assign" }.into();
                d.detail = self.name(l);
                return d;
            }
            let all: &[Use<'tcx>] = self.uses.get(&l).map(Vec::as_slice).unwrap_or(&[]);
            let live: Vec<&Use<'tcx>> = all.iter().filter(|u| !matches!(u, Use::Observe)).collect();
            // mir_built drops an aggregate / assignment operand temporary at its scope's end even after moving it (only
            // call arguments are unscheduled, `record_operands_moved`, builder/scope.rs:1260; aggregates, into.rs:384-
            // 404, never call it); drop elaboration removes that Drop later. After one moving use it is not a use.
            let moved: Vec<&Use<'tcx>> = live.iter().copied().filter(|u| !matches!(u, Use::Drop)).collect();
            let live = if moved.len() == 1 && moved.len() < live.len() && moved[0].moves() { moved } else { live };
            if live.is_empty() {
                d.dest = "other".into();
                d.detail = if all.is_empty() { "unused" } else { "observed-only" }.into();
                return d;
            }
            if live.len() > 1 {
                d.dest = "other".into();
                d.detail = format!("multi-use:{}", live.iter().map(|u| u.tag()).collect::<Vec<_>>().join(","));
                return d;
            }
            match live[0] {
                Use::Move(dst, loc) => {
                    cur = *dst;
                    w = WLoc::Stmt(*loc);
                }
                Use::Reborrow(dst, loc) => {
                    d.via.push("reborrow".into());
                    cur = *dst;
                    w = WLoc::Stmt(*loc);
                }
                Use::Wrap(dst, loc, what) => {
                    d.via.push(what.clone());
                    cur = *dst;
                    w = WLoc::Stmt(*loc);
                }
                Use::Unwrap(dst, loc) => {
                    d.via.push("match-some".into());
                    cur = *dst;
                    w = WLoc::Stmt(*loc);
                }
                Use::ToRaw(dst, loc, reason) => {
                    // the reference goes straight back to a raw pointer: an exclusion; follow the raw value on
                    if d.excluded.is_none() {
                        d.excluded = Some(*reason);
                    }
                    d.via.push((*reason).into());
                    cur = *dst;
                    w = WLoc::Stmt(*loc);
                }
                Use::FieldInit(dst, loc, what, elem) => {
                    let inner = if depth < 4 {
                        self.chase(*dst, WLoc::Stmt(*loc), depth + 1)
                    } else {
                        Dest { dest: "other".into(), detail: "deep".into(), ..Dest::default() }
                    };
                    if *elem {
                        // an element of a tuple / array / closure aggregate is not a field store
                        d.dest = "other".into();
                        d.detail = format!("elem:{what}>{}", inner.dest);
                    } else {
                        d.dest = "field-store".into();
                        d.detail = format!("init:{what}>{}", inner.dest);
                    }
                    d.ret = inner.ret;
                    return d;
                }
                Use::Arg(loc, idx) => {
                    let term = self.body.basic_blocks[loc.block].terminator();
                    let (func, tail) = match &term.kind {
                        TerminatorKind::Call { func, destination, target, .. } => {
                            let c = callee_of(self.tcx, self.body, func);
                            if let Some(def) = c.def
                                && passthrough(self.tcx, def)
                            {
                                d.via.push(short(&c.name));
                                cur = *destination;
                                w = WLoc::Call(*target);
                                continue;
                            }
                            // the receiver of `as_ptr / as_mut_ptr / ..`: straight back to raw (an exclusion); follow the
                            // raw value on
                            if let Some(def) = c.def
                                && *idx == 0
                                && method_to_raw(self.tcx, def)
                                && returns_raw(self.tcx, destination.ty(self.body, self.tcx).ty)
                            {
                                if d.excluded.is_none() {
                                    d.excluded = Some("method-to-raw");
                                }
                                d.via.push(format!("method-to-raw:{}", short(&c.name)));
                                cur = *destination;
                                w = WLoc::Call(*target);
                                continue;
                            }
                            (func, false)
                        }
                        TerminatorKind::TailCall { func, .. } => (func, true),
                        _ => {
                            d.dest = "other".into();
                            d.detail = "call-arg?".into();
                            return d;
                        }
                    };
                    let c = callee_of(self.tcx, self.body, func);
                    d.dest = "call-arg".into();
                    d.detail = if tail { format!("tail:{}", c.name) } else { c.name.clone() };
                    match c.inputs.get(*idx) {
                        Some(t) => {
                            d.formal_ty = t.to_string();
                            d.formal_safe = safety(self.tcx, *t).into();
                        }
                        None if c.variadic => {
                            d.formal_ty = "...".into();
                            d.formal_safe = "variadic".into();
                        }
                        None => {
                            d.formal_ty = "?".into();
                            d.formal_safe = "other".into();
                        }
                    }
                    return d;
                }
                Use::Drop => {
                    d.dest = "other".into();
                    d.detail = "drop".into();
                    return d;
                }
                Use::DerefUse(what) => {
                    d.dest = "other".into();
                    d.detail = (*what).into();
                    return d;
                }
                Use::Other(what) => {
                    d.dest = "other".into();
                    d.detail = (*what).into();
                    return d;
                }
                Use::Observe => unreachable!(),
            }
        }
        d.dest = "other".into();
        d.detail = "chain-limit".into();
        d
    }

    // ----- the scans

    /// kinds a, b and x.
    fn scan_direct(&self) -> Vec<SiteRow> {
        let (tcx, body) = (self.tcx, self.body);
        let mut rows = Vec::new();
        for (bb, data) in body.basic_blocks.iter_enumerated() {
            if data.is_cleanup {
                continue;
            }
            for (i, st) in data.statements.iter().enumerate() {
                let loc = Location { block: bb, statement_index: i };
                let StatementKind::Assign(b) = &st.kind else { continue };
                let Rvalue::Ref(_, bk, pl) = &b.1 else { continue };
                if matches!(bk, BorrowKind::Fake(_)) {
                    continue;
                }
                let proj = &pl.projection[..];
                let raw: Vec<usize> = (0..proj.len())
                    .filter(|&k| {
                        matches!(proj[k], ProjectionElem::Deref)
                            && PlaceRef { local: pl.local, projection: &proj[..k] }.ty(body, tcx).ty.is_raw_ptr()
                    })
                    .collect();
                let Some(&k) = raw.last() else { continue };
                let src_ty = PlaceRef { local: pl.local, projection: &proj[..k] }.ty(body, tcx).ty;
                let post = proj[k + 1..].iter().filter(|e| matches!(e, ProjectionElem::Deref)).count();
                let (null_dom, null_test, src_arg) = self.null_info(loc, pl.local, &proj[..k]);
                rows.push(SiteRow {
                    span: st.source_info.span,
                    kind: if matches!(bk, BorrowKind::Mut { .. }) { "a:mut-ref" } else { "a:ref" }.into(),
                    call: "-".into(),
                    src_ty: src_ty.to_string(),
                    prod_ty: b.1.ty(body, tcx).to_string(),
                    raw_derefs: raw.len(),
                    post_raw_derefs: post,
                    dest: self.chase(b.0, WLoc::Stmt(loc), 0),
                    null_dom,
                    null_test,
                    src_arg,
                });
            }
            let term = data.terminator();
            let TerminatorKind::Call { func, args, destination, target, .. } = &term.kind else { continue };
            let c = callee_of(tcx, body, func);
            let Some(def) = c.def else { continue };
            let Some(kind) = conv_kind(tcx, def) else { continue };
            let Some(a0) = args.first() else { continue };
            let src = a0.node.ty(body, tcx);
            let prod = destination.ty(body, tcx).ty;
            if kind == "x:transmute" && !(src.is_raw_ptr() && safety(tcx, prod) == "safe") {
                continue;
            }
            let at = Location { block: bb, statement_index: data.statements.len() };
            let nonnull = kind.starts_with("b:nonnull");
            let (null_dom, null_test, src_arg) = if nonnull {
                ("n/a".into(), "-".into(), None)
            } else {
                match a0.node.place() {
                    Some(p) => self.null_info(at, p.local, &p.projection[..]),
                    None => ("no".into(), "-".into(), None),
                }
            };
            // `NonNull::as_ref(&self)`: the pointer is the receiver's pointee, not the `&NonNull<T>` argument
            let src = if nonnull { src.builtin_deref(true).unwrap_or(src) } else { src };
            rows.push(SiteRow {
                span: term.source_info.span,
                kind,
                call: c.name.clone(),
                src_ty: src.to_string(),
                prod_ty: prod.to_string(),
                raw_derefs: 0,
                post_raw_derefs: 0,
                dest: self.chase(*destination, WLoc::Call(*target), 0),
                null_dom,
                null_test,
                src_arg,
            });
        }
        rows
    }

    /// kind h: calls of the current wrappers (callee -> the raw formal it converts).
    fn scan_helpers(&self, wrappers: &HashMap<DefId, usize>) -> Vec<SiteRow> {
        let (tcx, body) = (self.tcx, self.body);
        let mut rows = Vec::new();
        for (bb, data) in body.basic_blocks.iter_enumerated() {
            if data.is_cleanup {
                continue;
            }
            let term = data.terminator();
            let TerminatorKind::Call { func, args, destination, target, .. } = &term.kind else { continue };
            let Some((def, _)) = func.const_fn_def() else { continue };
            let Some(&idx) = wrappers.get(&def) else { continue };
            let Some(a) = args.get(idx) else { continue };
            let c = callee_of(tcx, body, func);
            let at = Location { block: bb, statement_index: data.statements.len() };
            let (null_dom, null_test, src_arg) = match a.node.place() {
                Some(p) => self.null_info(at, p.local, &p.projection[..]),
                None => ("no".into(), "-".into(), None),
            };
            rows.push(SiteRow {
                span: term.source_info.span,
                kind: "h".into(),
                call: c.name.clone(),
                src_ty: a.node.ty(body, tcx).to_string(),
                prod_ty: destination.ty(body, tcx).ty.to_string(),
                raw_derefs: 0,
                post_raw_derefs: 0,
                dest: self.chase(*destination, WLoc::Call(*target), 0),
                null_dom,
                null_test,
                src_arg,
            });
        }
        rows
    }
}

/// A row that makes its body a wrapper: not excluded, reaches the return place, pointer = a raw formal.
fn wraps(r: &SiteRow) -> Option<usize> {
    if r.dest.excluded.is_none() && r.dest.ret { r.src_arg } else { None }
}

// ---------------------------------------------------------------------------------------------------------------

/// The `sites.tsv` text for the crate (`root_dir`: the crate root's directory, for relative file names).
pub fn sites<'tcx>(tcx: TyCtxt<'tcx>, bodies: &[(LocalDefId, Body<'tcx>)], root_dir: &Path) -> String {
    let cxs: Vec<Cx<'_, 'tcx>> = bodies.iter().map(|(d, b)| Cx::new(tcx, *d, b)).collect();
    let direct: Vec<Vec<SiteRow>> = cxs.iter().map(Cx::scan_direct).collect();
    let mut wrappers: HashMap<DefId, usize> = HashMap::new();
    for (cx, rows) in cxs.iter().zip(&direct) {
        for r in rows {
            if let Some(i) = wraps(r) {
                wrappers.entry(cx.did.to_def_id()).or_insert(i);
            }
        }
    }
    // the fixpoint: a body whose call of a wrapper returns the converted value of one of its raw formals is a wrapper
    let mut helpers: Vec<Vec<SiteRow>>;
    loop {
        helpers = cxs.iter().map(|cx| cx.scan_helpers(&wrappers)).collect();
        let before = wrappers.len();
        for (cx, rows) in cxs.iter().zip(&helpers) {
            for r in rows {
                if let Some(i) = wraps(r) {
                    wrappers.entry(cx.did.to_def_id()).or_insert(i);
                }
            }
        }
        if wrappers.len() == before {
            break;
        }
    }
    let sm = tcx.sess.source_map();
    let mut lines: Vec<((String, usize, usize, String), String)> = Vec::new();
    for ((cx, d), h) in cxs.iter().zip(&direct).zip(&helpers) {
        let fn_path = tcx.def_path_str(cx.did);
        for r in d.iter().chain(h) {
            // per row: this row is the conversion that makes its function a wrapper
            let in_wrapper = if wraps(r).is_some() { "yes" } else { "no" };
            let mac = r.span.from_expansion();
            let sp = if mac { r.span.source_callsite() } else { r.span };
            let lo = sm.lookup_char_pos(sp.lo());
            let file = match &lo.file.name {
                FileName::Real(real) => match real.local_path() {
                    Some(p) => p.strip_prefix(root_dir).unwrap_or(p).display().to_string(),
                    None => lo.file.name.prefer_local().to_string(),
                },
                other => other.prefer_local().to_string(),
            };
            let col = lo.col.0 + 1;
            let mut s = String::new();
            let _ = write!(
                s,
                "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
                esc(&file),
                lo.line,
                col,
                esc(&fn_path),
                r.kind,
                esc(&r.call),
                esc(&r.src_ty),
                esc(&r.prod_ty),
                r.dest.dest,
                esc(&r.dest.detail),
                esc(if r.dest.formal_ty.is_empty() { "-" } else { r.dest.formal_ty.as_str() }),
                if r.dest.formal_safe.is_empty() { "-" } else { r.dest.formal_safe.as_str() },
                esc(&if r.dest.via.is_empty() { "-".to_owned() } else { r.dest.via.join(">") }),
                if r.dest.excluded.is_some() { "yes" } else { "no" },
                r.dest.excluded.unwrap_or("-"),
                r.null_dom,
                r.null_test,
                r.raw_derefs,
                r.post_raw_derefs,
                in_wrapper,
                if mac { "yes" } else { "no" },
            );
            lines.push(((file, lo.line, col, r.kind.clone()), s));
        }
    }
    lines.sort();
    let mut out = String::from(
        "file\tline\tcol\tfn\tkind\tcall\tsrc_ty\tprod_ty\tdest\tdest_detail\tformal_ty\tformal_safe\tvia\texcluded\t\
         excl_reason\tnull_dom\tnull_test\traw_derefs\tpost_raw_derefs\tin_wrapper\tmacro\n",
    );
    for (_, l) in lines {
        out.push_str(&l);
        out.push('\n');
    }
    out
}
