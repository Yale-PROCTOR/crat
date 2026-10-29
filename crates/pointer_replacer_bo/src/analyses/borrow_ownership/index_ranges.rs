//! **Index-range disjointness** (relay era-5c/267, R1325-1; the design is
//! era-5c report 218, accepted with riders R1–R5): the borrow model's
//! exclusion check skips an invalidation when the loan and the access reach
//! disjoint byte ranges of one base.
//!
//! **The fact.** A pointer value's *footprint* is `B + [lo, hi)` in bytes: `B`
//! is a pointer formal that is never written and whose address is never taken
//! (its value is the caller's, fixed for the body), and `[lo, hi)` covers every
//! byte any execution reaches through the value or through anything derived
//! from it. The footprint of a value is the union of its uses:
//! - a direct access `*v`, `(*v).f`, `(*v)[i]`: the bytes of the place (field
//!   offsets and element sizes from the layout; an index from the integer
//!   facts below);
//! - a derivation into a local with one definition: a copy, a pointer cast
//!   that keeps the address, `&(*v).f`, core's `offset` / `add` / `sub` (O's
//!   key, relay 264), core's slice `as_ptr` / `as_mut_ptr` (relay 265's key):
//!   that local's own footprint, already relative to `B`;
//! - an argument to a local callee: the callee's per-formal extent `Ext(g, k)`,
//!   instantiated at the call (below);
//! - the destination of `memcpy` / `memmove` / `memset` with a constant
//!   length: `[0, n)` written from the argument; a `memcpy` / `memmove`
//!   *source* is Unknown (the bytes copied out may be a pointer to the base,
//!   used after through the copy);
//! - a comparison or `is_null`: nothing;
//! - a store into a pointer field of a local struct, `s.f = v` (stage 2, E1,
//!   below): the field's path;
//! - anything else is Unknown: any other store into memory, a return, an
//!   aggregate, a cast to an integer, a foreign callee without a row, a local
//!   with two definitions, the address of the pointer local. A pointer
//!   *loaded* from memory is never a derivation (rider R2): it is no base,
//!   only the root of its own footprint (E1's loads). A read of a pointer
//!   stored in the base ends the footprint too (Unknown): what is reached
//!   through it is not the base's bytes, and two such pointers may meet
//!   outside them.
//!
//! **E1, the one-level field path** (stage 2, relay 267 §3). A *holder* is a
//! local struct (never a formal, never a union) a pointer is stored into one
//! field deep. The path of its field `[off, off + size)` is everything reached
//! through the pointer stored there, relative to that pointer: the families
//! of the locals the field is loaded into, in the body, and, through the
//! holder's address, in each local callee it is handed to: `Ext(g, k.f)`, the
//! loads of `(*k).f` in `g` and its callees (`Path`, per formal, bottom-up
//! like `Ext`). The path is Unknown when `g` or a callee stores to `(*k).f`
//! or reads its bytes other than as that pointer (a copy out of them, a
//! whole-struct read), when the holder is read whole in the body, or when its
//! address goes where the walk cannot follow (stored, returned, a foreign or
//! recursive callee). A store to the holder in the body only replaces what
//! the field holds, and every value stored into it carries the whole path in
//! its own footprint. The escape walk keeps such a store (by a local of the
//! base's family, onto a bounded path) from counting as the base's escape.
//! Neither a loaded value nor a holder is ever a base: the discharge takes
//! only a pointer formal.
//!
//! **A base that escapes discharges nothing.** A taint walk follows the
//! base's value through every local it reaches, bounded or not; when any of
//! those uses stores, returns, aggregates or casts it to an integer, takes its
//! address, hands it to a foreign or recursive callee or to a local one whose
//! formal escapes, copies bytes out of it or reads a pointer out of it, a
//! retained copy may reach the base behind every footprint's back, and the
//! discharge refuses.
//!
//! **What no footprint covers:** an access through a pointer to the base that
//! was retained before the function ran (a global or a heap cell holding the
//! base's pointer, set by a caller, used by a callee). That is the
//! retained-alias class every `Ref` formal already meets (the retention
//! rules), not this rung's. Nor a pointer rebuilt byte by byte out of the base
//! through character reads (C11's effective-type rules, the stated premise of
//! R542, leave those to a character copy).
//!
//! **`Ext(g, k)`** is the footprint of `g`'s pointer formal `k` in `g`, relative
//! to the formal; its bounds are constants or `a + b·n` in ONE integer formal
//! `n` of `g`. It is computed once per program, bottom-up over the local call
//! graph's SCCs, from the input's MIR only (never the model's kinds), so it is
//! the same in every round of the guarded repair. It is Unknown when the
//! formal may escape `g` (rider R1): stored, returned (this rung has no return
//! summary), handed to a foreign callee without a row, or handed to a member of
//! `g`'s own SCC. At a call, a bound in `n` is instantiated by the actual: a
//! constant gives a constant, the caller's own integer formal keeps it affine
//! one level up, anything else makes the extent Unknown.
//!
//! **The integer facts** are wave-6l's domain (`bo_rewriter/decision/
//! extent_proof.rs`, which the analysis may not import): a forward dataflow over
//! difference bounds `x − y ≤ c` between zero, the integer formals and the
//! integer locals that feed an index, a step or a guard, with branch and assert
//! conditions applied on their edges and widening at loop heads. A local whose
//! address is taken is never tracked; a local with one constant definition is a
//! constant. Stage 2 adds E2, the equality exit: on the edge where `h ≠ n`,
//! a bound `h ≤ n` already known becomes `h ≤ n − 1` (so a counter stepping by
//! one from below `n` and leaving at `h == n` stays below `n`); and the range
//! of a product `y · c` by a constant `c > 0` at its one definition, which
//! difference bounds cannot hold when `y`'s bound is a formal (`IntFacts::defs`:
//! an unsigned product, or core's unsigned `wrapping_mul`, lies in
//! `[0, c·hi(y)]` wrapped or not; a signed one is exact under
//! `§28:index-step-no-wrap`), carried through copies and value-keeping casts.
//!
//! **The discharge** (`borrow_engine/invalidates.rs`, `check_access_for_conflict`,
//! in the direct and the routed check): an invalidation `(access, loan)` that
//! `places_conflict` admitted is skipped when the loan's footprint (the
//! footprint of its issuer, `Borrower::Assign(Local(i))`, at the loan's own
//! statement) and the access's footprint have the same base, are both
//! constant, and are disjoint. Never discharged (rider R3): a loan whose
//! borrowed place is not behind a deref, a loan whose borrower is not
//! `Assign(Local(_))`, a copy-lend loan (the engine's own check), a write to a
//! whole local, and every access this module does not model at the point
//! (`StorageDead`, `Return`, `Drop`, …). Each discharge records a typed
//! `range-disjoint` receipt (rider R4): the function, the access, the loan, the
//! base, both ranges, the summaries used and the §28 operations the bounds rest
//! on.
//!
//! **Soundness, as the receipt states it.** Every crat claim is conditional on
//! a UB-free input (§28). The footprints over-approximate what a UB-free
//! execution reaches; they rest on three consequences of §28, the three
//! wave-6l's prover states, none a new premise:
//! - `§28:in-bounds-offset` — `offset` / `add` / `sub` stay inside their
//!   allocation (one past the end allowed), so a step never wraps into another
//!   object;
//! - `§28:index-step-no-wrap` — `+ c` on a signed index does not wrap (C's
//!   signed overflow is UB); an unsigned step is taken only when it provably
//!   does not wrap;
//! - `§28:usize-as-isize` — a `usize` index cast to `isize` keeps its value.
//!
//! Unknown discharges nothing; two bases discharge nothing (there is no
//! may-alias reasoning: the parameter-overlap partner's rows are the engine's
//! and are never discharged). **The emission owes the ranges** (R1322-4): the
//! borrow checker cannot see indices and Tree Borrows checks per byte, so the
//! pair is sound only when each emitted view of `B` stays inside its range;
//! the receipt carries both.

use std::{cell::RefCell, collections::BTreeSet, rc::Rc};

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def_id::LocalDefId;
use rustc_middle::{
    mir::{
        BasicBlock, BinOp, Body, CastKind, Local, Location, NonDivergingIntrinsic, Operand, Place,
        PlaceElem, PlaceRef, RETURN_PLACE, Rvalue, StatementKind, TerminatorKind, UnOp,
    },
    ty::{self, Ty, TyCtxt, TyKind, adjustment::PointerCoercion},
};

use crate::{
    analyses::{
        borrow::{Borrower, ProvenanceOwner},
        mir::{CallKind, TerminatorExt},
    },
    utils::rustc::RustProgram,
};

// ---------------------------------------------------------------------------
// The premises, the bounds and the footprints.
// ---------------------------------------------------------------------------

/// A consequence of §28 a bound rests on (the module doc).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum Premise {
    InBoundsOffset,
    IndexStepNoWrap,
    UsizeAsIsize,
}

impl Premise {
    pub(crate) fn label(self) -> &'static str {
        match self {
            Premise::InBoundsOffset => "§28:in-bounds-offset",
            Premise::IndexStepNoWrap => "§28:index-step-no-wrap",
            Premise::UsizeAsIsize => "§28:usize-as-isize",
        }
    }
}

/// The largest magnitude a bound keeps; beyond it, the bound is dropped.
const LIMIT: i64 = 1 << 40;

/// `coef · n + add`, with `n` the integer formal of argument index `formal`, or
/// the constant `add`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct Bound {
    pub(crate) formal: Option<u32>,
    pub(crate) coef: i64,
    pub(crate) add: i64,
}

impl Bound {
    pub(crate) const fn constant(add: i64) -> Self {
        Bound {
            formal: None,
            coef: 0,
            add,
        }
    }

    fn of_formal(formal: u32, add: i64) -> Self {
        Bound {
            formal: Some(formal),
            coef: 1,
            add,
        }
    }

    pub(crate) fn as_constant(self) -> Option<i64> {
        self.formal.is_none().then_some(self.add)
    }

    fn checked(self) -> Option<Self> {
        if self.add.unsigned_abs() >= LIMIT as u64 || self.coef.unsigned_abs() >= LIMIT as u64 {
            return None;
        }
        Some(if self.coef == 0 {
            Bound::constant(self.add)
        } else {
            self
        })
    }

    fn plus(self, other: Bound) -> Option<Bound> {
        let add = self.add.checked_add(other.add)?;
        match (self.formal, other.formal) {
            (None, _) => Bound {
                formal: other.formal,
                coef: other.coef,
                add,
            },
            (_, None) => Bound {
                formal: self.formal,
                coef: self.coef,
                add,
            },
            (Some(a), Some(b)) if a == b => Bound {
                formal: Some(a),
                coef: self.coef.checked_add(other.coef)?,
                add,
            },
            _ => return None,
        }
        .checked()
    }

    fn scale(self, k: i64) -> Option<Bound> {
        Bound {
            formal: self.formal,
            coef: self.coef.checked_mul(k)?,
            add: self.add.checked_mul(k)?,
        }
        .checked()
    }

    /// Two bounds compare when both are constants or both are the same multiple
    /// of one formal.
    fn comparable(self, other: Bound) -> bool {
        self.formal == other.formal && (self.formal.is_none() || self.coef == other.coef)
    }

    fn min(self, other: Bound) -> Option<Bound> {
        self.comparable(other)
            .then(|| if self.add <= other.add { self } else { other })
    }

    fn max(self, other: Bound) -> Option<Bound> {
        self.comparable(other)
            .then(|| if self.add >= other.add { self } else { other })
    }
}

/// An integer's interval at a point, inclusive; a side is `None` when the
/// facts bound it neither by a constant nor by a formal.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct IntRange {
    pub(crate) lo: Option<Bound>,
    pub(crate) hi: Option<Bound>,
    pub(crate) premises: BTreeSet<Premise>,
}

impl IntRange {
    fn exact(k: i64) -> Self {
        IntRange {
            lo: Some(Bound::constant(k)),
            hi: Some(Bound::constant(k)),
            premises: BTreeSet::new(),
        }
    }

    /// The constant the range pins, or the formal it equals.
    fn actual(&self) -> Option<Bound> {
        match (self.lo, self.hi) {
            (Some(lo), Some(hi)) if lo == hi => Some(lo),
            _ => None,
        }
    }
}

/// What a value reaches, relative to its base.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Footprint {
    /// Nothing is read or written through the value.
    Empty,
    Bytes(Bytes),
    /// Not bounded, with the first reason met.
    Unknown(&'static str),
}

/// `[lo, hi)` bytes from the base, `hi` exclusive.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Bytes {
    pub(crate) lo: Bound,
    pub(crate) hi: Bound,
    pub(crate) writes: bool,
    pub(crate) premises: BTreeSet<Premise>,
    /// The `(callee, formal)` summaries the footprint used.
    pub(crate) summaries: FxHashSet<(LocalDefId, u32)>,
}

impl Footprint {
    fn bytes(lo: Bound, hi: Bound, writes: bool, premises: BTreeSet<Premise>) -> Footprint {
        Footprint::Bytes(Bytes {
            lo,
            hi,
            writes,
            premises,
            summaries: FxHashSet::default(),
        })
        .normal()
    }

    /// A constant range that holds no byte is `Empty`.
    fn normal(self) -> Footprint {
        match &self {
            Footprint::Bytes(bytes) => match (bytes.lo.as_constant(), bytes.hi.as_constant()) {
                (Some(lo), Some(hi)) if hi <= lo => Footprint::Empty,
                _ => self,
            },
            _ => self,
        }
    }

    fn join(self, other: Footprint) -> Footprint {
        match (self, other) {
            (Footprint::Unknown(why), _) | (_, Footprint::Unknown(why)) => Footprint::Unknown(why),
            (Footprint::Empty, other) | (other, Footprint::Empty) => other,
            (Footprint::Bytes(a), Footprint::Bytes(b)) => {
                let (Some(lo), Some(hi)) = (a.lo.min(b.lo), a.hi.max(b.hi)) else {
                    return Footprint::Unknown("incomparable-bounds");
                };
                Footprint::Bytes(Bytes {
                    lo,
                    hi,
                    writes: a.writes || b.writes,
                    premises: a.premises.union(&b.premises).copied().collect(),
                    summaries: a.summaries.union(&b.summaries).copied().collect(),
                })
            }
        }
    }

    /// `[lo + self.lo, hi + self.hi)`: the footprint of a value at an offset in
    /// `[lo, hi]`.
    fn shift(self, lo: Bound, hi: Bound, premises: &BTreeSet<Premise>) -> Footprint {
        match self {
            Footprint::Bytes(mut bytes) => {
                let (Some(new_lo), Some(new_hi)) = (lo.plus(bytes.lo), hi.plus(bytes.hi)) else {
                    return Footprint::Unknown("two-formals");
                };
                bytes.lo = new_lo;
                bytes.hi = new_hi;
                bytes.premises.extend(premises.iter().copied());
                Footprint::Bytes(bytes).normal()
            }
            other => other,
        }
    }

    /// `None` unless every bound is a constant; `Some(None)` for `Empty`.
    pub(crate) fn constant(&self) -> Option<Option<(i64, i64)>> {
        match self {
            Footprint::Empty => Some(None),
            Footprint::Bytes(bytes) => {
                Some(Some((bytes.lo.as_constant()?, bytes.hi.as_constant()?)))
            }
            Footprint::Unknown(_) => None,
        }
    }

    fn writes(&self) -> bool {
        matches!(self, Footprint::Bytes(bytes) if bytes.writes)
    }

    fn premises(&self) -> BTreeSet<Premise> {
        match self {
            Footprint::Bytes(bytes) => bytes.premises.clone(),
            _ => BTreeSet::new(),
        }
    }

    fn summaries(&self) -> FxHashSet<(LocalDefId, u32)> {
        match self {
            Footprint::Bytes(bytes) => bytes.summaries.clone(),
            _ => FxHashSet::default(),
        }
    }

    /// The footprint with `g`'s bounds in its formals replaced by the actuals.
    fn instantiate(self, actual: &dyn Fn(u32) -> Option<Bound>) -> Footprint {
        let Footprint::Bytes(mut bytes) = self else {
            return self;
        };
        let bound = |b: Bound| instantiate_bound(b, actual);
        let (Some(lo), Some(hi)) = (bound(bytes.lo), bound(bytes.hi)) else {
            return Footprint::Unknown("non-constant-actual");
        };
        bytes.lo = lo;
        bytes.hi = hi;
        Footprint::Bytes(bytes).normal()
    }
}

/// A bound of `g`'s with its formal replaced by the actual.
fn instantiate_bound(b: Bound, actual: &dyn Fn(u32) -> Option<Bound>) -> Option<Bound> {
    match b.formal {
        None => Some(b),
        Some(formal) => {
            let value = actual(formal)?;
            value.scale(b.coef)?.plus(Bound::constant(b.add))
        }
    }
}

/// The most byte ranges a path keeps apart; past it they are merged, and then
/// one hull.
const MAX_TOUCHED: usize = 64;

/// E1, what a pointer's object gives out of the pointers stored in it, one
/// field deep: the bytes of the object (relative to the pointer) that are
/// written, or read other than as a pointer load at a constant offset; and
/// each such load, with the footprint of the loaded value (relative to that
/// value). A pointer stored in the object is reached only through those
/// loads, so the path of the field at `[off, off + size)` is the join of the
/// loads at exactly `off`. It is Unknown when a touched range meets the field
/// (a store to it, a copy of its bytes) or the object is reached where the
/// walk cannot follow.
#[derive(Clone, Debug, Default)]
pub(crate) struct Path {
    opaque: Option<&'static str>,
    /// `None`: a range with no bound.
    touched: Vec<Option<(Bound, Bound)>>,
    /// `(offset, size, footprint of the loaded value)`.
    loads: Vec<(i64, i64, Footprint)>,
}

impl Path {
    fn opaque(why: &'static str) -> Path {
        Path {
            opaque: Some(why),
            ..Path::default()
        }
    }

    fn stop(&mut self, why: &'static str) {
        self.opaque.get_or_insert(why);
    }

    fn touch(&mut self, range: Option<(Bound, Bound)>) {
        self.touched.push(range);
        if self.touched.len() <= MAX_TOUCHED {
            return;
        }
        let mut constant: Vec<(i64, i64)> = Vec::new();
        let mut rest = Vec::new();
        for range in self.touched.drain(..) {
            match range.and_then(|(lo, hi)| Some((lo.as_constant()?, hi.as_constant()?))) {
                Some(range) => constant.push(range),
                None => rest.push(range),
            }
        }
        constant.sort();
        let mut merged: Vec<(i64, i64)> = Vec::new();
        for (lo, hi) in constant {
            match merged.last_mut() {
                Some(last) if lo <= last.1 => last.1 = last.1.max(hi),
                _ => merged.push((lo, hi)),
            }
        }
        rest.dedup();
        if merged.len() + rest.len() > MAX_TOUCHED {
            if !rest.is_empty() {
                self.stop("touched");
            }
            if let (Some(first), Some(last)) = (merged.first(), merged.last()) {
                merged = vec![(first.0, last.1)];
            }
        }
        self.touched = merged
            .into_iter()
            .map(|(lo, hi)| Some((Bound::constant(lo), Bound::constant(hi))))
            .chain(rest)
            .collect();
    }

    /// The path of the pointer stored at `[off, off + size)`.
    fn at(&self, off: i64, size: i64) -> Footprint {
        if let Some(why) = self.opaque {
            return Footprint::Unknown(why);
        }
        let meets = |lo: i64, hi: i64| lo < off + size && off < hi;
        for range in &self.touched {
            match range.and_then(|(lo, hi)| Some((lo.as_constant()?, hi.as_constant()?))) {
                Some((lo, hi)) if !meets(lo, hi) => {}
                _ => return Footprint::Unknown("field-touched"),
            }
        }
        let mut fp = Footprint::Empty;
        for (o, s, loaded) in &self.loads {
            if (*o, *s) == (off, size) {
                fp = fp.join(loaded.clone());
            } else if meets(*o, o + s) {
                return Footprint::Unknown("field-misread");
            }
        }
        fp
    }

    /// A callee's path for an argument at `[deriv.lo, deriv.hi]` from this
    /// path's root, its bounds instantiated by the actuals.
    fn absorb(
        &mut self,
        callee: &Path,
        deriv: &Deriv,
        actual: &dyn Fn(u32) -> Option<Bound>,
        summary: (LocalDefId, u32),
    ) {
        if let Some(why) = callee.opaque {
            self.stop(why);
            return;
        }
        let shift = |lo: Bound, hi: Bound| -> Option<(Bound, Bound)> {
            Some((
                deriv.lo.plus(instantiate_bound(lo, actual)?)?,
                deriv.hi.plus(instantiate_bound(hi, actual)?)?,
            ))
        };
        for range in &callee.touched {
            self.touch(range.and_then(|(lo, hi)| shift(lo, hi)));
        }
        for (o, s, loaded) in &callee.loads {
            let loaded = match loaded.clone().instantiate(actual) {
                Footprint::Bytes(mut bytes) => {
                    bytes.summaries.insert(summary);
                    Footprint::Bytes(bytes)
                }
                other => other,
            };
            match deriv.lo.as_constant() {
                Some(d) if deriv.lo == deriv.hi => self.loads.push((o + d, *s, loaded)),
                // A load at an offset not known exactly: its bytes are
                // touched.
                _ => self.touch(shift(Bound::constant(*o), Bound::constant(o + s))),
            }
        }
    }
}

/// A pointer local's value: its base and its offset in `[lo, hi]` bytes from
/// it (inclusive), over every execution of its one definition.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Deriv {
    pub(crate) root: Local,
    pub(crate) lo: Bound,
    pub(crate) hi: Bound,
    pub(crate) premises: BTreeSet<Premise>,
}

/// The bound sum, for the domain's unit tests.
#[cfg(test)]
pub(crate) fn test_plus(a: Bound, b: Bound) -> Option<Bound> {
    a.plus(b)
}

// ---------------------------------------------------------------------------
// The receipt.
// ---------------------------------------------------------------------------

/// One discharged invalidation: at `access` in `function`, the access did not
/// invalidate the loan issued at `loan` to `issuer`, because both reach only
/// their own bytes of the pointer formal `base`. The emission owes the ranges:
/// each view of `base` must stay inside its range.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct RangeDisjoint {
    pub(crate) function: LocalDefId,
    pub(crate) access: Location,
    pub(crate) loan: Location,
    pub(crate) issuer: Local,
    pub(crate) base: Local,
    /// `[lo, hi)` bytes of `base`; `None` when nothing is reached.
    pub(crate) loan_bytes: Option<(i64, i64)>,
    pub(crate) loan_writes: bool,
    pub(crate) access_bytes: Option<(i64, i64)>,
    pub(crate) access_writes: bool,
    /// The `(callee, formal)` summaries either side used.
    pub(crate) summaries: Vec<(LocalDefId, u32)>,
    /// The §28 operations the bounds rest on (`Premise::label`).
    pub(crate) premises: Vec<&'static str>,
}

#[cfg(test)]
thread_local! {
    static RECEIPTS: RefCell<Vec<RangeDisjoint>> = const { RefCell::new(Vec::new()) };
}

/// Record a discharge: in the export (the final round's, under a capture) and,
/// in a test build, for the witnesses.
pub(crate) fn record(receipt: RangeDisjoint) {
    #[cfg(test)]
    RECEIPTS.with(|receipts| receipts.borrow_mut().push(receipt.clone()));
    super::export::record_range_disjoint(receipt);
}

/// Every receipt recorded on this thread since the last call.
#[cfg(test)]
pub(crate) fn take_receipts() -> Vec<RangeDisjoint> {
    RECEIPTS.with(|receipts| std::mem::take(&mut *receipts.borrow_mut()))
}

// ---------------------------------------------------------------------------
// The table and its scope.
// ---------------------------------------------------------------------------

thread_local! {
    /// The program's table and its holders: built by the first `ensure` (the
    /// solve's, once per run, or an engine context's that finds none), dropped
    /// with the last holder. Per thread, like the solve.
    static TABLE: RefCell<Option<(Rc<IndexRanges>, usize)>> = const { RefCell::new(None) };
}

/// One holder of the installed table; the last one to drop clears it. Not
/// `Send`: it must drop on the thread whose table it holds.
pub(crate) struct Scope(std::marker::PhantomData<*const ()>);

impl Drop for Scope {
    fn drop(&mut self) {
        TABLE.with(|slot| {
            let mut slot = slot.borrow_mut();
            if let Some((_, holders)) = slot.as_mut() {
                *holders -= 1;
                if *holders == 0 {
                    *slot = None;
                }
            }
        });
    }
}

/// Hold the installed table, building it for `program` when none is.
pub(crate) fn ensure(program: &RustProgram<'_>) -> Scope {
    let installed = TABLE.with(|slot| {
        let mut slot = slot.borrow_mut();
        match slot.as_mut() {
            Some((_, holders)) => {
                *holders += 1;
                true
            }
            None => false,
        }
    });
    if !installed {
        crate::phase_log::mark("index_ranges:build", "start", "");
        let table = Rc::new(IndexRanges::build(program));
        crate::phase_log::mark("index_ranges:build", "end", "");
        TABLE.with(|slot| *slot.borrow_mut() = Some((table, 1)));
    }
    Scope(std::marker::PhantomData)
}

/// The discharge (the module doc), against the installed table; `None` when
/// none is installed.
pub(crate) fn discharge<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    location: Location,
    place: Place<'tcx>,
    write: bool,
    loan: Loan<'tcx>,
) -> Option<RangeDisjoint> {
    let table = TABLE.with(|slot| slot.borrow().as_ref().map(|(table, _)| table.clone()))?;
    table.discharge(tcx, body, location, place, write, loan)
}

/// The loan as the discharge reads it: its borrowed place, its borrower and
/// the statement that issues it.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Loan<'tcx> {
    pub(crate) borrowed: Place<'tcx>,
    pub(crate) assigned: Borrower,
    pub(crate) location: Location,
}

/// Per program: each function's facts and the per-formal summaries.
pub(crate) struct IndexRanges {
    functions: FxHashMap<LocalDefId, FnFacts>,
    summaries: FxHashMap<(LocalDefId, u32), Footprint>,
    /// The `(g, k)` whose formal escapes `g`: stored, returned, handed where
    /// the walk cannot follow, or read out as a pointer.
    escapes: FxHashSet<(LocalDefId, u32)>,
    /// E1: `(g, k)`'s path, what `g` and its callees give out of the pointers
    /// stored in `*k`.
    paths: FxHashMap<(LocalDefId, u32), Path>,
    scc: FxHashMap<LocalDefId, usize>,
}

/// One function's facts, computed once.
struct FnFacts {
    shape: Shape,
    ints: IntFacts,
    /// E1's holders: the local structs a pointer is stored into.
    holders: FxHashSet<Local>,
    derivs: FxHashMap<Local, Deriv>,
    /// Complete once built: every local of `derivs` has its family.
    families: RefCell<FxHashMap<Local, Footprint>>,
    /// Complete once built: the path of every holder field a pointer is
    /// stored into, by `(holder, offset)`.
    holder_paths: RefCell<FxHashMap<(Local, i64), Footprint>>,
    /// The paths of the pointer formals, by argument index (moved into the
    /// table).
    paths: FxHashMap<u32, Path>,
    /// The bases some use of which escapes the body: stored, returned,
    /// handed where the walk cannot follow, or a pointer read out of it. A
    /// copy so retained may reach the base behind every footprint's back, so
    /// such a base discharges nothing (the reviewer's same-body retention
    /// guard).
    escaped: FxHashSet<Local>,
}

impl IndexRanges {
    pub(crate) fn build(program: &RustProgram<'_>) -> IndexRanges {
        let tcx = program.tcx;
        let set: FxHashSet<LocalDefId> = program.functions.iter().copied().collect();
        // The local call graph, and its SCCs callees first (petgraph's Tarjan
        // gives them in post-order).
        let mut graph = petgraph::graph::DiGraph::<LocalDefId, ()>::new();
        let mut node = FxHashMap::default();
        for &f in &program.functions {
            node.insert(f, graph.add_node(f));
        }
        for &f in &program.functions {
            let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
            for data in body.basic_blocks.iter() {
                if let TerminatorKind::Call { func, .. } = &data.terminator().kind
                    && let Some((callee, _)) = func.const_fn_def()
                    && let Some(callee) = callee.as_local()
                    && set.contains(&callee)
                {
                    graph.add_edge(node[&f], node[&callee], ());
                }
            }
        }
        let mut table = IndexRanges {
            functions: FxHashMap::default(),
            summaries: FxHashMap::default(),
            escapes: FxHashSet::default(),
            paths: FxHashMap::default(),
            scc: FxHashMap::default(),
        };
        for (index, component) in petgraph::algo::tarjan_scc(&graph).into_iter().enumerate() {
            for &member in &component {
                table.scc.insert(graph[member], index);
            }
            for &member in &component {
                let f = graph[member];
                let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
                let mut facts = FnFacts::build(tcx, &body, f, &table);
                for k in 0..body.arg_count {
                    let formal = Local::from_usize(k + 1);
                    if pointee(body.local_decls[formal].ty).is_none() {
                        continue;
                    }
                    let path = facts
                        .paths
                        .remove(&(k as u32))
                        .unwrap_or_else(|| Path::opaque("formal-written"));
                    table.paths.insert((f, k as u32), path);
                    let extent = match facts.derivs.get(&formal) {
                        Some(_) => facts
                            .families
                            .borrow()
                            .get(&formal)
                            .cloned()
                            .unwrap_or(Footprint::Unknown("no-family")),
                        None => Footprint::Unknown("formal-written"),
                    };
                    table.summaries.insert((f, k as u32), extent);
                    if facts.escaped.contains(&formal) {
                        table.escapes.insert((f, k as u32));
                    }
                }
                table.functions.insert(f, facts);
            }
        }
        table
    }

    /// `Ext(g, k)`.
    pub(crate) fn ext(&self, function: LocalDefId, formal: u32) -> Footprint {
        self.summaries
            .get(&(function, formal))
            .cloned()
            .unwrap_or(Footprint::Unknown("no-summary"))
    }

    /// A local's base and footprint in `function`.
    #[cfg(test)]
    pub(crate) fn family(&self, function: LocalDefId, local: Local) -> Option<(Local, Footprint)> {
        let facts = self.functions.get(&function)?;
        let deriv = facts.derivs.get(&local)?;
        Some((deriv.root, facts.families.borrow().get(&local)?.clone()))
    }

    fn discharge<'tcx>(
        &self,
        tcx: TyCtxt<'tcx>,
        body: &Body<'tcx>,
        location: Location,
        place: Place<'tcx>,
        write: bool,
        loan: Loan<'tcx>,
    ) -> Option<RangeDisjoint> {
        let function = body.source.def_id().as_local()?;
        let facts = self.functions.get(&function)?;
        // The loan: behind a deref, issued to a local at its one definition.
        if loan.borrowed.projection.first() != Some(&PlaceElem::Deref) {
            return None;
        }
        let Borrower::Assign(ProvenanceOwner::Local(issuer)) = loan.assigned else {
            return None;
        };
        if facts.shape.only_def(issuer) != Some(loan.location) {
            return None;
        }
        // The base is a pointer formal: a loaded value (R2) and a holder's
        // address (E1) are roots of their own paths, never bases.
        let loan_root = facts.derivs.get(&issuer)?.root;
        if !facts.shape.fixed_formal(loan_root) || facts.escaped.contains(&loan_root) {
            return None;
        }
        let loan_fp = facts.families.borrow().get(&issuer)?.clone();
        // The access: a write to a whole local never; otherwise the modeled
        // uses of exactly this place at this point.
        if place.projection.is_empty() && write {
            return None;
        }
        let ctx = Ctx::new(tcx, body, function, facts, self);
        let mut access_fp = None::<Footprint>;
        let mut access_root = None;
        for occ in occurrences(body, location) {
            if occ.accessed != place {
                continue;
            }
            let root = facts.derivs.get(&occ.from)?.root;
            if *access_root.get_or_insert(root) != root {
                return None;
            }
            let fp = ctx.footprint_of(&occ, location);
            access_fp = Some(match access_fp {
                None => fp,
                Some(previous) => previous.join(fp),
            });
        }
        let (access_fp, access_root) = (access_fp?, access_root?);
        if access_root != loan_root {
            return None;
        }
        let loan_bytes = loan_fp.constant()?;
        let access_bytes = access_fp.constant()?;
        if let (Some((a_lo, a_hi)), Some((b_lo, b_hi))) = (loan_bytes, access_bytes)
            && !(a_hi <= b_lo || b_hi <= a_lo)
        {
            return None;
        }
        let mut premises = loan_fp.premises();
        premises.extend(access_fp.premises());
        let mut summaries: Vec<(LocalDefId, u32)> = loan_fp.summaries().into_iter().collect();
        summaries.extend(access_fp.summaries());
        summaries.sort_by_key(|(callee, formal)| (callee.local_def_index.as_u32(), *formal));
        summaries.dedup();
        Some(RangeDisjoint {
            function,
            access: location,
            loan: loan.location,
            issuer,
            base: loan_root,
            loan_bytes,
            loan_writes: loan_fp.writes(),
            access_bytes,
            access_writes: access_fp.writes(),
            summaries,
            premises: premises.into_iter().map(Premise::label).collect(),
        })
    }
}

// ---------------------------------------------------------------------------
// Shapes: definitions and taken addresses.
// ---------------------------------------------------------------------------

/// Where each local is written as a whole, and which locals have their address
/// taken (`&x`, `&x.f`: no deref on the way).
struct Shape {
    defs: FxHashMap<Local, Vec<Location>>,
    address_taken: FxHashSet<Local>,
    arg_count: usize,
}

impl Shape {
    fn new(body: &Body<'_>) -> Shape {
        let mut defs: FxHashMap<Local, Vec<Location>> = FxHashMap::default();
        let mut address_taken = FxHashSet::default();
        for (block, data) in body.basic_blocks.iter_enumerated() {
            for (statement_index, statement) in data.statements.iter().enumerate() {
                let location = Location {
                    block,
                    statement_index,
                };
                match &statement.kind {
                    StatementKind::Assign(box (place, rvalue)) => {
                        if let Some(local) = place.as_local() {
                            defs.entry(local).or_default().push(location);
                        }
                        if let Rvalue::Ref(_, _, borrowed) | Rvalue::RawPtr(_, borrowed) = rvalue
                            && !borrowed.projection.contains(&PlaceElem::Deref)
                        {
                            address_taken.insert(borrowed.local);
                        }
                    }
                    StatementKind::SetDiscriminant { place, .. } | StatementKind::Deinit(place) => {
                        if let Some(local) = place.as_local() {
                            defs.entry(local).or_default().push(location);
                        }
                    }
                    _ => {}
                }
            }
            let location = body.terminator_loc(block);
            match &data.terminator().kind {
                TerminatorKind::Call { destination, .. } => {
                    if let Some(local) = destination.as_local() {
                        defs.entry(local).or_default().push(location);
                    }
                }
                TerminatorKind::InlineAsm { operands, .. } => {
                    for operand in operands.iter() {
                        if let rustc_middle::mir::InlineAsmOperand::Out {
                            place: Some(place), ..
                        }
                        | rustc_middle::mir::InlineAsmOperand::InOut {
                            out_place: Some(place),
                            ..
                        } = operand
                        {
                            address_taken.insert(place.local);
                        }
                    }
                }
                _ => {}
            }
        }
        Shape {
            defs,
            address_taken,
            arg_count: body.arg_count,
        }
    }

    fn is_formal(&self, local: Local) -> bool {
        (1..=self.arg_count).contains(&local.as_usize())
    }

    /// The local's one definition, if it has exactly one and is not a formal.
    fn only_def(&self, local: Local) -> Option<Location> {
        if self.is_formal(local) || self.address_taken.contains(&local) {
            return None;
        }
        match self.defs.get(&local).map(Vec::as_slice) {
            Some([only]) => Some(*only),
            _ => None,
        }
    }

    /// A formal never written and never addressed: its value is the caller's.
    fn fixed_formal(&self, local: Local) -> bool {
        self.is_formal(local)
            && !self.address_taken.contains(&local)
            && self.defs.get(&local).is_none_or(Vec::is_empty)
    }
}

/// The pointee of a raw pointer or a reference.
fn pointee(ty: Ty<'_>) -> Option<Ty<'_>> {
    match ty.kind() {
        TyKind::RawPtr(pointee, _) | TyKind::Ref(_, pointee, _) => Some(*pointee),
        _ => None,
    }
}

/// The bit width and signedness of an integer type.
fn int_shape(ty: Ty<'_>) -> Option<(u64, bool)> {
    match ty.kind() {
        TyKind::Int(int) => Some((int.bit_width().unwrap_or(64), true)),
        TyKind::Uint(uint) => Some((uint.bit_width().unwrap_or(64), false)),
        _ => None,
    }
}

/// The statement or the terminator at a location.
enum At<'a, 'tcx> {
    Statement(&'a rustc_middle::mir::Statement<'tcx>),
    Terminator(&'a rustc_middle::mir::Terminator<'tcx>),
}

fn at<'a, 'tcx>(body: &'a Body<'tcx>, location: Location) -> At<'a, 'tcx> {
    let data = &body.basic_blocks[location.block];
    match data.statements.get(location.statement_index) {
        Some(statement) => At::Statement(statement),
        None => At::Terminator(data.terminator()),
    }
}

fn operand_local(operand: &Operand<'_>) -> Option<Local> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => place.as_local(),
        Operand::Constant(_) => None,
    }
}

/// O's key (relay 264): core's raw-pointer `offset` / `add` / `sub`, never the
/// name alone; the result stays in the receiver's allocation under §28.
fn core_pointer_step(tcx: TyCtxt<'_>, call: &CallKind) -> Option<bool> {
    let CallKind::RustLib(did) = call else {
        return None;
    };
    if tcx.crate_name(did.krate).as_str() != "core" || !tcx.def_path_str(*did).contains("::ptr::") {
        return None;
    }
    match tcx.item_name(*did).as_str() {
        "offset" | "add" => Some(false),
        "sub" => Some(true),
        _ => None,
    }
}

/// Core's raw-pointer `is_null`: reads nothing through the pointer.
fn core_is_null(tcx: TyCtxt<'_>, call: &CallKind) -> bool {
    matches!(call, CallKind::RustLib(did)
        if tcx.crate_name(did.krate).as_str() == "core"
            && tcx.def_path_str(*did).contains("::ptr::")
            && tcx.item_name(*did).as_str() == "is_null")
}

/// Relay 265's key: core's slice `as_ptr` / `as_mut_ptr`, resolved, on an
/// inherent impl of a slice type: the result is the receiver's buffer.
fn core_slice_buffer<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>, func: &Operand<'tcx>) -> bool {
    func.const_fn_def().is_some_and(|(def_id, args)| {
        ty::Instance::try_resolve(tcx, body.typing_env(tcx), def_id, args)
            .ok()
            .flatten()
            .is_some_and(|instance| {
                let item = instance.def_id();
                matches!(instance.def, ty::InstanceKind::Item(_))
                    && tcx.crate_name(item.krate).as_str() == "core"
                    && matches!(tcx.item_name(item).as_str(), "as_mut_ptr" | "as_ptr")
                    && tcx.impl_of_method(item).is_some_and(|impl_did| {
                        tcx.trait_id_of_impl(impl_did).is_none()
                            && matches!(
                                tcx.type_of(impl_did).skip_binder().kind(),
                                TyKind::Slice(_)
                            )
                    })
            })
    })
}

/// The libc rows: `(destination written, source read)` argument indices and
/// the length's, for `memcpy` / `memmove` / `memset`.
fn libc_row(call: &CallKind) -> Option<(usize, Option<usize>, usize)> {
    let CallKind::LibC(name) = call else {
        return None;
    };
    match name.as_str() {
        "memcpy" | "memmove" => Some((0, Some(1), 2)),
        "memset" => Some((0, None, 2)),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// The integer facts (wave-6l's difference-bound domain).
// ---------------------------------------------------------------------------

/// +∞ in the matrix; bounds are kept far from overflow.
const INF: i64 = i64::MAX / 4;

/// The most integer locals one function tracks; a larger slice tracks none.
const MAX_TRACKED: usize = 200;

/// A difference-bound matrix: `m[i * n + j]` bounds `x_i − x_j`. Variable 0 is
/// the constant zero.
#[derive(Clone, PartialEq, Eq, Debug)]
struct Dbm {
    n: usize,
    m: Vec<i64>,
}

impl Dbm {
    fn top(n: usize) -> Self {
        let mut m = vec![INF; n * n];
        for i in 0..n {
            m[i * n + i] = 0;
        }
        Dbm { n, m }
    }

    fn get(&self, i: usize, j: usize) -> i64 {
        self.m[i * self.n + j]
    }

    fn sum(a: i64, b: i64) -> i64 {
        if a >= INF || b >= INF {
            INF
        } else {
            (a + b).clamp(-INF, INF)
        }
    }

    /// Adds `x_i − x_j ≤ c` and restores closure.
    fn constrain(&mut self, i: usize, j: usize, c: i64) {
        if c >= self.get(i, j) {
            return;
        }
        let n = self.n;
        let into_i: Vec<i64> = (0..n).map(|k| self.get(k, i)).collect();
        let out_of_j: Vec<i64> = (0..n).map(|l| self.get(j, l)).collect();
        for k in 0..n {
            if into_i[k] >= INF {
                continue;
            }
            let through = Self::sum(into_i[k], c);
            for l in 0..n {
                let bound = Self::sum(through, out_of_j[l]);
                if bound < self.m[k * n + l] {
                    self.m[k * n + l] = bound;
                }
            }
        }
    }

    fn forget(&mut self, x: usize) {
        let n = self.n;
        for k in 0..n {
            if k != x {
                self.m[x * n + k] = INF;
                self.m[k * n + x] = INF;
            }
        }
    }

    /// `x := y + c`.
    fn assign(&mut self, x: usize, y: usize, c: i64) {
        if x == y {
            let n = self.n;
            for k in 0..n {
                if k == x {
                    continue;
                }
                let out = self.m[x * n + k];
                if out < INF {
                    self.m[x * n + k] = (out + c).clamp(-INF, INF);
                }
                let into = self.m[k * n + x];
                if into < INF {
                    self.m[k * n + x] = (into - c).clamp(-INF, INF);
                }
            }
            return;
        }
        self.forget(x);
        self.constrain(x, y, c);
        self.constrain(y, x, -c);
    }

    fn exact(&self, x: usize) -> Option<i64> {
        let (upper, lower) = (self.get(x, 0), self.get(0, x));
        (upper < INF && upper == -lower).then_some(upper)
    }

    fn bottom(&self) -> bool {
        (0..self.n).any(|i| self.get(i, i) < 0)
    }

    fn join(&self, other: &Dbm) -> Dbm {
        Dbm {
            n: self.n,
            m: self
                .m
                .iter()
                .zip(&other.m)
                .map(|(a, b)| *a.max(b))
                .collect(),
        }
    }

    /// The standard widening: a bound that grew is dropped.
    fn widen(&self, newer: &Dbm) -> Dbm {
        Dbm {
            n: self.n,
            m: self
                .m
                .iter()
                .zip(&newer.m)
                .map(|(old, new)| if new > old { INF } else { *old })
                .collect(),
        }
    }

    fn leq(&self, other: &Dbm) -> bool {
        self.m.iter().zip(&other.m).all(|(a, b)| a <= b)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Term {
    Var(usize),
    Const(i64),
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct Cond {
    op: BinOp,
    left: Term,
    right: Term,
}

#[derive(Clone, PartialEq, Eq, Debug)]
struct IState {
    dbm: Dbm,
    conds: FxHashMap<Local, Cond>,
    premises: BTreeSet<Premise>,
}

impl IState {
    fn join(&self, other: &IState, widen: bool) -> IState {
        let dbm = if widen {
            self.dbm.widen(&self.dbm.join(&other.dbm))
        } else {
            self.dbm.join(&other.dbm)
        };
        IState {
            dbm,
            conds: self
                .conds
                .iter()
                .filter(|(local, cond)| other.conds.get(local) == Some(cond))
                .map(|(local, cond)| (*local, *cond))
                .collect(),
            premises: self.premises.union(&other.premises).copied().collect(),
        }
    }

    fn leq(&self, other: &IState) -> bool {
        self.dbm.leq(&other.dbm)
            && other
                .conds
                .iter()
                .all(|(local, cond)| self.conds.get(local) == Some(cond))
            && self.premises.is_subset(&other.premises)
    }
}

/// The integer facts one function's derivations read: the constants, the
/// interval of each indexing or argument local where it is used, and the
/// interval of each product (and of what keeps its value) at its one
/// definition.
struct IntFacts {
    consts: FxHashMap<Local, i64>,
    ranges: FxHashMap<(Location, Local), IntRange>,
    /// A local with one definition, never addressed: its interval at every
    /// use. Products `y · c` by a constant `c > 0` (an unsigned one, or
    /// core's unsigned `wrapping_mul`, is in `[0, c·hi(y)]` whether it wraps
    /// or not: a wrapped product is below 2^bits, which is at most `c·y`; a
    /// signed one is exact under `§28:index-step-no-wrap`), and the copies
    /// and value-keeping casts of those. The difference bounds cannot hold
    /// `c·n`; this can.
    defs: FxHashMap<Local, IntRange>,
}

impl IntFacts {
    fn range(&self, location: Location, local: Local) -> Option<IntRange> {
        if let Some(k) = self.consts.get(&local) {
            return Some(IntRange::exact(*k));
        }
        combine(self.ranges.get(&(location, local)), self.defs.get(&local))
    }
}

/// The interval at a point, each side the point's when it has one and the
/// definition's otherwise.
fn combine(at: Option<&IntRange>, def: Option<&IntRange>) -> Option<IntRange> {
    let (at, def) = match (at, def) {
        (None, None) => return None,
        (Some(only), None) | (None, Some(only)) => return Some(only.clone()),
        (Some(at), Some(def)) => (at, def),
    };
    let mut premises = BTreeSet::new();
    let mut side = |mine: Option<Bound>, theirs: Option<Bound>, from: &IntRange| match mine {
        Some(bound) => Some(bound),
        None => {
            premises.extend(from.premises.iter().copied());
            theirs
        }
    };
    let lo = side(at.lo, def.lo, def);
    let hi = side(at.hi, def.hi, def);
    premises.extend(at.premises.iter().copied());
    Some(IntRange { lo, hi, premises })
}

struct Ints<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    /// Locals whose address is taken: never a condition (a write through the
    /// address would leave it stale: the reviewer's B1).
    address_taken: &'a FxHashSet<Local>,
    /// Locals used only as the count of core's `offset` / `add` / `sub`.
    offset_only: FxHashSet<Local>,
    consts: FxHashMap<Local, i64>,
    vars: FxHashMap<Local, usize>,
    var_locals: Vec<Local>,
    /// `(variable, argument index)` of each integer formal never written.
    formals: Vec<(usize, u32)>,
}

impl<'a, 'tcx> Ints<'a, 'tcx> {
    fn compute(tcx: TyCtxt<'tcx>, body: &'a Body<'tcx>, shape: &'a Shape) -> IntFacts {
        let consts = constant_locals(tcx, body, shape);
        let tracked = int_slice(tcx, body, shape, &consts);
        let mut vars = FxHashMap::default();
        let mut var_locals = Vec::new();
        for local in tracked {
            vars.insert(local, var_locals.len() + 1);
            var_locals.push(local);
        }
        let formals = var_locals
            .iter()
            .enumerate()
            .filter(|(_, local)| shape.fixed_formal(**local))
            .map(|(index, local)| (index + 1, (local.as_u32() - 1)))
            .collect();
        let ints = Ints {
            tcx,
            body,
            address_taken: &shape.address_taken,
            offset_only: offset_only_locals(tcx, body),
            consts,
            vars,
            var_locals,
            formals,
        };
        let ranges = ints.run();
        let mut defs = FxHashMap::default();
        for local in ints.var_locals.clone() {
            ints.def_range(shape, &ranges, &mut defs, local);
        }
        IntFacts {
            consts: ints.consts,
            ranges,
            defs: defs
                .into_iter()
                .filter_map(|(local, range)| range.map(|range| (local, range)))
                .collect(),
        }
    }

    /// The interval of a product, or of a copy or a value-keeping cast of
    /// one, at its one definition (`IntFacts::defs`).
    fn def_range(
        &self,
        shape: &Shape,
        ranges: &FxHashMap<(Location, Local), IntRange>,
        defs: &mut FxHashMap<Local, Option<IntRange>>,
        x: Local,
    ) -> Option<IntRange> {
        if let Some(known) = defs.get(&x) {
            return known.clone();
        }
        // A cycle has no range: mark it before the definition is read.
        defs.insert(x, None);
        let found = self.def_range_once(shape, ranges, defs, x);
        defs.insert(x, found.clone());
        found
    }

    fn def_range_once(
        &self,
        shape: &Shape,
        ranges: &FxHashMap<(Location, Local), IntRange>,
        defs: &mut FxHashMap<Local, Option<IntRange>>,
        x: Local,
    ) -> Option<IntRange> {
        let location = shape.only_def(x)?;
        let (bits, signed) = int_shape(self.body.local_decls[x].ty)?;
        let range_of = |y: Local, defs: &mut FxHashMap<Local, Option<IntRange>>| {
            if let Some(k) = self.consts.get(&y) {
                return Some(IntRange::exact(*k));
            }
            let def = self.def_range(shape, ranges, defs, y);
            combine(ranges.get(&(location, y)), def.as_ref())
        };
        // `y · c`, `c > 0` a constant, from the operands.
        let product = |left: &Operand<'tcx>, right: &Operand<'tcx>| -> Option<(Local, i64)> {
            let constant = |operand: &Operand<'tcx>| match operand {
                Operand::Constant(_) => constant_value(self.tcx, operand),
                _ => operand_local(operand).and_then(|l| self.consts.get(&l).copied()),
            };
            let (y, c) = match (operand_local(left), constant(right)) {
                (Some(y), Some(c)) if !self.consts.contains_key(&y) => (y, c),
                _ => (operand_local(right)?, constant(left)?),
            };
            (c > 0).then_some((y, c))
        };
        let scaled = |range: IntRange, c: i64, signed: bool| -> Option<IntRange> {
            if signed {
                let mut premises = range.premises.clone();
                premises.insert(Premise::IndexStepNoWrap);
                Some(IntRange {
                    lo: Some(range.lo?.scale(c)?),
                    hi: Some(range.hi?.scale(c)?),
                    premises,
                })
            } else {
                Some(IntRange {
                    lo: Some(Bound::constant(0)),
                    hi: Some(range.hi?.scale(c)?),
                    premises: range.premises,
                })
            }
        };
        match at(self.body, location) {
            At::Statement(statement) => {
                let StatementKind::Assign(box (_, rvalue)) = &statement.kind else {
                    return None;
                };
                match rvalue {
                    Rvalue::BinaryOp(BinOp::Mul | BinOp::MulUnchecked, box (left, right)) => {
                        let (y, c) = product(left, right)?;
                        scaled(range_of(y, defs)?, c, signed)
                    }
                    Rvalue::Use(operand) => {
                        self.def_range(shape, ranges, defs, operand_local(operand)?)
                    }
                    Rvalue::Cast(CastKind::IntToInt, operand, _) => {
                        let y = operand_local(operand)?;
                        let from = int_shape(self.body.local_decls[y].ty)?;
                        let range = self.def_range(shape, ranges, defs, y)?;
                        let constant = |b: Option<Bound>| b.and_then(Bound::as_constant);
                        let premise = cast_keeps(
                            from,
                            (bits, signed),
                            constant(range.lo),
                            constant(range.hi),
                            self.offset_only.contains(&x),
                        )?;
                        let mut range = range;
                        range.premises.extend(premise);
                        Some(range)
                    }
                    _ => None,
                }
            }
            At::Terminator(terminator) => {
                let TerminatorKind::Call { func, args, .. } = &terminator.kind else {
                    return None;
                };
                let def = func.const_fn_def()?.0;
                let core_integer = self.tcx.crate_name(def.krate).as_str() == "core"
                    && self.tcx.def_path_str(def).contains("num::<impl");
                if signed || !core_integer || self.tcx.item_name(def).as_str() != "wrapping_mul" {
                    return None;
                }
                let [left, right] = &args[..] else {
                    return None;
                };
                let (y, c) = product(&left.node, &right.node)?;
                scaled(range_of(y, defs)?, c, false)
            }
        }
    }

    fn var(&self, local: Local) -> Option<usize> {
        self.vars.get(&local).copied()
    }

    fn unsigned(&self, local: Local) -> bool {
        matches!(self.body.local_decls[local].ty.kind(), TyKind::Uint(_))
    }

    fn initial(&self) -> IState {
        let mut dbm = Dbm::top(self.vars.len() + 1);
        for (local, var) in &self.vars {
            if self.unsigned(*local) {
                dbm.constrain(0, *var, 0);
            }
        }
        IState {
            dbm,
            conds: FxHashMap::default(),
            premises: BTreeSet::new(),
        }
    }

    /// The fixpoint, then one recording pass over the converged states.
    fn run(&self) -> FxHashMap<(Location, Local), IntRange> {
        let mut recorded = FxHashMap::default();
        let blocks = self.body.basic_blocks.len();
        let mut entry: Vec<Option<IState>> = vec![None; blocks];
        let mut visits = vec![0usize; blocks];
        // Widening points: the targets of retreating edges in reverse
        // postorder (the loop heads). Every other block joins plainly, so a
        // bound an edge condition sets inside the loop is never widened away.
        let mut order = vec![usize::MAX; blocks];
        for (index, block) in self
            .body
            .basic_blocks
            .reverse_postorder()
            .iter()
            .enumerate()
        {
            order[block.index()] = index;
        }
        let mut head = vec![false; blocks];
        for (block, data) in self.body.basic_blocks.iter_enumerated() {
            for target in data.terminator().successors() {
                if order[target.index()] <= order[block.index()] {
                    head[target.index()] = true;
                }
            }
        }
        entry[0] = Some(self.initial());
        let mut work = vec![BasicBlock::from_u32(0)];
        let mut steps = 0usize;
        while let Some(block) = work.pop() {
            steps += 1;
            if steps > 50_000 {
                // Over budget: only the constants are known.
                return recorded;
            }
            let Some(state) = entry[block.index()].clone() else {
                continue;
            };
            for (target, out) in self.transfer_block(block, state, &mut None) {
                if out.dbm.bottom() {
                    continue;
                }
                let slot = &mut entry[target.index()];
                let next = match slot {
                    None => out,
                    Some(old) => {
                        if out.leq(old) {
                            continue;
                        }
                        visits[target.index()] += 1;
                        old.join(&out, head[target.index()] && visits[target.index()] > 2)
                    }
                };
                *slot = Some(next);
                if !work.contains(&target) {
                    work.push(target);
                }
            }
        }
        for (index, state) in entry.into_iter().enumerate() {
            let Some(state) = state else { continue };
            self.transfer_block(
                BasicBlock::from_usize(index),
                state,
                &mut Some(&mut recorded),
            );
        }
        recorded
    }

    /// Record the interval of every indexing local of `place`.
    fn record_place(
        &self,
        state: &IState,
        location: Location,
        place: &Place<'tcx>,
        recorded: &mut Option<&mut FxHashMap<(Location, Local), IntRange>>,
    ) {
        let Some(recorded) = recorded.as_deref_mut() else {
            return;
        };
        for elem in place.projection.iter() {
            if let PlaceElem::Index(index) = elem
                && let Some(var) = self.var(index)
            {
                recorded.insert((location, index), self.range(state, Term::Var(var)));
            }
        }
    }

    fn record_operand(
        &self,
        state: &IState,
        location: Location,
        operand: &Operand<'tcx>,
        recorded: &mut Option<&mut FxHashMap<(Location, Local), IntRange>>,
    ) {
        if let Operand::Copy(place) | Operand::Move(place) = operand {
            self.record_place(state, location, place, recorded);
            if let Some(local) = place.as_local()
                && let Some(var) = self.var(local)
                && let Some(recorded) = recorded.as_deref_mut()
            {
                recorded.insert((location, local), self.range(state, Term::Var(var)));
            }
        }
    }

    fn record_rvalue(
        &self,
        state: &IState,
        location: Location,
        rvalue: &Rvalue<'tcx>,
        recorded: &mut Option<&mut FxHashMap<(Location, Local), IntRange>>,
    ) {
        match rvalue {
            Rvalue::Use(operand)
            | Rvalue::Cast(_, operand, _)
            | Rvalue::UnaryOp(_, operand)
            | Rvalue::Repeat(operand, _) => {
                if let Operand::Copy(place) | Operand::Move(place) = operand {
                    self.record_place(state, location, place, recorded);
                }
            }
            Rvalue::BinaryOp(op, box (left, right)) => {
                for operand in [left, right] {
                    if let Operand::Copy(place) | Operand::Move(place) = operand {
                        self.record_place(state, location, place, recorded);
                    }
                    // A product's operand, for its range at the definition.
                    if matches!(op, BinOp::Mul | BinOp::MulUnchecked)
                        && let Some(local) = operand_local(operand)
                        && let Some(var) = self.var(local)
                        && let Some(recorded) = recorded.as_deref_mut()
                    {
                        recorded.insert((location, local), self.range(state, Term::Var(var)));
                    }
                }
            }
            Rvalue::Aggregate(_, operands) => {
                for operand in operands {
                    if let Operand::Copy(place) | Operand::Move(place) = operand {
                        self.record_place(state, location, place, recorded);
                    }
                }
            }
            Rvalue::Ref(_, _, place)
            | Rvalue::RawPtr(_, place)
            | Rvalue::CopyForDeref(place)
            | Rvalue::Len(place)
            | Rvalue::Discriminant(place) => self.record_place(state, location, place, recorded),
            _ => {}
        }
    }

    /// The interval of a term, by a constant or by an integer formal.
    fn range(&self, state: &IState, term: Term) -> IntRange {
        let x = match term {
            Term::Const(k) => return IntRange::exact(k),
            Term::Var(x) => x,
        };
        let dbm = &state.dbm;
        let hi = if dbm.get(x, 0) < INF {
            Some(Bound::constant(dbm.get(x, 0)))
        } else {
            self.formals
                .iter()
                .find(|(f, _)| dbm.get(x, *f) < INF)
                .map(|(f, arg)| Bound::of_formal(*arg, dbm.get(x, *f)))
        };
        let lo = if dbm.get(0, x) < INF {
            Some(Bound::constant(-dbm.get(0, x)))
        } else {
            self.formals
                .iter()
                .find(|(f, _)| dbm.get(*f, x) < INF)
                .map(|(f, arg)| Bound::of_formal(*arg, -dbm.get(*f, x)))
        };
        IntRange {
            lo,
            hi,
            premises: state.premises.clone(),
        }
    }

    fn transfer_block(
        &self,
        block: BasicBlock,
        mut state: IState,
        recorded: &mut Option<&mut FxHashMap<(Location, Local), IntRange>>,
    ) -> Vec<(BasicBlock, IState)> {
        let data = &self.body.basic_blocks[block];
        for (statement_index, statement) in data.statements.iter().enumerate() {
            let location = Location {
                block,
                statement_index,
            };
            match &statement.kind {
                StatementKind::Assign(box (place, rvalue)) => {
                    self.record_place(&state, location, place, recorded);
                    self.record_rvalue(&state, location, rvalue, recorded);
                    self.assign(&mut state, place, rvalue);
                }
                StatementKind::StorageLive(local) | StatementKind::StorageDead(local) => {
                    self.kill(&mut state, *local);
                }
                StatementKind::SetDiscriminant { place, .. } | StatementKind::Deinit(place) => {
                    self.record_place(&state, location, place, recorded);
                    if let Some(local) = place.as_local() {
                        self.kill(&mut state, local);
                    }
                }
                _ => {}
            }
        }
        let location = self.body.terminator_loc(block);
        let terminator = data.terminator();
        match &terminator.kind {
            TerminatorKind::Goto { target } => vec![(*target, state)],
            TerminatorKind::SwitchInt { discr, targets } => {
                self.record_operand(&state, location, discr, recorded);
                let cond = operand_local(discr).and_then(|local| state.conds.get(&local).copied());
                let values: Vec<_> = targets.iter().collect();
                let two_way = values.len() == 1 && values[0].0 == 0;
                let mut out = Vec::new();
                for (_, target) in &values {
                    let mut edge = state.clone();
                    if let (Some(cond), true) = (cond, two_way) {
                        self.apply(&mut edge, cond, false);
                    }
                    out.push((*target, edge));
                }
                let mut otherwise = state;
                if let (Some(cond), true) = (cond, two_way) {
                    self.apply(&mut otherwise, cond, true);
                }
                out.push((targets.otherwise(), otherwise));
                out
            }
            TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                ..
            } => {
                for arg in args.iter() {
                    self.record_operand(&state, location, &arg.node, recorded);
                }
                self.record_place(&state, location, destination, recorded);
                self.call(&mut state, func, args, destination);
                target.map(|t| vec![(t, state)]).unwrap_or_default()
            }
            TerminatorKind::Assert {
                cond,
                expected,
                target,
                ..
            } => {
                self.record_operand(&state, location, cond, recorded);
                if let Some(cond) =
                    operand_local(cond).and_then(|local| state.conds.get(&local).copied())
                {
                    self.apply(&mut state, cond, *expected);
                }
                vec![(*target, state)]
            }
            TerminatorKind::Drop { target, place, .. } => {
                self.record_place(&state, location, place, recorded);
                vec![(*target, state)]
            }
            TerminatorKind::FalseEdge { real_target, .. }
            | TerminatorKind::FalseUnwind { real_target, .. } => vec![(*real_target, state)],
            _ => vec![],
        }
    }

    fn kill(&self, state: &mut IState, local: Local) {
        if let Some(var) = self.var(local) {
            state.dbm.forget(var);
            let mentions = |term: Term| matches!(term, Term::Var(v) if v == var);
            state.conds.retain(|held, cond| {
                *held != local && !mentions(cond.left) && !mentions(cond.right)
            });
        } else {
            state.conds.remove(&local);
        }
    }

    fn term(&self, state: &IState, operand: &Operand<'tcx>) -> Option<Term> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                let local = place.as_local()?;
                if let Some(k) = self.consts.get(&local) {
                    return Some(Term::Const(*k));
                }
                let var = self.var(local)?;
                Some(match state.dbm.exact(var) {
                    Some(k) => Term::Const(k),
                    None => Term::Var(var),
                })
            }
            Operand::Constant(_) => constant_value(self.tcx, operand).map(Term::Const),
        }
    }

    fn assign_term(&self, state: &mut IState, x: usize, term: Term, c: i64) {
        match term {
            Term::Var(y) => state.dbm.assign(x, y, c),
            Term::Const(k) => state.dbm.assign(x, 0, k + c),
        }
    }

    /// A comparison's outcome on the edge that takes it.
    fn apply(&self, state: &mut IState, cond: Cond, holds: bool) {
        let var = |term: Term| match term {
            Term::Var(v) => (v, 0),
            Term::Const(k) => (0, k),
        };
        let ((a, ka), (b, kb)) = (var(cond.left), var(cond.right));
        let d = kb - ka;
        let (first, second) = match (cond.op, holds) {
            (BinOp::Lt, true) | (BinOp::Ge, false) => ((a, b, d - 1), None),
            (BinOp::Le, true) | (BinOp::Gt, false) => ((a, b, d), None),
            (BinOp::Gt, true) | (BinOp::Le, false) => ((b, a, -d - 1), None),
            (BinOp::Ge, true) | (BinOp::Lt, false) => ((b, a, -d), None),
            (BinOp::Eq, true) | (BinOp::Ne, false) => ((a, b, d), Some((b, a, -d))),
            // E2, the equality exit: unequal, and already at most (at
            // least) the other side, so strictly below (above) it.
            (BinOp::Eq, false) | (BinOp::Ne, true) => {
                if state.dbm.get(a, b) <= d {
                    state.dbm.constrain(a, b, d - 1);
                }
                if state.dbm.get(b, a) <= -d {
                    state.dbm.constrain(b, a, -d - 1);
                }
                return;
            }
            _ => return,
        };
        state.dbm.constrain(first.0, first.1, first.2);
        if let Some((i, j, c)) = second {
            state.dbm.constrain(i, j, c);
        }
    }

    /// Is `x := term + c` exact? A signed `+` / `-` is when it cannot leave
    /// the type, and otherwise under `§28:index-step-no-wrap` (C's signed
    /// overflow is UB); an unsigned one, and any `wrapping_*` (`proven`), only
    /// when it provably stays in the type.
    fn step_exact(&self, state: &mut IState, x: Local, term: Term, c: i64, proven: bool) -> bool {
        let Some((bits, signed)) = int_shape(self.body.local_decls[x].ty) else {
            return false;
        };
        let (min, max) = type_range(bits, signed);
        match term {
            Term::Const(k) => {
                let v = k as i128 + c as i128;
                if (min..=max).contains(&v) {
                    true
                } else if signed && !proven {
                    state.premises.insert(Premise::IndexStepNoWrap);
                    true
                } else {
                    false
                }
            }
            Term::Var(_) if c == 0 => true,
            Term::Var(_) if signed && !proven => {
                state.premises.insert(Premise::IndexStepNoWrap);
                true
            }
            Term::Var(y) if c < 0 => {
                let lower = state.dbm.get(0, y);
                lower < INF && -(lower as i128) + c as i128 >= min
            }
            Term::Var(y) => {
                let upper = state.dbm.get(y, 0);
                (upper < INF && upper as i128 + c as i128 <= max)
                    || (!signed
                        && self.var_locals.iter().enumerate().any(|(index, local)| {
                            let z = index + 1;
                            z != y
                                && state.dbm.get(y, z) <= -c
                                && int_shape(self.body.local_decls[*local].ty)
                                    .is_some_and(|(width, sign)| width <= bits && !sign)
                        }))
            }
        }
    }

    /// Does the cast keep the value? Widening within a signedness; unsigned
    /// into a wider signed type; signed into unsigned when non-negative; a cast
    /// whose constant bounds fit; and `usize` into `isize` when every use of
    /// the result is the count of `offset` / `add` / `sub` (C's `p + n`: an `n`
    /// past `isize::MAX` would leave the object, UB under §28 —
    /// `§28:usize-as-isize`). Elsewhere `(ssize_t)n` is implementation-defined,
    /// not UB, so it is not assumed (the reviewer's M2).
    fn value_preserving(
        &self,
        state: &mut IState,
        x: Local,
        term: Term,
        from: (u64, bool),
        to: (u64, bool),
    ) -> bool {
        let (lo, hi) = match term {
            Term::Const(k) => (Some(k), Some(k)),
            Term::Var(v) => (
                (state.dbm.get(0, v) < INF).then(|| -state.dbm.get(0, v)),
                (state.dbm.get(v, 0) < INF).then(|| state.dbm.get(v, 0)),
            ),
        };
        match cast_keeps(from, to, lo, hi, self.offset_only.contains(&x)) {
            Some(premise) => {
                state.premises.extend(premise);
                true
            }
            None => false,
        }
    }

    fn assign(&self, state: &mut IState, place: &Place<'tcx>, rvalue: &Rvalue<'tcx>) {
        let Some(x) = place.as_local() else {
            return;
        };
        let Some(x_var) = self.var(x) else {
            // A comparison into a boolean local is a condition, unless the
            // local's address is taken.
            self.kill(state, x);
            if self.address_taken.contains(&x) {
                return;
            }
            if let Rvalue::BinaryOp(
                op @ (BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge | BinOp::Eq | BinOp::Ne),
                box (left, right),
            ) = rvalue
                && let (Some(left), Some(right)) = (self.term(state, left), self.term(state, right))
            {
                state.conds.insert(
                    x,
                    Cond {
                        op: *op,
                        left,
                        right,
                    },
                );
            }
            return;
        };
        enum New {
            Term(Term, i64),
            Range(i64, i64),
            Below(Term),
            Unknown,
        }
        let mut probe = state.clone();
        let new = match rvalue {
            Rvalue::Use(operand) => match self.term(&probe, operand) {
                Some(term) => New::Term(term, 0),
                None => New::Unknown,
            },
            Rvalue::Cast(CastKind::IntToInt, operand, target) => {
                let from = int_shape(operand.ty(&self.body.local_decls, self.tcx));
                match (self.term(&probe, operand), from, int_shape(*target)) {
                    (Some(term), Some(from), Some(to))
                        if self.value_preserving(&mut probe, x, term, from, to) =>
                    {
                        New::Term(term, 0)
                    }
                    _ => New::Unknown,
                }
            }
            Rvalue::BinaryOp(op, box (left, right)) => {
                let (l, r) = (self.term(&probe, left), self.term(&probe, right));
                match op {
                    BinOp::Add | BinOp::AddUnchecked => match (l, r) {
                        (Some(Term::Var(v)), Some(Term::Const(c)))
                        | (Some(Term::Const(c)), Some(Term::Var(v))) => New::Term(Term::Var(v), c),
                        (Some(Term::Const(a)), Some(Term::Const(b))) => {
                            New::Term(Term::Const(a + b), 0)
                        }
                        _ => New::Unknown,
                    },
                    BinOp::Sub | BinOp::SubUnchecked => match (l, r) {
                        (Some(Term::Var(v)), Some(Term::Const(c))) => New::Term(Term::Var(v), -c),
                        (Some(Term::Const(a)), Some(Term::Const(b))) => {
                            New::Term(Term::Const(a - b), 0)
                        }
                        _ => New::Unknown,
                    },
                    // `v · c` with `c > 0` and `v` between two constants.
                    BinOp::Mul | BinOp::MulUnchecked => match (l, r) {
                        (Some(Term::Const(a)), Some(Term::Const(b))) => match a.checked_mul(b) {
                            Some(p) => New::Term(Term::Const(p), 0),
                            None => New::Unknown,
                        },
                        (Some(Term::Var(v)), Some(Term::Const(c)))
                        | (Some(Term::Const(c)), Some(Term::Var(v)))
                            if c > 0 && probe.dbm.get(v, 0) < INF && probe.dbm.get(0, v) < INF =>
                        {
                            let (lo, hi) = (-probe.dbm.get(0, v), probe.dbm.get(v, 0));
                            match (lo.checked_mul(c), hi.checked_mul(c)) {
                                (Some(lo), Some(hi)) => New::Range(lo, hi),
                                _ => New::Unknown,
                            }
                        }
                        _ => New::Unknown,
                    },
                    // Unsigned `a & m`: at most each non-negative operand.
                    BinOp::BitAnd if self.unsigned(x) => match (l, r) {
                        (Some(Term::Const(m)), Some(t)) | (Some(t), Some(Term::Const(m)))
                            if m >= 0 =>
                        {
                            let _ = t;
                            New::Below(Term::Const(m))
                        }
                        _ => New::Unknown,
                    },
                    _ => New::Unknown,
                }
            }
            _ => New::Unknown,
        };
        let new = match new {
            New::Term(term, c) if !self.step_exact(&mut probe, x, term, c, false) => New::Unknown,
            New::Range(lo, hi) => {
                // A product is exact under §28 when signed, and provably in
                // range when unsigned.
                match int_shape(self.body.local_decls[x].ty) {
                    Some((_, true)) => {
                        probe.premises.insert(Premise::IndexStepNoWrap);
                        New::Range(lo, hi)
                    }
                    Some((bits, false)) if (hi as i128) <= type_range(bits, false).1 => {
                        New::Range(lo, hi)
                    }
                    _ => New::Unknown,
                }
            }
            other => other,
        };
        state.premises = probe.premises;
        match new {
            New::Term(Term::Var(y), c) if y == x_var => {
                let mentions = |term: Term| matches!(term, Term::Var(v) if v == y);
                state
                    .conds
                    .retain(|_, cond| !mentions(cond.left) && !mentions(cond.right));
                state.dbm.assign(y, y, c);
            }
            New::Term(term, c) => {
                self.kill(state, x);
                self.assign_term(state, x_var, term, c);
            }
            New::Range(lo, hi) => {
                self.kill(state, x);
                state.dbm.constrain(x_var, 0, hi);
                state.dbm.constrain(0, x_var, -lo);
            }
            New::Below(Term::Const(m)) => {
                self.kill(state, x);
                state.dbm.constrain(x_var, 0, m);
            }
            New::Below(_) | New::Unknown => self.kill(state, x),
        }
        if self.unsigned(x) {
            state.dbm.constrain(0, x_var, 0);
        }
    }

    /// `wrapping_add` / `wrapping_sub` by a constant on an integer (core's
    /// integer methods); every other call's destination is forgotten.
    fn call(
        &self,
        state: &mut IState,
        func: &Operand<'tcx>,
        args: &[rustc_span::source_map::Spanned<Operand<'tcx>>],
        destination: &Place<'tcx>,
    ) {
        let Some(dest) = destination.as_local() else {
            return;
        };
        let callee = func.const_fn_def().map(|(def, _)| def);
        let integer_step = callee.and_then(|def| {
            let path = self.tcx.def_path_str(def);
            (self.tcx.crate_name(def.krate).as_str() == "core" && path.contains("num::<impl"))
                .then(|| self.tcx.item_name(def))
        });
        let dest_var = self.var(dest);
        // The new value, against the state before the destination changes.
        let new = match (integer_step, dest_var, args) {
            (Some(name), Some(_), [left, right]) => {
                let sign = match name.as_str() {
                    "wrapping_add" => Some(1),
                    "wrapping_sub" => Some(-1),
                    _ => None,
                };
                sign.and_then(|sign| {
                    let (l, r) = (self.term(state, &left.node), self.term(state, &right.node));
                    let (term, c) = match (l, r) {
                        (Some(term), Some(Term::Const(c))) => (term, sign * c),
                        (Some(Term::Const(c)), Some(term)) if sign == 1 => (term, c),
                        _ => return None,
                    };
                    let mut probe = state.clone();
                    self.step_exact(&mut probe, dest, term, c, true).then_some((
                        term,
                        c,
                        probe.premises,
                    ))
                })
            }
            _ => None,
        };
        match (new, dest_var) {
            (Some((Term::Var(y), c, premises)), Some(x)) if y == x => {
                state.premises = premises;
                let mentions = |term: Term| matches!(term, Term::Var(v) if v == x);
                state
                    .conds
                    .retain(|_, cond| !mentions(cond.left) && !mentions(cond.right));
                state.dbm.assign(x, x, c);
            }
            (Some((term, c, premises)), Some(x)) => {
                state.premises = premises;
                self.kill(state, dest);
                self.assign_term(state, x, term, c);
            }
            _ => self.kill(state, dest),
        }
        if let Some(x) = dest_var
            && self.unsigned(dest)
        {
            state.dbm.constrain(0, x, 0);
        }
    }
}

/// Locals whose every use is the count of a core `offset` / `add` / `sub`.
fn offset_only_locals<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> FxHashSet<Local> {
    use rustc_middle::mir::visit::{PlaceContext, Visitor};
    struct Uses(FxHashMap<Local, usize>);
    impl<'tcx> Visitor<'tcx> for Uses {
        fn visit_local(&mut self, local: Local, context: PlaceContext, _: Location) {
            if context.is_use() && !context.is_mutating_use() && !context.is_storage_marker() {
                *self.0.entry(local).or_default() += 1;
            }
        }
    }
    let mut uses = Uses(FxHashMap::default());
    uses.visit_body(body);
    let mut counts: FxHashMap<Local, usize> = FxHashMap::default();
    for data in body.basic_blocks.iter() {
        let terminator = data.terminator();
        if let TerminatorKind::Call { args, .. } = &terminator.kind
            && let Some(call) = terminator.as_call(tcx)
            && core_pointer_step(tcx, &call.func).is_some()
            && let Some(count) = args.get(1).and_then(|arg| operand_local(&arg.node))
        {
            *counts.entry(count).or_default() += 1;
        }
    }
    counts
        .into_iter()
        .filter(|(local, n)| uses.0.get(local) == Some(n))
        .map(|(local, _)| local)
        .collect()
}

/// Does a cast from `from` to `to` keep a value in `[lo, hi]` (the bounds
/// when constant)? `Some` with the §28 use it rests on, if any
/// (`Ints::value_preserving`).
fn cast_keeps(
    from: (u64, bool),
    to: (u64, bool),
    lo: Option<i64>,
    hi: Option<i64>,
    offset_only: bool,
) -> Option<Option<Premise>> {
    let fits = |bits: u64, signed: bool| {
        let (min, max) = type_range(bits, signed);
        lo.is_some_and(|lo| lo as i128 >= min) && hi.is_some_and(|hi| hi as i128 <= max)
    };
    match (from.1, to.1) {
        (false, false) | (true, true) if to.0 >= from.0 => Some(None),
        (false, true) if to.0 > from.0 => Some(None),
        (true, false) if to.0 >= from.0 && lo.is_some_and(|lo| lo >= 0) => Some(None),
        _ if fits(to.0, to.1) => Some(None),
        (false, true) if to.0 == from.0 && to.0 == 64 && offset_only => {
            Some(Some(Premise::UsizeAsIsize))
        }
        _ => None,
    }
}

/// The values an integer type holds, `[min, max]` (128-bit types clipped to
/// `i128`).
fn type_range(bits: u64, signed: bool) -> (i128, i128) {
    match (bits >= 128, signed) {
        (true, true) => (i128::MIN, i128::MAX),
        (true, false) => (0, i128::MAX),
        (false, true) => (-(1i128 << (bits - 1)), (1i128 << (bits - 1)) - 1),
        (false, false) => (0, (1i128 << bits) - 1),
    }
}

/// An integer constant operand's value.
fn constant_value<'tcx>(tcx: TyCtxt<'tcx>, operand: &Operand<'tcx>) -> Option<i64> {
    let Operand::Constant(constant) = operand else {
        return None;
    };
    let (bits, signed) = int_shape(constant.ty())?;
    let raw = constant
        .const_
        .try_eval_bits(tcx, ty::TypingEnv::fully_monomorphized())?;
    let value: i128 = if !signed {
        i128::try_from(raw).ok()?
    } else if bits < 128 && (raw >> (bits - 1)) & 1 == 1 {
        raw as i128 - (1i128 << bits)
    } else {
        raw as i128
    };
    i64::try_from(value)
        .ok()
        .filter(|v| v.unsigned_abs() < LIMIT as u64)
}

/// Integer locals with one definition, a constant one: a literal, a `const`
/// item, a value-keeping cast or the sum, difference or product of constants.
fn constant_locals<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    shape: &Shape,
) -> FxHashMap<Local, i64> {
    let mut consts: FxHashMap<Local, i64> = FxHashMap::default();
    loop {
        let mut changed = false;
        for (local, decl) in body.local_decls.iter_enumerated() {
            if consts.contains_key(&local) || int_shape(decl.ty).is_none() {
                continue;
            }
            let Some(location) = shape.only_def(local) else {
                continue;
            };
            let At::Statement(statement) = at(body, location) else {
                continue;
            };
            let StatementKind::Assign(box (_, rvalue)) = &statement.kind else {
                continue;
            };
            let value = |operand: &Operand<'tcx>| match operand {
                Operand::Constant(_) => constant_value(tcx, operand),
                _ => operand_local(operand).and_then(|l| consts.get(&l).copied()),
            };
            let fits = |v: i64| {
                let (bits, signed) = int_shape(decl.ty).expect("an integer local");
                let (min, max) = type_range(bits, signed);
                (min..=max).contains(&(v as i128))
            };
            let new = match rvalue {
                Rvalue::Use(operand) | Rvalue::Cast(CastKind::IntToInt, operand, _) => {
                    value(operand)
                }
                Rvalue::BinaryOp(op, box (left, right)) => match (value(left), value(right)) {
                    (Some(a), Some(b)) => match op {
                        BinOp::Add | BinOp::AddUnchecked => a.checked_add(b),
                        BinOp::Sub | BinOp::SubUnchecked => a.checked_sub(b),
                        BinOp::Mul | BinOp::MulUnchecked => a.checked_mul(b),
                        BinOp::Div if b != 0 => a.checked_div(b),
                        BinOp::Rem if b != 0 => a.checked_rem(b),
                        _ => None,
                    },
                    _ => None,
                },
                _ => None,
            };
            if let Some(v) = new.filter(|v| fits(*v) && v.unsigned_abs() < LIMIT as u64) {
                consts.insert(local, v);
                changed = true;
            }
        }
        if !changed {
            return consts;
        }
    }
}

/// The integer locals the facts track: those that index a place, step a
/// pointer, reach a local callee or a libc row's length, or meet a comparison,
/// closed over their definitions; never a constant or an addressed local.
fn int_slice<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    shape: &Shape,
    consts: &FxHashMap<Local, i64>,
) -> Vec<Local> {
    let trackable = |local: Local| {
        int_shape(body.local_decls[local].ty).is_some()
            && !consts.contains_key(&local)
            && !shape.address_taken.contains(&local)
    };
    let mut seeds: Vec<Local> = Vec::new();
    let seed_place = |place: &Place<'tcx>, seeds: &mut Vec<Local>| {
        for elem in place.projection.iter() {
            if let PlaceElem::Index(index) = elem {
                seeds.push(index);
            }
        }
    };
    for data in body.basic_blocks.iter() {
        for statement in &data.statements {
            if let StatementKind::Assign(box (place, rvalue)) = &statement.kind {
                seed_place(place, &mut seeds);
                match rvalue {
                    Rvalue::BinaryOp(
                        BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge | BinOp::Eq | BinOp::Ne,
                        box (left, right),
                    ) => {
                        seeds.extend(operand_local(left));
                        seeds.extend(operand_local(right));
                    }
                    Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
                    | Rvalue::Cast(_, Operand::Copy(p) | Operand::Move(p), _)
                    | Rvalue::Ref(_, _, p)
                    | Rvalue::RawPtr(_, p)
                    | Rvalue::CopyForDeref(p) => seed_place(p, &mut seeds),
                    _ => {}
                }
            }
        }
        let terminator = data.terminator();
        if let TerminatorKind::Call { args, .. } = &terminator.kind
            && let Some(call) = terminator.as_call(tcx)
        {
            let local_callee = matches!(call.func, CallKind::FreeStanding(_) | CallKind::Impl(_));
            for (k, arg) in args.iter().enumerate() {
                if let Operand::Copy(p) | Operand::Move(p) = &arg.node {
                    seed_place(p, &mut seeds);
                }
                let seeded = local_callee
                    || (k == 1 && core_pointer_step(tcx, &call.func).is_some())
                    || libc_row(&call.func).is_some_and(|(_, _, length)| k == length);
                if seeded {
                    seeds.extend(operand_local(&arg.node));
                }
            }
        }
    }
    let mut tracked: Vec<Local> = Vec::new();
    let mut seen = FxHashSet::default();
    let mut work: Vec<Local> = seeds.into_iter().filter(|l| trackable(*l)).collect();
    while let Some(local) = work.pop() {
        if !seen.insert(local) {
            continue;
        }
        tracked.push(local);
        for location in shape.defs.get(&local).into_iter().flatten() {
            match at(body, *location) {
                At::Statement(statement) => {
                    if let StatementKind::Assign(box (_, rvalue)) = &statement.kind {
                        let operands: Vec<&Operand<'tcx>> = match rvalue {
                            Rvalue::Use(o) | Rvalue::Cast(_, o, _) | Rvalue::UnaryOp(_, o) => {
                                vec![o]
                            }
                            Rvalue::BinaryOp(_, box (a, b)) => vec![a, b],
                            _ => vec![],
                        };
                        for operand in operands {
                            if let Some(source) = operand_local(operand)
                                && trackable(source)
                            {
                                work.push(source);
                            }
                        }
                    }
                }
                At::Terminator(terminator) => {
                    if let TerminatorKind::Call { args, .. } = &terminator.kind {
                        for arg in args.iter() {
                            if let Some(source) = operand_local(&arg.node)
                                && trackable(source)
                            {
                                work.push(source);
                            }
                        }
                    }
                }
            }
        }
    }
    if tracked.len() > MAX_TRACKED {
        return Vec::new();
    }
    tracked.sort();
    tracked
}

// ---------------------------------------------------------------------------
// The pointer facts: derivations, uses and families.
// ---------------------------------------------------------------------------

/// How a place or a pointer value is used at one point.
#[derive(Clone, Debug)]
enum Use<'tcx> {
    /// `*from…` read or written: its bytes.
    Bytes {
        place: Place<'tcx>,
        write: bool,
    },
    /// The value (or `&(*from).f`) lands in `dest`.
    Flow {
        dest: Place<'tcx>,
    },
    /// The whole value is argument `k` of the point's call.
    Arg {
        k: usize,
    },
    /// Read and dropped: a comparison, `PtrMetadata`.
    Inert,
    Escape(&'static str),
}

/// One use of a pointer local, with the place the engine checks for it.
#[derive(Clone, Debug)]
struct Occ<'tcx> {
    accessed: Place<'tcx>,
    from: Local,
    what: Use<'tcx>,
}

fn is_pointer<'tcx>(body: &Body<'tcx>, local: Local) -> bool {
    pointee(body.local_decls[local].ty).is_some()
}

/// Every use of a pointer local at `location`.
fn occurrences<'tcx>(body: &Body<'tcx>, location: Location) -> Vec<Occ<'tcx>> {
    let mut out = Vec::new();
    let deref_first = |place: &Place<'tcx>| place.projection.first() == Some(&PlaceElem::Deref);
    // A place read: `*p…` by its bytes; a whole pointer by `whole`.
    let read = |place: &Place<'tcx>, whole: Use<'tcx>, out: &mut Vec<Occ<'tcx>>| {
        if deref_first(place) {
            out.push(Occ {
                accessed: *place,
                from: place.local,
                what: Use::Bytes {
                    place: *place,
                    write: false,
                },
            });
        } else if place.projection.is_empty() && is_pointer(body, place.local) {
            out.push(Occ {
                accessed: *place,
                from: place.local,
                what: whole,
            });
        }
    };
    let write = |place: &Place<'tcx>, out: &mut Vec<Occ<'tcx>>| {
        if deref_first(place) {
            out.push(Occ {
                accessed: *place,
                from: place.local,
                what: Use::Bytes {
                    place: *place,
                    write: true,
                },
            });
        }
    };
    match at(body, location) {
        At::Statement(statement) => match &statement.kind {
            StatementKind::Assign(box (lhs, rvalue)) => {
                write(lhs, &mut out);
                let flow = Use::Flow { dest: *lhs };
                match rvalue {
                    Rvalue::Use(operand) => {
                        if let Operand::Copy(p) | Operand::Move(p) = operand {
                            read(p, flow, &mut out);
                        }
                    }
                    Rvalue::Cast(kind, operand, _) => {
                        let keeps = matches!(
                            kind,
                            CastKind::PtrToPtr
                                | CastKind::PointerCoercion(
                                    PointerCoercion::Unsize
                                        | PointerCoercion::MutToConstPointer
                                        | PointerCoercion::ArrayToPointer,
                                    _
                                )
                        );
                        if let Operand::Copy(p) | Operand::Move(p) = operand {
                            read(p, if keeps { flow } else { Use::Escape("cast") }, &mut out);
                        }
                    }
                    Rvalue::Repeat(operand, _) => {
                        if let Operand::Copy(p) | Operand::Move(p) = operand {
                            read(p, Use::Escape("repeat"), &mut out);
                        }
                    }
                    Rvalue::UnaryOp(op, operand) => {
                        if let Operand::Copy(p) | Operand::Move(p) = operand {
                            let what = if *op == UnOp::PtrMetadata {
                                Use::Inert
                            } else {
                                Use::Escape("unary")
                            };
                            read(p, what, &mut out);
                        }
                    }
                    Rvalue::BinaryOp(op, box (left, right)) => {
                        let compare = matches!(
                            op,
                            BinOp::Eq
                                | BinOp::Ne
                                | BinOp::Lt
                                | BinOp::Le
                                | BinOp::Gt
                                | BinOp::Ge
                                | BinOp::Cmp
                        );
                        for operand in [left, right] {
                            if let Operand::Copy(p) | Operand::Move(p) = operand {
                                let what = if compare {
                                    Use::Inert
                                } else {
                                    Use::Escape("arithmetic")
                                };
                                read(p, what, &mut out);
                            }
                        }
                    }
                    Rvalue::Aggregate(_, operands) => {
                        for operand in operands {
                            if let Operand::Copy(p) | Operand::Move(p) = operand {
                                read(p, Use::Escape("aggregate"), &mut out);
                            }
                        }
                    }
                    Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => {
                        if deref_first(place) {
                            out.push(Occ {
                                accessed: *place,
                                from: place.local,
                                what: flow,
                            });
                        } else if is_pointer(body, place.local) {
                            out.push(Occ {
                                accessed: *place,
                                from: place.local,
                                what: Use::Escape("address-taken"),
                            });
                        }
                    }
                    Rvalue::CopyForDeref(place) => read(place, flow, &mut out),
                    Rvalue::Len(place) | Rvalue::Discriminant(place) => {
                        read(place, Use::Inert, &mut out)
                    }
                    Rvalue::ShallowInitBox(operand, _) | Rvalue::WrapUnsafeBinder(operand, _) => {
                        if let Operand::Copy(p) | Operand::Move(p) = operand {
                            read(p, Use::Escape("box"), &mut out);
                        }
                    }
                    _ => {}
                }
            }
            StatementKind::SetDiscriminant { place, .. } | StatementKind::Deinit(place) => {
                write(place, &mut out)
            }
            StatementKind::Intrinsic(box NonDivergingIntrinsic::Assume(operand)) => {
                if let Operand::Copy(p) | Operand::Move(p) = operand {
                    read(p, Use::Inert, &mut out);
                }
            }
            StatementKind::Intrinsic(box NonDivergingIntrinsic::CopyNonOverlapping(copy)) => {
                for operand in [&copy.src, &copy.dst, &copy.count] {
                    if let Operand::Copy(p) | Operand::Move(p) = operand {
                        read(p, Use::Escape("copy-nonoverlapping"), &mut out);
                    }
                }
            }
            _ => {}
        },
        At::Terminator(terminator) => match &terminator.kind {
            TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } => {
                // A function pointer read out of the base is a pointer read.
                if let Operand::Copy(p) | Operand::Move(p) = func {
                    read(p, Use::Escape("called-pointer"), &mut out);
                }
                for (k, arg) in args.iter().enumerate() {
                    if let Operand::Copy(p) | Operand::Move(p) = &arg.node {
                        read(p, Use::Arg { k }, &mut out);
                    }
                }
                write(destination, &mut out);
            }
            TerminatorKind::TailCall { args, .. } => {
                for arg in args.iter() {
                    if let Operand::Copy(p) | Operand::Move(p) = &arg.node {
                        read(p, Use::Escape("tail-call"), &mut out);
                    }
                }
            }
            TerminatorKind::SwitchInt { discr: operand, .. }
            | TerminatorKind::Assert { cond: operand, .. } => {
                if let Operand::Copy(p) | Operand::Move(p) = operand {
                    read(p, Use::Inert, &mut out);
                }
            }
            TerminatorKind::Drop { place, .. } => {
                if deref_first(place) {
                    out.push(Occ {
                        accessed: *place,
                        from: place.local,
                        what: Use::Escape("drop"),
                    });
                }
            }
            TerminatorKind::InlineAsm { operands, .. } => {
                use rustc_middle::mir::InlineAsmOperand as A;
                for operand in operands.iter() {
                    let place = match operand {
                        A::In { value, .. } => match value {
                            Operand::Copy(p) | Operand::Move(p) => Some(*p),
                            Operand::Constant(_) => None,
                        },
                        A::Out { place, .. } => *place,
                        A::InOut { in_value, .. } => match in_value {
                            Operand::Copy(p) | Operand::Move(p) => Some(*p),
                            Operand::Constant(_) => None,
                        },
                        _ => None,
                    };
                    if let Some(place) = place
                        && is_pointer(body, place.local)
                    {
                        out.push(Occ {
                            accessed: place,
                            from: place.local,
                            what: Use::Escape("asm"),
                        });
                    }
                }
            }
            _ => {}
        },
    }
    out
}

/// The pointer facts of one function under construction, or read back.
struct Ctx<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    function: LocalDefId,
    env: ty::TypingEnv<'tcx>,
    shape: &'a Shape,
    ints: &'a IntFacts,
    holders: &'a FxHashSet<Local>,
    derivs: &'a FxHashMap<Local, Deriv>,
    families: &'a RefCell<FxHashMap<Local, Footprint>>,
    holder_paths: &'a RefCell<FxHashMap<(Local, i64), Footprint>>,
    /// Families being computed (a cycle is Unknown).
    open: RefCell<FxHashSet<Local>>,
    /// The paths of roots already walked (E1).
    paths: RefCell<FxHashMap<Local, Path>>,
    /// Every use of a pointer local, by local (the families' input).
    uses: Option<&'a FxHashMap<Local, Vec<(Location, Occ<'tcx>)>>>,
    table: &'a IndexRanges,
}

impl<'a, 'tcx> Ctx<'a, 'tcx> {
    /// A read-back context over finished facts (the discharge).
    fn new(
        tcx: TyCtxt<'tcx>,
        body: &'a Body<'tcx>,
        function: LocalDefId,
        facts: &'a FnFacts,
        table: &'a IndexRanges,
    ) -> Ctx<'a, 'tcx> {
        // The families and the holders' paths are complete: the cells are
        // only read.
        Ctx {
            tcx,
            body,
            function,
            env: ty::TypingEnv::post_analysis(tcx, function),
            shape: &facts.shape,
            ints: &facts.ints,
            holders: &facts.holders,
            derivs: &facts.derivs,
            families: &facts.families,
            holder_paths: &facts.holder_paths,
            open: RefCell::new(FxHashSet::default()),
            paths: RefCell::new(FxHashMap::default()),
            uses: None,
            table,
        }
    }

    /// Does a value of `ty` hold a pointer (a raw pointer, a reference or a
    /// function pointer), within `depth` levels of fields and elements? Past
    /// the depth, an aggregate counts as holding one.
    fn holds_pointer(&self, ty: Ty<'tcx>, depth: u32) -> bool {
        match ty.kind() {
            TyKind::RawPtr(..) | TyKind::Ref(..) | TyKind::FnPtr(..) => true,
            TyKind::Array(element, _) | TyKind::Slice(element) => {
                depth == 0 || self.holds_pointer(*element, depth - 1)
            }
            TyKind::Tuple(elements) => {
                depth == 0 || elements.iter().any(|t| self.holds_pointer(t, depth - 1))
            }
            TyKind::Adt(def, args) => {
                depth == 0
                    || def
                        .all_fields()
                        .any(|field| self.holds_pointer(field.ty(self.tcx, args), depth - 1))
            }
            TyKind::Bool
            | TyKind::Char
            | TyKind::Int(_)
            | TyKind::Uint(_)
            | TyKind::Float(_)
            | TyKind::Never => false,
            _ => true,
        }
    }

    fn size_of(&self, ty: Ty<'tcx>) -> Option<i64> {
        let layout = self.tcx.layout_of(self.env.as_query_input(ty)).ok()?;
        if layout.is_unsized() {
            return None;
        }
        i64::try_from(layout.size.bytes()).ok()
    }

    /// The offsets `[lo, hi]` (inclusive) of the first byte of `*p.proj` from
    /// `*p`, the size it touches (`None` when unsized), and whether it stops at
    /// a second deref (a pointer read out of the object).
    fn place_offset(
        &self,
        place: &Place<'tcx>,
        location: Location,
    ) -> Option<(Bound, Bound, Option<i64>, bool, BTreeSet<Premise>)> {
        self.place_offset_from(place, 1, location)
    }

    /// The same, from the object the first `start` projections reach: 1 for
    /// `*p.proj`, 0 for a holder's own `s.proj` (E1).
    fn place_offset_from(
        &self,
        place: &Place<'tcx>,
        start: usize,
        location: Location,
    ) -> Option<(Bound, Bound, Option<i64>, bool, BTreeSet<Premise>)> {
        let mut ty = PlaceRef {
            local: place.local,
            projection: &place.projection[..start],
        }
        .ty(self.body, self.tcx)
        .ty;
        let (mut lo, mut hi) = (Bound::constant(0), Bound::constant(0));
        let mut premises = BTreeSet::new();
        for elem in place.projection[start..].iter().copied() {
            match elem {
                PlaceElem::Deref => {
                    return Some((lo, hi, self.size_of(ty), true, premises));
                }
                PlaceElem::Field(field, field_ty) => {
                    let adt_ok = match ty.kind() {
                        TyKind::Adt(def, _) => def.is_struct() || def.is_union(),
                        TyKind::Tuple(_) => true,
                        _ => false,
                    };
                    if !adt_ok {
                        return None;
                    }
                    let layout = self.tcx.layout_of(self.env.as_query_input(ty)).ok()?;
                    let offset = i64::try_from(layout.fields.offset(field.index()).bytes()).ok()?;
                    lo = lo.plus(Bound::constant(offset))?;
                    hi = hi.plus(Bound::constant(offset))?;
                    ty = field_ty;
                }
                PlaceElem::Index(index) => {
                    let element = ty.builtin_index()?;
                    let size = self.size_of(element)?;
                    let range = self.ints.range(location, index)?;
                    lo = lo.plus(range.lo?.scale(size)?)?;
                    hi = hi.plus(range.hi?.scale(size)?)?;
                    premises.extend(range.premises.iter().copied());
                    ty = element;
                }
                PlaceElem::ConstantIndex {
                    offset,
                    from_end: false,
                    ..
                } => {
                    let element = ty.builtin_index()?;
                    let size = self.size_of(element)?;
                    let bytes = i64::try_from(offset).ok()?.checked_mul(size)?;
                    lo = lo.plus(Bound::constant(bytes))?;
                    hi = hi.plus(Bound::constant(bytes))?;
                    ty = element;
                }
                PlaceElem::Subtype(next) | PlaceElem::OpaqueCast(next) => ty = next,
                _ => return None,
            }
        }
        Some((lo, hi, self.size_of(ty), false, premises))
    }

    /// A pointer local's value, from its one definition.
    fn derive(&self, local: Local, derivs: &mut FxHashMap<Local, Option<Deriv>>) -> Option<Deriv> {
        if let Some(known) = derivs.get(&local) {
            return known.clone();
        }
        // A cycle has no value: mark it before the definition is read.
        derivs.insert(local, None);
        let found = self.derive_once(local, derivs);
        derivs.insert(local, found.clone());
        found
    }

    fn derive_once(
        &self,
        local: Local,
        derivs: &mut FxHashMap<Local, Option<Deriv>>,
    ) -> Option<Deriv> {
        let ty = self.body.local_decls[local].ty;
        pointee(ty)?;
        if self.shape.fixed_formal(local) {
            return Some(Deriv {
                root: local,
                lo: Bound::constant(0),
                hi: Bound::constant(0),
                premises: BTreeSet::new(),
            });
        }
        let location = self.shape.only_def(local)?;
        match at(self.body, location) {
            At::Statement(statement) => {
                let StatementKind::Assign(box (_, rvalue)) = &statement.kind else {
                    return None;
                };
                match rvalue {
                    Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
                    | Rvalue::CopyForDeref(p)
                    | Rvalue::Cast(
                        CastKind::PtrToPtr
                        | CastKind::PointerCoercion(
                            PointerCoercion::Unsize
                            | PointerCoercion::MutToConstPointer
                            | PointerCoercion::ArrayToPointer,
                            _,
                        ),
                        Operand::Copy(p) | Operand::Move(p),
                        _,
                    ) if p.projection.is_empty() => self.derive(p.local, derivs),
                    Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place)
                        if place.projection.first() == Some(&PlaceElem::Deref) =>
                    {
                        let base = self.derive(place.local, derivs)?;
                        let (lo, hi, _, through, premises) = self.place_offset(place, location)?;
                        if through {
                            return None;
                        }
                        Some(Deriv {
                            root: base.root,
                            lo: base.lo.plus(lo)?,
                            hi: base.hi.plus(hi)?,
                            premises: base.premises.union(&premises).copied().collect(),
                        })
                    }
                    // A pointer loaded from memory is the root of its own
                    // family (E1's loads; R2: never a base).
                    Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
                    | Rvalue::CopyForDeref(p)
                    | Rvalue::Cast(
                        CastKind::PtrToPtr
                        | CastKind::PointerCoercion(
                            PointerCoercion::Unsize
                            | PointerCoercion::MutToConstPointer
                            | PointerCoercion::ArrayToPointer,
                            _,
                        ),
                        Operand::Copy(p) | Operand::Move(p),
                        _,
                    ) if pointee(p.ty(self.body, self.tcx).ty).is_some() => Some(Deriv {
                        root: local,
                        lo: Bound::constant(0),
                        hi: Bound::constant(0),
                        premises: BTreeSet::new(),
                    }),
                    // A holder's address (E1): the holder is the root.
                    Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place)
                        if self.holders.contains(&place.local)
                            && !place.projection.contains(&PlaceElem::Deref) =>
                    {
                        let (lo, hi, _, _, premises) =
                            self.place_offset_from(place, 0, location)?;
                        Some(Deriv {
                            root: place.local,
                            lo,
                            hi,
                            premises,
                        })
                    }
                    _ => None,
                }
            }
            At::Terminator(terminator) => {
                let TerminatorKind::Call { func, args, .. } = &terminator.kind else {
                    return None;
                };
                let call = terminator.as_call(self.tcx)?;
                let receiver = args.first().and_then(|arg| match &arg.node {
                    Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => Some(p.local),
                    _ => None,
                })?;
                if let Some(backwards) = core_pointer_step(self.tcx, &call.func) {
                    let base = self.derive(receiver, derivs)?;
                    let element = pointee(self.body.local_decls[receiver].ty)?;
                    let size = self.size_of(element)?;
                    let step = match &args.get(1)?.node {
                        operand @ Operand::Constant(_) => {
                            IntRange::exact(constant_value(self.tcx, operand)?)
                        }
                        operand => self.ints.range(location, operand_local(operand)?)?,
                    };
                    let (mut lo, mut hi) = (step.lo?.scale(size)?, step.hi?.scale(size)?);
                    if backwards {
                        (lo, hi) = (hi.scale(-1)?, lo.scale(-1)?);
                    }
                    let mut premises = base.premises.clone();
                    premises.extend(step.premises.iter().copied());
                    premises.insert(Premise::InBoundsOffset);
                    return Some(Deriv {
                        root: base.root,
                        lo: base.lo.plus(lo)?,
                        hi: base.hi.plus(hi)?,
                        premises,
                    });
                }
                if core_slice_buffer(self.tcx, self.body, func) || libc_row(&call.func).is_some() {
                    return self.derive(receiver, derivs);
                }
                None
            }
        }
    }

    /// The footprint one use contributes, relative to its local's base.
    fn footprint_of(&self, occ: &Occ<'tcx>, location: Location) -> Footprint {
        let Some(deriv) = self.derivs.get(&occ.from) else {
            return Footprint::Unknown("no-base");
        };
        match &occ.what {
            Use::Bytes { place, write } => {
                let Some((lo, hi, Some(size), through, premises)) =
                    self.place_offset(place, location)
                else {
                    return Footprint::Unknown("place-unbounded");
                };
                // A pointer read out of the base reaches memory its ranges do not
                // describe: two such pointers may meet outside the base.
                if through || (!*write && self.holds_pointer(place.ty(self.body, self.tcx).ty, 4)) {
                    return Footprint::Unknown("loads-a-pointer");
                }
                let (Some(lo), Some(hi)) = (
                    deriv.lo.plus(lo),
                    deriv
                        .hi
                        .plus(hi)
                        .and_then(|h| h.plus(Bound::constant(size))),
                ) else {
                    return Footprint::Unknown("two-formals");
                };
                let mut all = deriv.premises.clone();
                all.extend(premises);
                Footprint::bytes(lo, hi, *write && !through, all)
            }
            Use::Flow { dest } => self.flow(deriv, dest),
            Use::Arg { k } => self.argument(deriv, *k, location),
            Use::Inert => Footprint::Empty,
            Use::Escape(why) => Footprint::Unknown(why),
        }
    }

    /// A value landing in `dest`: that local's family, when it is the same
    /// base; a holder's field's path (E1), shifted by the value's offset.
    fn flow(&self, deriv: &Deriv, dest: &Place<'tcx>) -> Footprint {
        match dest.as_local() {
            Some(RETURN_PLACE) => Footprint::Unknown("returned"),
            Some(dest) => match self.derivs.get(&dest) {
                Some(next) if next.root == deriv.root => self.family(dest),
                _ => Footprint::Unknown("flows-into-untracked"),
            },
            None => match self.holder_field(dest) {
                Some((holder, off, size)) => {
                    self.holder_path(holder, off, size)
                        .shift(deriv.lo, deriv.hi, &deriv.premises)
                }
                None => Footprint::Unknown("stored"),
            },
        }
    }

    /// `(holder, offset, size)` of a store's destination `s.f`: a pointer
    /// field one level into a holder (E1).
    fn holder_field(&self, dest: &Place<'tcx>) -> Option<(Local, i64, i64)> {
        if !self.holders.contains(&dest.local) {
            return None;
        }
        let [PlaceElem::Field(field, field_ty)] = dest.projection[..] else {
            return None;
        };
        if !matches!(field_ty.kind(), TyKind::RawPtr(..)) {
            return None;
        }
        let ty = self.body.local_decls[dest.local].ty;
        let layout = self.tcx.layout_of(self.env.as_query_input(ty)).ok()?;
        let off = i64::try_from(layout.fields.offset(field.index()).bytes()).ok()?;
        Some((dest.local, off, self.size_of(field_ty)?))
    }

    /// E1: everything reached through the pointer stored in `holder`'s field
    /// at `[off, off + size)`, relative to that pointer: the loads of the field
    /// in the body and, through the holder's address, in the callees it is
    /// handed to (their paths). Unknown when the holder is read whole, its
    /// field's bytes are read other than as a pointer, a callee stores to
    /// the field, or its address goes where the walk cannot follow. A store
    /// to the holder in the body only replaces what the field holds: every
    /// stored value carries the path in its own footprint.
    fn holder_path(&self, holder: Local, off: i64, size: i64) -> Footprint {
        if let Some(known) = self.holder_paths.borrow().get(&(holder, off)) {
            return known.clone();
        }
        if self.uses.is_none() {
            return Footprint::Unknown("no-path");
        }
        // A cycle is Unknown: marked before the walk.
        self.holder_paths
            .borrow_mut()
            .insert((holder, off), Footprint::Unknown("cycle"));
        let fp = self
            .path(holder)
            .at(off, size)
            .join(self.holder_mentions(holder, off, size));
        self.holder_paths
            .borrow_mut()
            .insert((holder, off), fp.clone());
        fp
    }

    /// The holder's own mentions in the body: loads of the field, reads of
    /// other bytes, writes, and its address taken into a local of its path.
    fn holder_mentions(&self, holder: Local, off: i64, size: i64) -> Footprint {
        use rustc_middle::mir::visit::{
            MutatingUseContext as M, NonMutatingUseContext as N, PlaceContext, Visitor,
        };
        struct Mentions<'tcx>(Local, Vec<(Location, Place<'tcx>, PlaceContext)>);
        impl<'tcx> Visitor<'tcx> for Mentions<'tcx> {
            fn visit_place(
                &mut self,
                place: &Place<'tcx>,
                context: PlaceContext,
                location: Location,
            ) {
                if place.local == self.0 {
                    self.1.push((location, *place, context));
                }
                self.super_place(place, context, location);
            }
        }
        let mut mentions = Mentions(holder, Vec::new());
        mentions.visit_body(self.body);
        let meets = |place: &Place<'tcx>, location: Location| -> bool {
            match self.place_offset_from(place, 0, location) {
                Some((lo, hi, Some(bytes), _, _)) => match (lo.as_constant(), hi.as_constant()) {
                    (Some(lo), Some(hi)) => lo < off + size && off < hi + bytes,
                    _ => true,
                },
                _ => true,
            }
        };
        let mut fp = Footprint::Empty;
        for (location, place, context) in mentions.1 {
            // Through a pointer stored in the holder: a read of that pointer.
            if place.projection.contains(&PlaceElem::Deref) {
                if meets(&place, location) {
                    return Footprint::Unknown("holder-field-used");
                }
                continue;
            }
            match context {
                PlaceContext::NonUse(_)
                | PlaceContext::NonMutatingUse(N::Inspect | N::PlaceMention)
                | PlaceContext::MutatingUse(
                    M::Store | M::Call | M::AsmOutput | M::SetDiscriminant | M::Deinit | M::Retag,
                ) => {}
                PlaceContext::MutatingUse(M::Borrow | M::RawBorrow)
                | PlaceContext::NonMutatingUse(N::SharedBorrow | N::FakeBorrow | N::RawBorrow) => {
                    // The address lands in a local of the holder's path.
                    let taken = match at(self.body, location) {
                        At::Statement(statement) => match &statement.kind {
                            StatementKind::Assign(box (lhs, _)) => lhs.as_local(),
                            _ => None,
                        },
                        At::Terminator(_) => None,
                    };
                    if !taken
                        .and_then(|local| self.derivs.get(&local))
                        .is_some_and(|deriv| deriv.root == holder)
                    {
                        return Footprint::Unknown("holder-address");
                    }
                }
                PlaceContext::NonMutatingUse(N::Copy | N::Move) => {
                    let field = matches!(
                        self.place_offset_from(&place, 0, location),
                        Some((lo, hi, Some(bytes), false, _))
                            if lo == hi && lo.as_constant() == Some(off) && bytes == size
                    );
                    match field.then(|| self.exact_load(&place, location)).flatten() {
                        Some(loaded) => fp = fp.join(loaded),
                        None if meets(&place, location) => {
                            return Footprint::Unknown("holder-read");
                        }
                        None => {}
                    }
                }
                _ => return Footprint::Unknown("holder-use"),
            }
            if matches!(fp, Footprint::Unknown(_)) {
                return fp;
            }
        }
        fp
    }

    /// The statement at `location` loads the pointer at `place` into a local of
    /// its own family, and nothing else: that family.
    fn exact_load(&self, place: &Place<'tcx>, location: Location) -> Option<Footprint> {
        let At::Statement(statement) = at(self.body, location) else {
            return None;
        };
        let StatementKind::Assign(box (lhs, rvalue)) = &statement.kind else {
            return None;
        };
        let (Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
        | Rvalue::CopyForDeref(p)
        | Rvalue::Cast(
            CastKind::PtrToPtr
            | CastKind::PointerCoercion(
                PointerCoercion::Unsize
                | PointerCoercion::MutToConstPointer
                | PointerCoercion::ArrayToPointer,
                _,
            ),
            Operand::Copy(p) | Operand::Move(p),
            _,
        )) = rvalue
        else {
            return None;
        };
        let dest = lhs.as_local()?;
        if p != place
            || self
                .derivs
                .get(&dest)
                .is_none_or(|deriv| deriv.root != dest)
        {
            return None;
        }
        Some(self.family(dest))
    }

    /// The path of `root` (a pointer formal, or a holder through its
    /// address): every use of every local of its family.
    fn path(&self, root: Local) -> Path {
        if let Some(known) = self.paths.borrow().get(&root) {
            return known.clone();
        }
        let Some(uses) = self.uses else {
            return Path::opaque("no-path");
        };
        let mut members: Vec<(Local, &Deriv)> = self
            .derivs
            .iter()
            .filter(|(_, deriv)| deriv.root == root)
            .map(|(local, deriv)| (*local, deriv))
            .collect();
        members.sort_by_key(|(local, _)| *local);
        let mut path = Path::default();
        // The bytes `[deriv.lo + lo, deriv.hi + hi + size)`, `None` unbounded.
        let span = |deriv: &Deriv, lo: Bound, hi: Bound, size: i64| -> Option<(Bound, Bound)> {
            Some((
                deriv.lo.plus(lo)?,
                deriv.hi.plus(hi)?.plus(Bound::constant(size))?,
            ))
        };
        for (local, deriv) in members {
            for (location, occ) in uses.get(&local).into_iter().flatten() {
                match &occ.what {
                    Use::Inert => {}
                    Use::Escape(why) => path.stop(why),
                    Use::Flow { dest } => match dest.as_local() {
                        Some(RETURN_PLACE) => path.stop("returned"),
                        Some(dest)
                            if self.derivs.get(&dest).is_some_and(|next| next.root == root) => {}
                        Some(_) => path.stop("flows-into-untracked"),
                        None => path.stop("stored"),
                    },
                    Use::Bytes { place, write } => {
                        let Some((lo, hi, Some(size), through, _)) =
                            self.place_offset(place, *location)
                        else {
                            path.touch(None);
                            continue;
                        };
                        let range = span(deriv, lo, hi, size);
                        // A pointer loaded at one constant offset of the root.
                        let load = match range {
                            Some((from, _))
                                if !*write && !through && deriv.lo == deriv.hi && lo == hi =>
                            {
                                from.as_constant().zip(self.exact_load(place, *location))
                            }
                            _ => None,
                        };
                        match load {
                            Some((at, loaded)) => path.loads.push((at, size, loaded)),
                            None => path.touch(range),
                        }
                    }
                    Use::Arg { k } => self.path_argument(&mut path, deriv, *k, *location),
                }
                if path.opaque.is_some() {
                    break;
                }
            }
        }
        self.paths.borrow_mut().insert(root, path.clone());
        path
    }

    /// A member of a path as argument `k` of the call at `location`.
    fn path_argument(&self, path: &mut Path, deriv: &Deriv, k: usize, location: Location) {
        let terminator = self.body.basic_blocks[location.block].terminator();
        let (
            TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            },
            Some(call),
        ) = (&terminator.kind, terminator.as_call(self.tcx))
        else {
            path.stop("not-a-call");
            return;
        };
        let actual = |j: u32| self.actual(args, j, location);
        let lands_in_path = |dest: &Place<'tcx>| {
            dest.as_local()
                .and_then(|dest| self.derivs.get(&dest))
                .is_some_and(|next| next.root == deriv.root)
        };
        if k == 0
            && (core_pointer_step(self.tcx, &call.func).is_some()
                || core_slice_buffer(self.tcx, self.body, func))
        {
            if !lands_in_path(destination) {
                path.stop("flows-into-untracked");
            }
            return;
        }
        if k == 0 && core_is_null(self.tcx, &call.func) {
            return;
        }
        if let Some((written, read, length)) = libc_row(&call.func) {
            if k != written && Some(k) != read {
                path.stop("libc-argument");
                return;
            }
            let n = actual(length as u32).and_then(Bound::as_constant);
            path.touch(n.and_then(|n| Some((deriv.lo, deriv.hi.plus(Bound::constant(n))?))));
            if k == written && !lands_in_path(destination) {
                // `memcpy` / `memmove` / `memset` return their destination.
                path.stop("flows-into-untracked");
            }
            return;
        }
        let callee = func
            .const_fn_def()
            .and_then(|(def, _)| def.as_local())
            .filter(|callee| self.table.scc.contains_key(callee));
        let Some(callee) = callee else {
            path.stop("foreign-callee");
            return;
        };
        if self.table.scc.get(&callee) == self.table.scc.get(&self.function) {
            path.stop("recursion");
            return;
        }
        match self.table.paths.get(&(callee, k as u32)) {
            Some(callee_path) => path.absorb(callee_path, deriv, &actual, (callee, k as u32)),
            None => path.stop("no-path"),
        }
    }

    /// The actual of formal `j` at a call: a constant, or a range pinned to
    /// one value (the caller's formal keeps it affine).
    fn actual(
        &self,
        args: &[rustc_span::source_map::Spanned<Operand<'tcx>>],
        j: u32,
        location: Location,
    ) -> Option<Bound> {
        let operand = &args.get(j as usize)?.node;
        match operand {
            Operand::Constant(_) => constant_value(self.tcx, operand).map(Bound::constant),
            _ => self.ints.range(location, operand_local(operand)?)?.actual(),
        }
    }

    /// The whole value as argument `k` of the call at `location`.
    fn argument(&self, deriv: &Deriv, k: usize, location: Location) -> Footprint {
        let terminator = self.body.basic_blocks[location.block].terminator();
        let TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &terminator.kind
        else {
            return Footprint::Unknown("not-a-call");
        };
        let Some(call) = terminator.as_call(self.tcx) else {
            return Footprint::Unknown("not-a-call");
        };
        let actual = |j: u32| self.actual(args, j, location);
        if k == 0
            && (core_pointer_step(self.tcx, &call.func).is_some()
                || core_slice_buffer(self.tcx, self.body, func))
        {
            return self.flow(deriv, destination);
        }
        if k == 0 && core_is_null(self.tcx, &call.func) {
            return Footprint::Empty;
        }
        if let Some((written, read, length)) = libc_row(&call.func) {
            let Some(n) = actual(length as u32).and_then(Bound::as_constant) else {
                return Footprint::Unknown("libc-length");
            };
            let own = if k == written {
                Footprint::bytes(
                    Bound::constant(0),
                    Bound::constant(n),
                    true,
                    BTreeSet::new(),
                )
            } else if Some(k) == read {
                // The bytes copied out may be a pointer to the base, used after
                // through the copy (the reviewer's M1): a pointer read out of
                // the base, as `loads-a-pointer`. Types cannot rule it out: the
                // object behind a byte pointer may hold pointers.
                return Footprint::Unknown("copies-bytes-out");
            } else {
                return Footprint::Unknown("libc-argument");
            };
            let own = own.shift(deriv.lo, deriv.hi, &deriv.premises);
            // `memcpy` / `memmove` / `memset` return their destination.
            return if k == written {
                own.join(self.flow(deriv, destination))
            } else {
                own
            };
        }
        let callee = func
            .const_fn_def()
            .and_then(|(def, _)| def.as_local())
            .filter(|callee| self.table.scc.contains_key(callee));
        let Some(callee) = callee else {
            return Footprint::Unknown("foreign-callee");
        };
        if self.table.scc.get(&callee) == self.table.scc.get(&self.function) {
            return Footprint::Unknown("recursion");
        }
        let extent = self.table.ext(callee, k as u32);
        let extent = match extent.instantiate(&actual) {
            Footprint::Bytes(mut bytes) => {
                bytes.summaries.insert((callee, k as u32));
                Footprint::Bytes(bytes)
            }
            other => other,
        };
        extent.shift(deriv.lo, deriv.hi, &deriv.premises)
    }

    /// The bases whose value escapes the body, by a taint walk over value
    /// flows from each pointer formal that is never written: every local the
    /// value reaches (copies, address-keeping casts, `&(*p).f`, core's steps,
    /// slice `as_ptr`, `memcpy`'s return) carries the base, whether its range
    /// is known or not. A carried use escapes when it stores, returns,
    /// aggregates or casts the value to an integer, takes its address, hands
    /// it to a foreign or recursive callee or to a local one whose formal
    /// escapes, copies bytes out of it, or reads a pointer out of it.
    fn escaped_roots(&self) -> FxHashSet<Local> {
        let Some(uses) = self.uses else {
            return FxHashSet::default();
        };
        let mut carried: FxHashMap<Local, FxHashSet<Local>> = FxHashMap::default();
        let mut work = Vec::new();
        for local in self.body.local_decls.indices() {
            if self.shape.fixed_formal(local) && is_pointer(self.body, local) {
                carried.entry(local).or_default().insert(local);
                work.push(local);
            }
        }
        let mut escaped = FxHashSet::default();
        while let Some(local) = work.pop() {
            let roots = carried[&local].clone();
            let mut into =
                |dest: &Place<'tcx>, work: &mut Vec<Local>, escaped: &mut FxHashSet<Local>| {
                    match dest.as_local() {
                        Some(RETURN_PLACE) | None => escaped.extend(roots.iter().copied()),
                        Some(dest) => {
                            let set = carried.entry(dest).or_default();
                            let before = set.len();
                            set.extend(roots.iter().copied());
                            if set.len() != before {
                                work.push(dest);
                            }
                        }
                    }
                };
            for (location, occ) in uses.get(&local).into_iter().flatten() {
                match &occ.what {
                    Use::Inert => {}
                    Use::Escape(_) => escaped.extend(roots.iter().copied()),
                    // E1: a value of the family stored into a holder's field
                    // whose path is bounded is retained only where that path
                    // reaches, and its footprint carries the path.
                    Use::Flow { dest }
                        if self.derivs.contains_key(&local)
                            && self.holder_field(dest).is_some_and(|(holder, off, size)| {
                                !matches!(
                                    self.holder_path(holder, off, size),
                                    Footprint::Unknown(_)
                                )
                            }) => {}
                    Use::Flow { dest } => into(dest, &mut work, &mut escaped),
                    Use::Bytes { place, write } => {
                        let through = place.projection[1..].contains(&PlaceElem::Deref);
                        if through
                            || (!*write && self.holds_pointer(place.ty(self.body, self.tcx).ty, 4))
                        {
                            escaped.extend(roots.iter().copied());
                        }
                    }
                    Use::Arg { k } => {
                        let terminator = self.body.basic_blocks[location.block].terminator();
                        let (
                            TerminatorKind::Call {
                                func, destination, ..
                            },
                            Some(call),
                        ) = (&terminator.kind, terminator.as_call(self.tcx))
                        else {
                            escaped.extend(roots.iter().copied());
                            continue;
                        };
                        if *k == 0
                            && (core_pointer_step(self.tcx, &call.func).is_some()
                                || core_slice_buffer(self.tcx, self.body, func))
                        {
                            into(destination, &mut work, &mut escaped);
                        } else if *k == 0 && core_is_null(self.tcx, &call.func) {
                        } else if let Some((written, _, _)) = libc_row(&call.func) {
                            if *k == written {
                                into(destination, &mut work, &mut escaped);
                            } else {
                                escaped.extend(roots.iter().copied());
                            }
                        } else {
                            let callee = func
                                .const_fn_def()
                                .and_then(|(def, _)| def.as_local())
                                .filter(|callee| self.table.scc.contains_key(callee));
                            let follows = callee.is_some_and(|callee| {
                                self.table.scc.get(&callee) != self.table.scc.get(&self.function)
                                    && !self.table.escapes.contains(&(callee, *k as u32))
                            });
                            if !follows {
                                escaped.extend(roots.iter().copied());
                            }
                        }
                    }
                }
            }
        }
        escaped
    }

    /// Everything reached through `local` and what derives from it.
    fn family(&self, local: Local) -> Footprint {
        if let Some(known) = self.families.borrow().get(&local) {
            return known.clone();
        }
        let Some(uses) = self.uses else {
            return Footprint::Unknown("no-family");
        };
        if !self.open.borrow_mut().insert(local) {
            return Footprint::Unknown("cycle");
        }
        let mut fp = Footprint::Empty;
        for (location, occ) in uses.get(&local).into_iter().flatten() {
            fp = fp.join(self.footprint_of(occ, *location));
            if matches!(fp, Footprint::Unknown(_)) {
                break;
            }
        }
        self.open.borrow_mut().remove(&local);
        self.families.borrow_mut().insert(local, fp.clone());
        fp
    }
}

impl FnFacts {
    fn build<'tcx>(
        tcx: TyCtxt<'tcx>,
        body: &Body<'tcx>,
        function: LocalDefId,
        table: &IndexRanges,
    ) -> FnFacts {
        let shape = Shape::new(body);
        let ints = Ints::compute(tcx, body, &shape);
        let holders = holders(body, &shape);
        let families = RefCell::new(FxHashMap::default());
        let holder_paths = RefCell::new(FxHashMap::default());
        let escaped: FxHashSet<Local>;
        let mut paths = FxHashMap::default();
        let none = FxHashMap::default();
        let derivs: FxHashMap<Local, Deriv> = {
            let ctx = Ctx {
                tcx,
                body,
                function,
                env: ty::TypingEnv::post_analysis(tcx, function),
                shape: &shape,
                ints: &ints,
                holders: &holders,
                derivs: &none,
                families: &families,
                holder_paths: &holder_paths,
                open: RefCell::new(FxHashSet::default()),
                paths: RefCell::new(FxHashMap::default()),
                uses: None,
                table,
            };
            let mut memo = FxHashMap::default();
            for local in body.local_decls.indices() {
                if is_pointer(body, local) {
                    ctx.derive(local, &mut memo);
                }
            }
            memo.into_iter()
                .filter_map(|(local, deriv)| deriv.map(|deriv| (local, deriv)))
                .collect()
        };
        let mut uses: FxHashMap<Local, Vec<(Location, Occ<'tcx>)>> = FxHashMap::default();
        for (block, data) in body.basic_blocks.iter_enumerated() {
            for statement_index in 0..=data.statements.len() {
                let location = Location {
                    block,
                    statement_index,
                };
                for occ in occurrences(body, location) {
                    uses.entry(occ.from).or_default().push((location, occ));
                }
            }
        }
        {
            let ctx = Ctx {
                tcx,
                body,
                function,
                env: ty::TypingEnv::post_analysis(tcx, function),
                shape: &shape,
                ints: &ints,
                holders: &holders,
                derivs: &derivs,
                families: &families,
                holder_paths: &holder_paths,
                open: RefCell::new(FxHashSet::default()),
                paths: RefCell::new(FxHashMap::default()),
                uses: Some(&uses),
                table,
            };
            let mut locals: Vec<Local> = derivs.keys().copied().collect();
            locals.sort();
            for local in &locals {
                ctx.family(*local);
            }
            // Every holder field a pointer is stored into has its path (the
            // read-back context only reads them).
            for data in body.basic_blocks.iter() {
                for statement in &data.statements {
                    if let StatementKind::Assign(box (place, _)) = &statement.kind
                        && let Some((holder, off, size)) = ctx.holder_field(place)
                    {
                        ctx.holder_path(holder, off, size);
                    }
                }
            }
            escaped = ctx.escaped_roots();
            for k in 0..body.arg_count {
                let formal = Local::from_usize(k + 1);
                if derivs
                    .get(&formal)
                    .is_some_and(|deriv| deriv.root == formal)
                {
                    paths.insert(k as u32, ctx.path(formal));
                }
            }
        }
        FnFacts {
            shape,
            ints,
            holders,
            derivs,
            families,
            holder_paths,
            paths,
            escaped,
        }
    }
}

/// E1's holders: the local structs (never a formal, never a union) a pointer is
/// stored into one field deep, `s.f = p`.
fn holders(body: &Body<'_>, shape: &Shape) -> FxHashSet<Local> {
    let mut out = FxHashSet::default();
    for data in body.basic_blocks.iter() {
        for statement in &data.statements {
            if let StatementKind::Assign(box (place, _)) = &statement.kind
                && let [PlaceElem::Field(_, field_ty)] = place.projection[..]
                && matches!(field_ty.kind(), TyKind::RawPtr(..))
                && !shape.is_formal(place.local)
                && matches!(body.local_decls[place.local].ty.kind(), TyKind::Adt(def, _) if def.is_struct())
            {
                out.insert(place.local);
            }
        }
    }
    out
}
