//! Row (b) FIELD-OBJECT-IDENTITY: witnesses, controls and the pairing law.
//! Fixtures are compiled for analysis and never executed.

use rustc_hash::FxHashSet;
use rustc_middle::mir::{Local, Location, TerminatorKind};
use rustc_span::def_id::LocalDefId;

use super::{
    field_objects::{self, FieldBase},
    objects::{ObjectFacts, ObjectRoot, ObjectSet},
    tests_call_reach::{named_local, object_facts},
    tests_return_origin::{named_function, with_program},
};
use crate::{
    analyses::{
        borrow_ownership::{
            export::{PlaceKey, ProjKey},
            source_events::SourceRole,
        },
        mir::{CallKind, TerminatorExt},
    },
    utils::rustc::RustProgram,
};

/// The cell a place names, for a place written out explicitly rather than
/// recovered from MIR: `local` dereferenced `derefs` times, then `field`.
fn field_cell(
    facts: &ObjectFacts,
    function: LocalDefId,
    at: Location,
    local: Local,
    derefs: usize,
    field: u32,
) -> ObjectSet {
    let mut proj = vec![ProjKey::Deref; derefs];
    proj.push(ProjKey::Field(field));
    facts.pointer_at(function, at, &PlaceKey { local, proj }, 0)
}

fn local_cell(facts: &ObjectFacts, function: LocalDefId, at: Location, local: Local) -> ObjectSet {
    facts.pointer_at(
        function,
        at,
        &PlaceKey {
            local,
            proj: Vec::new(),
        },
        0,
    )
}

/// The exact root a wave-1 load from field `field` of parameter `parameter` mints.
fn input_field(function: LocalDefId, parameter: Local, field: u32) -> ObjectSet {
    ObjectSet {
        roots: FxHashSet::from_iter([ObjectRoot::Field {
            base: FieldBase::Input {
                function,
                parameter,
                depth: 0,
            },
            field,
        }]),
        unknown: false,
    }
}

/// Terminator locations of the calls to a named libc entry, in block order.
fn libc_sites(program: &RustProgram<'_>, function: LocalDefId, name: &str) -> Vec<Location> {
    let body = program
        .tcx
        .mir_drops_elaborated_and_const_checked(function)
        .borrow();
    let mut sites: Vec<_> = body
        .basic_blocks
        .iter_enumerated()
        .filter_map(|(block, data)| {
            let call = data.terminator().as_call(program.tcx)?;
            matches!(call.func, CallKind::LibC(symbol) if symbol.as_str() == name).then_some(
                Location {
                    block,
                    statement_index: data.statements.len(),
                },
            )
        })
        .collect();
    sites.sort_by_key(|site| (site.block.as_u32(), site.statement_index));
    sites
}

/// The terminator location of the one call to a named local function, plus its
/// normal successor's entry location.
fn local_call(
    program: &RustProgram<'_>,
    caller: LocalDefId,
    callee: LocalDefId,
) -> (Location, Location) {
    let body = program
        .tcx
        .mir_drops_elaborated_and_const_checked(caller)
        .borrow();
    let calls: Vec<_> = body
        .basic_blocks
        .iter_enumerated()
        .filter_map(|(block, data)| {
            let call = data.terminator().as_call(program.tcx)?;
            if !matches!(call.func, CallKind::FreeStanding(function) if function == callee) {
                return None;
            }
            let TerminatorKind::Call {
                target: Some(target),
                ..
            } = data.terminator().kind
            else {
                panic!("fixture call must have a normal successor");
            };
            Some((
                Location {
                    block,
                    statement_index: data.statements.len(),
                },
                Location {
                    block: target,
                    statement_index: 0,
                },
            ))
        })
        .collect();
    assert_eq!(calls.len(), 1, "one exact observed local call");
    calls[0]
}

// ---------------------------------------------------------------- B-W01

/// B-W01, the `buffer_resize` shape: `realloc((*p).f, ..)` with `obj(p)` a
/// known `Input`. The retired set must be the exact field root, not Unknown.
const REALLOC_FIELD: &str = r#"
unsafe extern "C" { fn realloc(p: *mut core::ffi::c_void, n: usize) -> *mut core::ffi::c_void; }
#[repr(C)] pub struct Buf { data: *mut u8 }
pub unsafe fn grow(p: *mut Buf, n: usize) -> *mut u8 {
    let old = (*p).data;
    let fresh = realloc(old as *mut core::ffi::c_void, n) as *mut u8;
    fresh
}
"#;

#[test]
fn b_w01_a_reallocated_field_load_is_the_exact_field_root() {
    with_program(REALLOC_FIELD, |program| {
        let grow = named_function(program, "grow");
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(grow)
            .borrow();
        let p = named_local(&body, "p");
        let old = named_local(&body, "old");
        drop(body);
        let sites = libc_sites(program, grow, "realloc");
        assert_eq!(sites.len(), 1, "one exact realloc site");
        let facts = object_facts(program);
        let expected = input_field(grow, p, 0);
        assert_eq!(
            local_cell(&facts, grow, sites[0], old),
            expected,
            "the retired operand carries the exact field root at the realloc site"
        );
        assert_eq!(
            field_cell(&facts, grow, sites[0], p, 1, 0),
            expected,
            "the field place itself names the same root, which is the channel a direct \
             `free((*p).f)` operand uses"
        );
    });
}

// ---------------------------------------------------------------- B-W02

/// B-W02: two loads of the same field of the same object, with nothing between
/// them that may write the cell. The roots are identical, and the retirement of
/// one conflicts with the other rather than being disjoint from it.
const TWO_LOADS: &str = r#"
unsafe extern "C" { fn free(p: *mut core::ffi::c_void); }
#[repr(C)] pub struct Node { payload: *mut u8 }
pub unsafe fn twice(p: *mut Node) -> u8 {
    let first = (*p).payload;
    let second = (*p).payload;
    let value = *second;
    free(first as *mut core::ffi::c_void);
    value
}
"#;

#[test]
fn b_w02_two_unwritten_loads_are_the_same_object_and_conflict() {
    with_program(TWO_LOADS, |program| {
        let twice = named_function(program, "twice");
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(twice)
            .borrow();
        let p = named_local(&body, "p");
        let first = named_local(&body, "first");
        let second = named_local(&body, "second");
        drop(body);
        let sites = libc_sites(program, twice, "free");
        assert_eq!(sites.len(), 1, "one exact free site");
        let facts = object_facts(program);
        let expected = input_field(twice, p, 0);
        let retired = local_cell(&facts, twice, sites[0], first);
        let live = local_cell(&facts, twice, sites[0], second);
        assert_eq!(
            retired, expected,
            "the retired load is the exact field root"
        );
        assert_eq!(live, expected, "the live load is the same exact field root");
        assert_eq!(
            super::overlap(&retired, &live, twice, true),
            Some(super::OverlapReason::SameAbstractRoot),
            "retiring one of two identical field objects conflicts with the other"
        );
    });
}

// ---------------------------------------------------------------- B-W03

/// B-W03: a store to the field between the two loads. The first load's identity
/// must die -- it named the object that WAS in the cell.
const STORE_BETWEEN: &str = r#"
unsafe extern "C" { fn free(p: *mut core::ffi::c_void); fn malloc(n: usize) -> *mut u8; }
#[repr(C)] pub struct Node { payload: *mut u8 }
pub unsafe fn replace(p: *mut Node) -> u8 {
    let first = (*p).payload;
    (*p).payload = malloc(8);
    let second = (*p).payload;
    let value = *second;
    free(first as *mut core::ffi::c_void);
    value
}
"#;

#[test]
fn b_w03_a_field_store_kills_the_earlier_load() {
    with_program(STORE_BETWEEN, |program| {
        let replace = named_function(program, "replace");
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(replace)
            .borrow();
        let p = named_local(&body, "p");
        let first = named_local(&body, "first");
        drop(body);
        let allocations = libc_sites(program, replace, "malloc");
        let frees = libc_sites(program, replace, "free");
        assert_eq!(allocations.len(), 1, "one exact allocation site");
        assert_eq!(frees.len(), 1, "one exact free site");
        let facts = object_facts(program);
        assert_eq!(
            local_cell(&facts, replace, allocations[0], first),
            input_field(replace, p, 0),
            "before the store the first load is the exact field root, so this witness is not vacuous"
        );
        let after = local_cell(&facts, replace, frees[0], first);
        assert!(
            after.unknown,
            "the store replaced the cell's content, so the earlier load's identity must not \
             survive as exact evidence: {after:?}"
        );
    });
}

// ---------------------------------------------------------------- B-W04

/// B-W04, the row-(a) interaction: a non-allocator local call between the load
/// and its use. `first` never escapes and sits at depth 0, so row (a) preserves
/// its pointer VALUE; row (b) must still kill its field IDENTITY, because the
/// callee may write the cell it was loaded from.
const CALL_BETWEEN: &str = r#"
unsafe extern "C" { fn free(p: *mut core::ffi::c_void); }
#[repr(C)] pub struct Node { payload: *mut u8 }
unsafe fn touch(n: *mut Node) -> u8 { (*n).payload as usize as u8 }
pub unsafe fn visit(p: *mut Node) -> u8 {
    let first = (*p).payload;
    let seen = touch(p);
    free(first as *mut core::ffi::c_void);
    seen
}
"#;

#[test]
fn b_w04_a_local_call_kills_field_identity_it_could_write() {
    with_program(CALL_BETWEEN, |program| {
        let visit = named_function(program, "visit");
        let touch = named_function(program, "touch");
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(visit)
            .borrow();
        let p = named_local(&body, "p");
        let first = named_local(&body, "first");
        drop(body);
        let (site, after) = local_call(program, visit, touch);
        let facts = object_facts(program);
        assert_eq!(
            local_cell(&facts, visit, site, first),
            input_field(visit, p, 0),
            "before the call the load is the exact field root, so this witness is not vacuous"
        );
        let killed = local_cell(&facts, visit, after, first);
        assert!(
            killed.unknown,
            "the callee may write the field cell, so field identity must not survive the call \
             even in a cell the callee cannot name: {killed:?}"
        );
    });
}

// ---------------------------------------------------------------- B-W05

/// B-W05: a MAY base is never named. Two known bases is the discriminating
/// shape -- an Unknown base is refused by the `unknown` test alone.
const MAY_BASE: &str = r#"
unsafe extern "C" { fn free(p: *mut core::ffi::c_void); fn opaque() -> *mut Node; }
#[repr(C)] pub struct Node { payload: *mut u8 }
pub unsafe fn two_known(p: *mut Node, q: *mut Node, choose: bool) -> u8 {
    let base = if choose { p } else { q };
    let loaded = (*base).payload;
    let value = *loaded;
    free(loaded as *mut core::ffi::c_void);
    value
}
pub unsafe fn one_unknown(p: *mut Node, choose: bool) -> u8 {
    let base = if choose { p } else { opaque() };
    let loaded = (*base).payload;
    let value = *loaded;
    free(loaded as *mut core::ffi::c_void);
    value
}
"#;

#[test]
fn b_w05_a_may_base_mints_no_field_root() {
    with_program(MAY_BASE, |program| {
        let facts = object_facts(program);
        for name in ["two_known", "one_unknown"] {
            let function = named_function(program, name);
            let body = program
                .tcx
                .mir_drops_elaborated_and_const_checked(function)
                .borrow();
            let loaded = named_local(&body, "loaded");
            let base = named_local(&body, "base");
            drop(body);
            let frees = libc_sites(program, function, "free");
            assert_eq!(frees.len(), 1, "one exact free site in {name}");
            let carrier = local_cell(&facts, function, frees[0], base);
            assert!(
                carrier.unknown || carrier.roots.len() > 1,
                "{name} must actually present a MAY base, or this witness is vacuous: {carrier:?}"
            );
            let cell = local_cell(&facts, function, frees[0], loaded);
            assert!(
                !field_objects::names_field(&cell),
                "{name} must mint no field root from a MAY base: {cell:?}"
            );
            assert!(
                cell.unknown,
                "{name}'s load stays Unknown, exactly as before this row: {cell:?}"
            );
        }
    });
}

// ---------------------------------------------------------------- B-W06

/// B-W06 must-not-move, the exact `buffer_free` shape. `free((*p).f)` then
/// `free(p)`: the pair still conflicts and both slots stay Raw. This is the
/// pairing law's load-bearing case -- `Field { base: o, f }` against `o` itself
/// is NOT disjoint, because a field of `o` may point back into `o`.
const SELF_FREE_PAIR: &str = r#"
unsafe extern "C" { fn free(p: *mut core::ffi::c_void); }
#[repr(C)] pub struct Buffer { alloc: *mut u8 }
pub unsafe fn buffer_free(s: *mut Buffer) {
    free((*s).alloc as *mut core::ffi::c_void);
    free(s as *mut core::ffi::c_void);
}
"#;

#[test]
fn b_w06_buffer_free_self_free_pair_still_conflicts() {
    assert!(
        !super::tests::accepts(SELF_FREE_PAIR, &[("buffer_free", 1, 0)]),
        "row (b) must not promote the self-free pair: a field of the container may point back \
         into the container"
    );
    with_program(SELF_FREE_PAIR, |program| {
        let buffer_free = named_function(program, "buffer_free");
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(buffer_free)
            .borrow();
        let s = named_local(&body, "s");
        drop(body);
        let frees = libc_sites(program, buffer_free, "free");
        assert_eq!(frees.len(), 2, "two exact free sites");
        let facts = object_facts(program);
        let retired = field_cell(&facts, buffer_free, frees[0], s, 1, 0);
        assert_eq!(
            retired,
            input_field(buffer_free, s, 0),
            "the refusal now rests on a NAMED field root, not on Unknown"
        );
        let container = local_cell(&facts, buffer_free, frees[0], s);
        assert_eq!(
            super::overlap(&retired, &container, buffer_free, true),
            Some(super::OverlapReason::UnresolvedInvocation),
            "a field of the container is not disjoint from the container"
        );
    });
}

// ---------------------------------------------------------------- B-W07

/// B-W07: the bound. Anything that is not "one or more derefs, then one field,
/// then nothing" mints nothing, and no extra depth is ever named.
#[test]
fn b_w07_only_a_single_field_step_is_within_the_bound() {
    assert_eq!(
        field_objects::field_step(&[ProjKey::Deref, ProjKey::Field(3)], 0),
        Some((0, 3)),
        "one deref then one field is the wave-1 shape"
    );
    assert_eq!(
        field_objects::field_step(&[ProjKey::Deref, ProjKey::Deref, ProjKey::Field(1)], 0),
        Some((1, 1)),
        "the containing object may itself sit behind a deref"
    );
    for (shape, why) in [
        (
            vec![ProjKey::Deref, ProjKey::Field(0), ProjKey::Field(0)],
            "a nested field path is past the bound",
        ),
        (
            vec![ProjKey::Field(0)],
            "a field of a local aggregate has no pointer base to name",
        ),
        (
            vec![ProjKey::Deref, ProjKey::Index(4)],
            "an array element is not a field",
        ),
        (
            vec![ProjKey::Deref, ProjKey::Field(0), ProjKey::Deref],
            "a load through the field is past the bound",
        ),
        (
            vec![ProjKey::Deref, ProjKey::Downcast(1), ProjKey::Field(0)],
            "a variant field is not a wave-1 field step",
        ),
        (vec![ProjKey::Deref], "a plain deref is not a field load"),
        (Vec::new(), "the bare local is not a field load"),
    ] {
        assert_eq!(
            field_objects::field_step(&shape, 0),
            None,
            "{why}: {shape:?}"
        );
    }
    assert_eq!(
        field_objects::field_step(&[ProjKey::Deref, ProjKey::Field(3)], 1),
        None,
        "a cell BEHIND a field load is not named in wave 1"
    );
}

/// The production path agrees with the bound: a nested field load stays Unknown.
const NESTED_FIELD: &str = r#"
unsafe extern "C" { fn free(p: *mut core::ffi::c_void); }
#[repr(C)] pub struct Inner { payload: *mut u8 }
#[repr(C)] pub struct Outer { inner: Inner }
pub unsafe fn nested(p: *mut Outer) -> u8 {
    let loaded = (*p).inner.payload;
    let value = *loaded;
    free(loaded as *mut core::ffi::c_void);
    value
}
"#;

#[test]
fn b_w07_a_nested_field_load_stays_unknown_in_production() {
    with_program(NESTED_FIELD, |program| {
        let nested = named_function(program, "nested");
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(nested)
            .borrow();
        let loaded = named_local(&body, "loaded");
        drop(body);
        let frees = libc_sites(program, nested, "free");
        assert_eq!(frees.len(), 1, "one exact free site");
        let facts = object_facts(program);
        let cell = local_cell(&facts, nested, frees[0], loaded);
        assert!(
            !field_objects::names_field(&cell) && cell.unknown,
            "a two-step field path mints nothing: {cell:?}"
        );
    });
}

// ---------------------------------------------------------------- B-W08

/// B-W08: a field-rooted event crossing a route step fails closed. The base
/// names the callee's own parameter object and wave 1 has no rebasing rule, so
/// the routed event must carry `unknown` and say why.
const ROUTED_FIELD_FREE: &str = r#"
unsafe extern "C" { fn free(p: *mut core::ffi::c_void); }
#[repr(C)] pub struct Node { payload: *mut u8 }
unsafe fn release(n: *mut Node) { free((*n).payload as *mut core::ffi::c_void); }
pub unsafe fn caller(p: *mut Node, keep: *const u8) -> u8 {
    let value = *keep;
    release(p);
    value
}
"#;

#[test]
fn b_w08_a_field_root_fails_closed_across_a_route_step() {
    with_program(ROUTED_FIELD_FREE, |program| {
        let caller = named_function(program, "caller");
        let release = named_function(program, "release");
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(release)
            .borrow();
        let n = named_local(&body, "n");
        drop(body);
        let facts = object_facts(program);
        let events = crate::analyses::borrow_ownership::source_events::collect(program);
        let routed = super::routes::expand(program, &events, &facts);
        let own: Vec<_> = routed
            .frames
            .get(&release)
            .into_iter()
            .flatten()
            .filter(|event| event.source.key.role == SourceRole::Free && event.route.is_empty())
            .collect();
        assert_eq!(own.len(), 1, "one exact unrouted free event in the callee");
        assert_eq!(
            own[0].objects,
            input_field(release, n, 0),
            "in its own frame the event carries the exact field root"
        );
        let crossed: Vec<_> = routed
            .frames
            .get(&caller)
            .into_iter()
            .flatten()
            .filter(|event| event.source.key.role == SourceRole::Free && !event.route.is_empty())
            .collect();
        assert_eq!(
            crossed.len(),
            1,
            "one exact routed free event in the caller"
        );
        assert!(
            crossed[0].objects.unknown,
            "field identity must not cross a frame unrebased: {:?}",
            crossed[0].objects
        );
        assert_eq!(
            crossed[0].uncertainty,
            Some(super::RouteReason::FieldAcrossFrame),
            "the fail-closed step is typed, not an indistinguishable unknown object (R323-2)"
        );
    });
}

// ---------------------------------------------------------------- B-C01

/// B-C01, obligation 2 of the row: in wave 1 no pair involving a field root may
/// yield the disjointness verdict, except the pre-existing `heap_only` skip for
/// `Stack` roots, which is unchanged.
#[test]
fn b_c01_no_field_pair_is_disjoint_outside_the_stack_skip() {
    with_program(TWO_LOADS, |program| {
        let frame = named_function(program, "twice");
        let base = FieldBase::Input {
            function: frame,
            parameter: Local::from_u32(1),
            depth: 0,
        };
        let field = ObjectRoot::Field { base, field: 0 };
        let other_field = ObjectRoot::Field { base, field: 1 };
        let site = Location {
            block: rustc_middle::mir::START_BLOCK,
            statement_index: 0,
        };
        let partners = [
            ObjectRoot::Input {
                function: frame,
                parameter: Local::from_u32(1),
                depth: 0,
            },
            ObjectRoot::Fresh { frame, site },
            ObjectRoot::Stack {
                function: frame,
                local: Local::from_u32(2),
            },
            other_field,
        ];
        let one = |root: ObjectRoot| ObjectSet {
            roots: FxHashSet::from_iter([root]),
            unknown: false,
        };
        assert_eq!(
            super::overlap(&one(field), &one(field), frame, true),
            Some(super::OverlapReason::SameAbstractRoot),
            "the identical field root is the same abstract object"
        );
        for partner in partners {
            let stack = matches!(partner, ObjectRoot::Stack { .. });
            for (left, right) in [(field, partner), (partner, field)] {
                for heap_only in [false, true] {
                    let verdict = super::overlap(&one(left), &one(right), frame, heap_only);
                    if stack && heap_only {
                        assert_eq!(
                            verdict, None,
                            "the P0 stack skip is unchanged: {left:?} vs {right:?}"
                        );
                    } else {
                        assert_eq!(
                            verdict,
                            Some(super::OverlapReason::UnresolvedInvocation),
                            "no field pair may be disjoint: {left:?} vs {right:?} \
                             (heap_only={heap_only})"
                        );
                    }
                }
            }
        }
    });
}

// ---------------------------------------------------------------- B-C02

/// B-C02, the mechanized form of obligation 2: a minted field root must never
/// REMOVE a conflict that Unknown would have reported. This is the property
/// that makes wave 1 sound without depending on the kill obligation, and it is
/// also the measurement of wave 1's precision: if a field root never removes a
/// conflict, wave 1 cannot promote anything through `overlap`, and the yield it
/// carries is exact identity in the receipts rather than verdict movement. The
/// day a later wave makes any pair below disjoint, this control fails and the
/// kill obligation becomes load-bearing -- which is exactly when it should be
/// re-examined.
#[test]
fn b_c02_a_field_root_never_removes_a_conflict_unknown_would_report() {
    with_program(MAY_BASE, |program| {
        let frame = named_function(program, "two_known");
        let other = named_function(program, "one_unknown");
        let site = Location {
            block: rustc_middle::mir::START_BLOCK,
            statement_index: 0,
        };
        let base = FieldBase::Input {
            function: frame,
            parameter: Local::from_u32(1),
            depth: 0,
        };
        let field = ObjectRoot::Field { base, field: 0 };
        let pool = [
            ObjectRoot::Input {
                function: frame,
                parameter: Local::from_u32(1),
                depth: 0,
            },
            ObjectRoot::Input {
                function: frame,
                parameter: Local::from_u32(2),
                depth: 0,
            },
            ObjectRoot::Fresh { frame, site },
            ObjectRoot::Fresh { frame: other, site },
            ObjectRoot::Stack {
                function: frame,
                local: Local::from_u32(3),
            },
            field,
            ObjectRoot::Field { base, field: 1 },
        ];
        let mut partners = vec![Vec::new()];
        for (index, first) in pool.iter().enumerate() {
            partners.push(vec![*first]);
            for second in &pool[index + 1..] {
                partners.push(vec![*first, *second]);
            }
        }
        assert_eq!(partners.len(), 29, "exact enumeration of the partner sets");
        let mut compared = 0;
        let blanket_set = ObjectSet {
            roots: FxHashSet::default(),
            unknown: true,
        };
        let named = ObjectSet {
            roots: FxHashSet::from_iter([field]),
            unknown: false,
        };
        for roots in &partners {
            for unknown in [false, true] {
                let partner = ObjectSet {
                    roots: FxHashSet::from_iter(roots.iter().copied()),
                    unknown,
                };
                for heap_only in [false, true] {
                    for named_on_left in [false, true] {
                        let (minted, blanket) = if named_on_left {
                            (
                                super::overlap(&named, &partner, frame, heap_only),
                                super::overlap(&blanket_set, &partner, frame, heap_only),
                            )
                        } else {
                            (
                                super::overlap(&partner, &named, frame, heap_only),
                                super::overlap(&partner, &blanket_set, frame, heap_only),
                            )
                        };
                        assert_eq!(
                            minted.is_some(),
                            blanket.is_some(),
                            "a field root must conflict exactly when Unknown does: partner \
                             {partner:?} heap_only={heap_only} minted={minted:?} \
                             blanket={blanket:?}"
                        );
                        compared += 1;
                    }
                }
            }
        }
        assert_eq!(compared, 232, "exact comparison count");
    });
}
