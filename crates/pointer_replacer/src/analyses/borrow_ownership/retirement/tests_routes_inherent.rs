//! Row (0) ROUTE-INHERENT-METHOD: an unresolved inherent-method callee must not
//! decline the program (R245-1). Witnesses Z-W01..Z-W07, killers Z-K01..Z-K04.

/// Z-W01 getter: a free function retires, an unrelated frame calls an inherent
/// getter. The Ref selection is OUTSIDE any hold set (R307-2), so this is a clean
/// RED (no model at all) before the row and GREEN after it.
const GETTER: &str = r#"
unsafe extern "C" { fn free(p: *mut core::ffi::c_void); }
#[repr(C)] pub struct S { flags: u32 }
impl S { pub unsafe fn is_set(&self) -> bool { self.flags != 0 } }
pub unsafe fn probe(s: *mut S) -> bool { (*s).is_set() }
pub unsafe fn keeper(p: *const u8) -> u8 { *p }
pub unsafe fn releaser(q: *mut u8) { free(q as *mut core::ffi::c_void); }
"#;

/// Z-W02 setter: same shape through a `&mut self` inherent setter.
const SETTER: &str = r#"
unsafe extern "C" { fn free(p: *mut core::ffi::c_void); }
#[repr(C)] pub struct S { flags: u32 }
impl S { pub unsafe fn set(&mut self, v: u32) { self.flags = v; } }
pub unsafe fn probe(s: *mut S) { (*s).set(1); }
pub unsafe fn keeper(p: *const u8) -> u8 { *p }
pub unsafe fn releaser(q: *mut u8) { free(q as *mut core::ffi::c_void); }
"#;

/// Z-W06 control: the same program with the inherent method replaced by a free
/// function. It has no unresolved route, so it must be ACCEPTED both before and
/// after the row -- this is what makes Z-W01's RED attributable to the impl call.
const FREE_FUNCTION_CONTROL: &str = r#"
unsafe extern "C" { fn free(p: *mut core::ffi::c_void); }
#[repr(C)] pub struct S { flags: u32 }
pub unsafe fn is_set(s: *mut S) -> bool { (*s).flags != 0 }
pub unsafe fn probe(s: *mut S) -> bool { is_set(s) }
pub unsafe fn keeper(p: *const u8) -> u8 { *p }
pub unsafe fn releaser(q: *mut u8) { free(q as *mut core::ffi::c_void); }
"#;

#[test]
fn z_w06_control_free_function_callee_is_accepted() {
    assert!(
        super::tests::accepts(FREE_FUNCTION_CONTROL, &[("keeper", 1, 0)]),
        "the control must be accepted: it differs from Z-W01 only by the callee being a free function"
    );
}

#[test]
fn z_w01_inherent_getter_callee_must_not_decline_the_program() {
    assert!(
        super::tests::accepts(GETTER, &[("keeper", 1, 0)]),
        "an unresolved inherent-method callee is a coverage residual and must never decline the program (R245-1)"
    );
}

#[test]
fn z_w02_inherent_setter_callee_must_not_decline_the_program() {
    assert!(
        super::tests::accepts(SETTER, &[("keeper", 1, 0)]),
        "an inherent setter callee declines exactly as the getter does"
    );
}

/// Z-W03: the Ref is live ACROSS the unresolved call in the immediate caller.
/// The unknown-retirement event's object is the TOP set, so it overlaps this Ref
/// and the analysis must demote it. Read with Z-W01, a `false` here cannot be
/// "the program declined": Z-W01 shows this class of program now yields a model.
const ACROSS_IMMEDIATE: &str = r#"
unsafe extern "C" { fn free(p: *mut core::ffi::c_void); }
#[repr(C)] pub struct S { flags: u32, held: *mut u8 }
impl S { pub unsafe fn touch(&mut self) { free(self.held as *mut core::ffi::c_void); self.flags += 1; } }
pub unsafe fn caller(s: *mut S) -> u32 {
    let before = (*s).flags;
    (*s).touch();
    before + (*s).flags
}
pub unsafe fn keeper(p: *const u8) -> u8 { *p }
"#;

/// Z-W07 (R308-2): the grand-caller. `g` holds a Ref into an object it passes to
/// `f`, and `f` makes the unresolved inherent call. Nothing in `g` is an
/// unresolved call, so an immediate-frame hold could never reach it: only the
/// event's propagation through the g -> f route can demote this Ref.
const ACROSS_GRANDCALLER: &str = r#"
unsafe extern "C" { fn free(p: *mut core::ffi::c_void); }
#[repr(C)] pub struct S { flags: u32, held: *mut u8 }
impl S { pub unsafe fn touch(&mut self) { free(self.held as *mut core::ffi::c_void); self.flags += 1; } }
pub unsafe fn f(s: *mut S) { (*s).touch(); }
pub unsafe fn g(s: *mut S) -> u32 {
    let before = (*s).flags;
    f(s);
    before + (*s).flags
}
pub unsafe fn keeper(p: *const u8) -> u8 { *p }
"#;

/// Z-P01 (report-only, re-authored per R309-1 item 2): the first draft selected
/// `s` while `f(s)` passed that very pointer, so `s` was in use AT the call the
/// event sits on and demotion was the required outcome -- the draft could not
/// have reported anything. Here the selected Ref `s` is dead before the call and
/// a DIFFERENT pointer `t` is passed, so nothing about `s` is in use at or after
/// the event. Report whether it survives; no behaviour is asserted.
const BEFORE_ONLY: &str = r#"
unsafe extern "C" { fn free(p: *mut core::ffi::c_void); }
#[repr(C)] pub struct S { flags: u32, held: *mut u8 }
impl S { pub unsafe fn touch(&mut self) { free(self.held as *mut core::ffi::c_void); self.flags += 1; } }
pub unsafe fn f(t: *mut S) { (*t).touch(); }
pub unsafe fn g(s: *mut S, t: *mut S) -> u32 {
    let before = (*s).flags;
    f(t);
    before
}
pub unsafe fn keeper(p: *const u8) -> u8 { *p }
"#;

/// Z-W05: the exact corpus shape. brotli's 38 `CallKind::Impl` sites are calls to
/// `c2rust_bitfields` accessors whose bodies borrow a bitfield and hand it to a
/// RustLib target -- here `u32::from` -- so the callee body itself contains no
/// local call and no retirement. Under row (0) the program must be ACCEPTED; the
/// receiver's own demotion is what row (0') LEAF-CALLEE-EXEMPTION addresses.
const BROTLI_ACCESSOR_SHAPE: &str = r#"
#[repr(C)] pub struct Bits { raw: [u8; 4] }
#[repr(C)] pub struct State { bits: Bits, data: *mut u8 }
impl State {
    pub unsafe fn large_window(&self) -> u32 {
        let field = &self.bits.raw;
        u32::from(field[0])
    }
    pub unsafe fn set_large_window(&mut self, v: u8) {
        let field = &mut self.bits.raw;
        field[0] = v;
    }
}
pub unsafe fn probe(s: *mut State) -> u32 {
    (*s).set_large_window(1);
    (*s).large_window()
}
pub unsafe fn keeper(p: *const u8) -> u8 { *p }
"#;

#[test]
fn z_w03_ref_live_across_the_unresolved_call_is_demoted_in_the_caller() {
    assert!(
        !super::tests::accepts(ACROSS_IMMEDIATE, &[("caller", 1, 0)]),
        "the unknown-retirement event's TOP object overlaps a Ref live across the call; it must be demoted"
    );
    assert!(
        super::tests::accepts(ACROSS_IMMEDIATE, &[("keeper", 1, 0)]),
        "the same program still yields a model, so the demotion above is a demotion and not a decline"
    );
}

#[test]
fn z_w07_the_event_propagates_through_the_route_to_the_grand_caller() {
    assert!(
        !super::tests::accepts(ACROSS_GRANDCALLER, &[("g", 1, 0)]),
        "an immediate-frame hold cannot reach g: only route propagation of the unknown-retirement event can \
         demote a Ref held one frame above the unresolved call"
    );
    assert!(
        super::tests::accepts(ACROSS_GRANDCALLER, &[("keeper", 1, 0)]),
        "the same program still yields a model, so the demotion above is a demotion and not a decline"
    );
}

#[test]
fn z_p01_report_only_caller_ref_dead_before_the_call_on_another_pointer() {
    let survives = super::tests::accepts(BEFORE_ONLY, &[("g", 1, 0)]);
    println!("receipt.Z-P01 ref_dead_before_call_other_pointer_passed survives={survives}");
}

#[test]
fn z_w05_the_exact_brotli_accessor_shape_is_accepted() {
    assert!(
        super::tests::accepts(BROTLI_ACCESSOR_SHAPE, &[("keeper", 1, 0)]),
        "the corpus shape that declines brotli on every era-5 frame must yield a model (R245-1)"
    );
    let receiver = super::tests::accepts(BROTLI_ACCESSOR_SHAPE, &[("probe", 1, 0)]);
    println!(
        "receipt.Z-W05 accessor_receiver_survives={receiver} (row(0) alone measured false; row(0') leaf exemption turns it true)"
    );
}

/// Z-W04: the receipt, at review level, on the production path.
///
/// R308-2 named `Demotion.source` as the join. It is not this class's channel:
/// `local_outcome::Reason` carries only `InnerLoanMissing` and `OwnerMissing`
/// (the P1'-S demotion channel), while an `UnknownObjects` overlap is recorded as
/// a `RetirementConflict` -- which is exactly what the R286 evidence files show
/// for this row category. The receipt therefore joins
/// `RetirementConflict.source -> Coverage::UnresolvedCalleeEffects`, and carries
/// the conflict's own `target_key` as the affected slot.
#[test]
fn z_w04_receipt_joins_conflicts_to_unresolved_callee_coverage() {
    use rustc_hir::{ItemKind, OwnerNode};

    use crate::{
        analyses::borrow_ownership::{
            borrow_verify::with_mode_a_commit_trace,
            construction::{
                CopyLendMode, TestValidationBackend, construct_bo_into,
                verify_bo_construction_counting_for_test,
            },
            crate_slots::CrateSlots,
            export::with_bo_export,
            mutability_facts::MutFacts,
            origins::compute_origins,
            solver::KindSolver,
            source_events::Coverage,
        },
        utils::rustc::RustProgram,
    };

    ::utils::compilation::run_compiler_on_str(ACROSS_IMMEDIATE, |tcx| {
        let mut functions = Vec::new();
        let mut structs = Vec::new();
        for owner in tcx.hir_crate(()).owners.iter() {
            let Some(owner) = owner.as_owner() else { continue };
            let OwnerNode::Item(item) = owner.node() else { continue };
            match item.kind {
                ItemKind::Fn { .. } => functions.push(item.owner_id.def_id),
                ItemKind::Struct(..) => structs.push(item.owner_id.def_id),
                _ => {}
            }
        }
        let program = RustProgram {
            tcx,
            functions,
            structs,
        };
        let slots = CrateSlots::build(&program);
        let origins = compute_origins(&program);
        let facts = MutFacts::from_program(&program);
        let (keys, export) = with_bo_export(|| {
            let solver = KindSolver::new(&slots);
            let construction = construct_bo_into(
                &program,
                &slots,
                &origins,
                &facts,
                &solver,
                CopyLendMode::Baseline,
            )
            .expect("production construction");
            let keys: Vec<_> = construction
                .source_events
                .retirements
                .iter()
                .filter(|(_, event)| event.coverage == Coverage::UnresolvedCalleeEffects)
                .map(|(key, _)| key.clone())
                .collect();
            let _ = with_mode_a_commit_trace(|| {
                verify_bo_construction_counting_for_test(
                    &program,
                    &slots,
                    &origins,
                    &solver,
                    &construction,
                    &facts,
                    TestValidationBackend::HardCheckRoundOptimize,
                )
            });
            keys
        });
        assert!(
            !keys.is_empty(),
            "the unresolved-callee event must be present in the production inventory"
        );
        let mut rows = 0usize;
        let mut affected = std::collections::BTreeSet::new();
        for review in &export.retirement_rounds {
            for conflict in &review.conflicts {
                if keys.contains(&conflict.source) {
                    rows += 1;
                    affected.insert(conflict.target_key.clone());
                    println!(
                        "receipt.route:unknown-function:inherent-method slot={} overlap={:?}",
                        conflict.target_key, conflict.overlap
                    );
                }
            }
        }
        assert!(
            rows > 0,
            "each affected slot must carry route:unknown-function:inherent-method, joined through \
             RetirementConflict.source -> Coverage::UnresolvedCalleeEffects"
        );
        println!(
            "receipt.Z-W04 events={} conflict_rows={} distinct_slots={}",
            keys.len(),
            rows,
            affected.len()
        );
    })
    .unwrap_or_else(|error| error.raise())
}

// ---------------------------------------------------------------- row (0') ----
// R309-1 LEAF-CALLEE-EXEMPTION. A leaf callee retires nothing that propagates
// and calls nothing, so it gets neither event nor route. Z-W05 measured the RED:
// under row (0) alone the accessor receiver does NOT survive.

/// Z-W09 non-leaf by an explicit `free` in the callee body.
const NON_LEAF_FREE: &str = r#"
unsafe extern "C" { fn free(p: *mut core::ffi::c_void); }
#[repr(C)] pub struct S { p: *mut u8 }
impl S { pub unsafe fn release(&mut self) { free(self.p as *mut core::ffi::c_void); } }
pub unsafe fn probe(s: *mut S) -> *mut u8 {
    (*s).release();
    (*s).p
}
pub unsafe fn keeper(q: *const u8) -> u8 { *q }
"#;

/// Z-W10 non-leaf by a Drop terminator in the callee body.
const NON_LEAF_DROP: &str = r#"
#[repr(C)] pub struct S { p: *mut u8 }
impl S { pub unsafe fn take(&mut self) { let _b = Box::from_raw(self.p); } }
pub unsafe fn probe(s: *mut S) -> *mut u8 {
    (*s).take();
    (*s).p
}
pub unsafe fn keeper(q: *const u8) -> u8 { *q }
"#;

#[test]
fn z_w08_leaf_accessor_receiver_survives_as_ref() {
    assert!(
        super::tests::accepts(BROTLI_ACCESSOR_SHAPE, &[("probe", 1, 0)]),
        "a leaf accessor retires nothing and calls nothing, so the receiver must keep its Ref;          Z-W05 recorded this as false under row (0) alone"
    );
}

#[test]
fn z_w09_non_leaf_callee_that_frees_still_demotes_the_receiver() {
    assert!(
        !super::tests::accepts(NON_LEAF_FREE, &[("probe", 1, 0)]),
        "a callee whose body frees is NOT leaf; the unknown-retirement event must still demote the receiver"
    );
    assert!(
        super::tests::accepts(NON_LEAF_FREE, &[("keeper", 1, 0)]),
        "and the program is still accepted, so the line above is a demotion and not a decline"
    );
}

#[test]
fn z_w10_non_leaf_callee_with_a_drop_terminator_demotes_the_receiver() {
    assert!(
        !super::tests::accepts(NON_LEAF_DROP, &[("probe", 1, 0)]),
        "a Drop terminator in the callee body makes it non-leaf; the receiver must be demoted"
    );
    assert!(
        super::tests::accepts(NON_LEAF_DROP, &[("keeper", 1, 0)]),
        "and the program is still accepted"
    );
}
