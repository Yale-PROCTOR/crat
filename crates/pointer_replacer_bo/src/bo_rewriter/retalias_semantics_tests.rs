//! RB-RETALIAS RED controls over actual fixture models and original MIR.
//! These controls neither inject decisions nor use a corpus/cache entry point.
//! The write twin witnesses model admission protection. It does not discharge
//! the outstanding shared-parent child-permission consumer witness.

use std::collections::BTreeSet;

use rustc_middle::{
    mir::{
        BasicBlock, Body, Local, Location, Operand, ProjectionElem, Rvalue, StatementKind,
        TerminatorKind, VarDebugInfoContents,
        visit::{NonMutatingUseContext, PlaceContext, Visitor},
    },
    ty::TyKind,
};

use super::{
    bridge_receipt::{
        BridgeCalleeId, BridgeReceiptStage, BridgeReceiptState, BridgeRetentionTier,
        SignatureClassId,
    },
    decision::{
        Decision, DegradeReason,
        raw_boundary::{RAW_BOUNDARY_WAIVER_ID, RawBoundaryDisposition},
        raw_boundary_contracts::{PointeeAccess, classify_contract},
        return_alias::{self, ReturnUseState},
    },
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ChildCase {
    Discarded,
    CopiedRead,
    CopiedWrite,
}

fn input(case: ChildCase) -> String {
    // **R285-3 / R217-2 — the parent read is offset, and that is the whole
    // migration.** `strchr` reads to the NUL, so route (A)'s
    // `held:thin-extent` holds a THIN source at this position, correctly. The
    // retained-alias question these cases ask is about the returned CHILD's
    // tier, not about the parent's width, and every returned-parent row in the
    // pinned table is many-element — so the fixture gives the parent an
    // evidence-backed extent and settles a shared SLICE instead of a thin
    // reference. `shared()` already admitted `Slice { mutable: false }`; the
    // child relation, the T1/T2 split and the write twin's model-Raw
    // protection are untouched.
    //
    // The extent witness is a SEPARATE read, deliberately: the parent's own
    // direct load stays exactly one, which is what the consumed-load assertion
    // below counts, and would have gone to zero had the offset replaced it.
    let body = match case {
        ChildCase::Discarded => {
            "strchr(p, 65); let extent_witness = *p.offset(1);\n\
            let parent_read = *p; parent_read"
        }
        ChildCase::CopiedRead => {
            "let child = strchr(p, 65); let copied = child;\n\
            let extent_witness = *p.offset(1);\n\
            let parent_read = *p;\n\
            if copied.is_null() { parent_read } else { parent_read ^ *copied }"
        }
        ChildCase::CopiedWrite => {
            "let child = strchr(p, 65); let copied = child;\n\
            let extent_witness = *p.offset(1);\n\
            let parent_read = *p;\n\
            if copied.is_null() { parent_read } else { *copied = 66; parent_read }"
        }
    };
    // The sole caller owns writable NUL-terminated storage. The raw const
    // cast does not make that storage immutable; no original Rust shared
    // reference remains live over the child's guarded write.
    format!(
        "#![allow(dead_code, unused_variables, unused_unsafe)]\n\
         extern \"C\" {{ fn strchr(s: *const i8, c: i32) -> *mut i8; }}\n\
         unsafe fn target(p: *const i8) -> i8 {{ {body} }}\n\
         pub unsafe fn entry() -> i8 {{\n\
             let mut storage: [i8; 2] = [65, 0];\n\
             target(storage.as_mut_ptr() as *const i8)\n\
         }}\n"
    )
}

fn named_local(body: &Body<'_>, name: &str) -> Local {
    let locals = body
        .var_debug_info
        .iter()
        .filter_map(|info| {
            let VarDebugInfoContents::Place(place) = &info.value else { return None };
            (info.name.as_str() == name)
                .then(|| place.as_local())
                .flatten()
        })
        .collect::<BTreeSet<_>>();
    assert_eq!(
        locals.len(),
        1,
        "one actual MIR local for {name}: {locals:?}"
    );
    *locals.first().unwrap()
}

fn pointer_copies(body: &Body<'_>, root: Local) -> BTreeSet<Local> {
    let mut locals = BTreeSet::from([root]);
    loop {
        let before = locals.len();
        for data in body.basic_blocks.iter() {
            for statement in &data.statements {
                let StatementKind::Assign(assignment) = &statement.kind else { continue };
                let (destination, value) = &**assignment;
                let Some(destination) = destination.as_local() else { continue };
                let source = match value {
                    Rvalue::Use(operand) | Rvalue::Cast(_, operand, _) => {
                        operand.place().and_then(|place| place.as_local())
                    }
                    _ => None,
                };
                if source.is_some_and(|source| locals.contains(&source))
                    && matches!(body.local_decls[destination].ty.kind(), TyKind::RawPtr(..))
                {
                    locals.insert(destination);
                }
            }
        }
        if locals.len() == before {
            return locals;
        }
    }
}

fn assert_copy_chain_before_call(body: &Body<'_>, root: Local, argument: Local, call: Location) {
    assert_eq!(
        call.statement_index,
        body.basic_blocks[call.block].statements.len(),
        "copy-chain proof is anchored at the exact call terminator"
    );
    let mut current = argument;
    let mut before = call.statement_index;
    let mut seen = BTreeSet::new();
    let mut chain = Vec::new();
    while current != root {
        assert!(
            seen.insert(current),
            "copy-chain proof cannot contain a cycle"
        );
        let mut definitions = Vec::new();
        for (block, data) in body.basic_blocks.iter_enumerated() {
            for (statement_index, statement) in data.statements.iter().enumerate() {
                if let StatementKind::Assign(assignment) = &statement.kind
                    && assignment.0.as_local() == Some(current)
                {
                    definitions.push(Location {
                        block,
                        statement_index,
                    });
                }
            }
            assert!(
                !matches!(&data.terminator().kind,
                TerminatorKind::Call { destination, .. } if destination.as_local() == Some(current)),
                "a transparent argument temporary cannot also be a call result"
            );
        }
        assert_eq!(
            definitions.len(),
            1,
            "one definition for transparent temporary {current:?}"
        );
        let definition = definitions[0];
        assert_eq!(
            definition.block, call.block,
            "the observed copy is in the exact call block"
        );
        assert!(
            definition.statement_index < before,
            "each copy must precede its dependent use"
        );
        let StatementKind::Assign(assignment) =
            &body.basic_blocks[definition.block].statements[definition.statement_index].kind
        else {
            unreachable!("definition was collected from an assignment")
        };
        let Rvalue::Use(Operand::Copy(source) | Operand::Move(source)) = &assignment.1 else {
            panic!("argument lineage requires an actual transparent copy: {assignment:?}");
        };
        let source = source
            .as_local()
            .expect("transparent copy source is a plain local");
        assert!(matches!(
            body.local_decls[current].ty.kind(),
            TyKind::RawPtr(..)
        ));
        assert_eq!(
            body.local_decls[current].ty, body.local_decls[source].ty,
            "argument copy preserves the exact pointer type"
        );
        chain.push((source, current, definition));
        current = source;
        before = definition.statement_index;
    }
    chain.reverse();
    println!(
        "RB-RETALIAS exact argument copy chain: root={root:?}, argument={argument:?}, call={call:?}, chain={chain:?}"
    );
}

fn reachable(body: &Body<'_>, start: BasicBlock, target: BasicBlock) -> bool {
    let mut seen = BTreeSet::new();
    let mut pending = vec![start];
    while let Some(block) = pending.pop() {
        if !seen.insert(block) {
            continue;
        }
        if block == target {
            return true;
        }
        pending.extend(body.basic_blocks[block].terminator().successors());
    }
    false
}

struct ValueReads {
    local: Local,
    count: usize,
}

impl<'tcx> Visitor<'tcx> for ValueReads {
    fn visit_place(
        &mut self,
        place: &rustc_middle::mir::Place<'tcx>,
        context: PlaceContext,
        location: Location,
    ) {
        if place.as_local() == Some(self.local)
            && matches!(
                context,
                PlaceContext::NonMutatingUse(
                    NonMutatingUseContext::Copy | NonMutatingUseContext::Move
                )
            )
        {
            self.count += 1;
        }
        self.super_place(place, context, location);
    }
}

fn shared(decision: &Decision) -> bool {
    matches!(
        decision,
        Decision::Ref { mutable: false } | Decision::Slice { mutable: false, .. }
    )
}

fn check(case: ChildCase) {
    let source = input(case);
    let emitted = ::utils::compilation::run_compiler_on_str(&source, |tcx| {
        let capture = super::ast_transform::capture_ast(tcx).expect("RB-RETALIAS original AST capture");
        let (result, commits) = crate::analyses::borrow_ownership::borrow_verify::with_mode_a_commit_trace(|| {
            super::decide_table_with_ctx_config(tcx, Some((
                crate::analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay,
                Some(crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph),
            )))
        });
        let (table, ctx) = result.expect("RB-RETALIAS actual fixture decision pipeline");
        let solve = super::model_cache::solve_receipt();
        println!("RB-RETALIAS {case:?} solve receipt: {solve:#?}");
        assert!(solve.is_some(), "actual fixture solve receipt is mandatory");

        let (subject, decided) = table.entries.iter()
            .find(|(subject, _)| subject.label == "target::p")
            .expect("actual target::p subject");
        let kind = ctx.slots.fn_local_slots.get(&subject.fn_did)
            .and_then(|slots| slots.slot_for_local_depth(subject.local, 0))
            .and_then(|slot| ctx.model.get(&super::SlotRef::Local(subject.fn_did, slot)))
            .copied();
        // Admission diagnosis only: observe the same solve and original MIR
        // before any premise assertion. No mode, fact, input, or decision is
        // changed, and no additional solver invocation is introduced.
        let body = tcx.mir_drops_elaborated_and_const_checked(subject.fn_did).borrow();
        let pointer_locals = body.local_decls.iter_enumerated().filter_map(|(local, declaration)| {
            if !matches!(declaration.ty.kind(), TyKind::RawPtr(..) | TyKind::Ref(..)) { return None; }
            let slot = ctx.slots.fn_local_slots.get(&subject.fn_did)
                .and_then(|slots| slots.slot_for_local_depth(local, 0));
            let model = slot.and_then(|slot| ctx.model.get(&super::SlotRef::Local(subject.fn_did, slot)));
            Some((local, format!("{:?}", declaration.ty), slot, model.copied(),
                ctx.mut_facts.is_mutable(subject.fn_did, local), ctx.mut_facts.is_defaulted(subject.fn_did, local)))
        }).collect::<Vec<_>>();
        let origin_flows = ctx.analysis.origins.as_ref()
            .and_then(|origins| origins.try_native_flows())
            .and_then(|flows| flows.get(&subject.fn_did))
            .map(|flow| flow.body.depth0_value_flows());
        println!("RB-RETALIAS admission {case:?}: source={source:?}\nrepair_mode={:?}\nmode_a_commits={commits:#?}\npointer_locals=(local,type,slot,kind,mutable,defaulted){pointer_locals:#?}\norigin_flows={origin_flows:#?}\noriginal_target_mir={body:#?}",
            crate::analyses::borrow_ownership::borrow_verify::RepairMode::current());
        let (_, candidate) = ctx.hypothetical.entries.iter()
            .find(|(candidate, _)| candidate.fn_did == subject.fn_did && candidate.hir_id == subject.hir_id)
            .expect("original production candidate for target::p");
        if case == ChildCase::CopiedWrite {
            assert_eq!(kind, Some(super::SlotKind::Raw),
                "the unchanged write twin is protected at model admission");
            assert!(ctx.mut_facts.is_mutable(subject.fn_did, subject.local)
                && !ctx.mut_facts.is_defaulted(subject.fn_did, subject.local),
                "write-twin parent mutability must be an actual Foster fact");
            for decision in [candidate, decided] {
                assert!(matches!(decision, Decision::Degraded(record) if record.reason == DegradeReason::KindRaw),
                    "model-Raw protection must survive both decision stages: {decision:?}");
            }
        } else {
            assert_eq!(kind, Some(super::SlotKind::Ref),
                "AUTHORING PREMISE: source must be actual model-Ref, never sourceRaw: {case:?}");
            assert!(shared(candidate),
                "AUTHORING PREMISE: a real shared borrowed candidate is required: {case:?}, {candidate:?}");
        }

        let calls = body.basic_blocks.iter_enumerated().filter_map(|(block, data)| {
            let TerminatorKind::Call { func, args, destination, target, .. } = &data.terminator().kind else { return None };
            let TyKind::FnDef(callee, _) = *func.constant()?.ty().kind() else { return None };
            if tcx.item_name(callee).as_str() != "strchr" { return None; }
            assert!(matches!(tcx.hir_node_by_def_id(callee.expect_local()), rustc_hir::Node::ForeignItem(_)),
                "the call must resolve to the declared foreign item");
            let location = Location { block, statement_index: data.statements.len() };
            let parent_argument = args[0].node.place().and_then(|place| place.as_local())
                .expect("the returned parent argument has a plain MIR local");
            assert_copy_chain_before_call(&body, subject.local, parent_argument, location);
            Some((location, callee, *destination, *target, parent_argument))
        }).collect::<Vec<_>>();
        assert_eq!(calls.len(), 1, "exactly one resolved return-alias call");
        let (call, callee, destination, normal_target, parent_argument) = calls[0];
        let destination = destination.as_local().expect("plain returned-child destination premise");
        let normal_target = normal_target.expect("normal returning-call premise");
        let observation = return_alias::observe(&body, call);
        assert_eq!(observation.destination.as_ref().map(|destination| destination.local), Some(destination));
        assert_eq!(observation.state, if case == ChildCase::Discarded { ReturnUseState::Unused } else { ReturnUseState::Used },
            "actual returned-result use premise: {observation:?}");

        let parent_read = named_local(&body, "parent_read");
        let mut consumed = ValueReads { local: parent_read, count: 0 };
        consumed.visit_body(&body);
        assert!(consumed.count > 0, "parent read must be consumed, not a discarded observation");
        let mut parent_loads = Vec::new();
        let mut child_reads = Vec::new();
        let mut child_writes = Vec::new();
        let descendants = pointer_copies(&body, destination);
        for (block, data) in body.basic_blocks.iter_enumerated() {
            for (statement_index, statement) in data.statements.iter().enumerate() {
                let StatementKind::Assign(assignment) = &statement.kind else { continue };
                let (lhs, rhs) = &**assignment;
                let location = Location { block, statement_index };
                if let Rvalue::Use(Operand::Copy(place) | Operand::Move(place)) = rhs
                    && matches!(place.projection.first(), Some(ProjectionElem::Deref))
                {
                    if place.local == subject.local && lhs.as_local() == Some(parent_read) {
                        parent_loads.push(location);
                    }
                    if descendants.contains(&place.local) { child_reads.push(location); }
                }
                if descendants.contains(&lhs.local)
                    && matches!(lhs.projection.first(), Some(ProjectionElem::Deref))
                {
                    child_writes.push(location);
                }
            }
        }
        assert_eq!(parent_loads.len(), 1, "one actual consumed parent load: {body:?}");
        assert!(reachable(&body, normal_target, parent_loads[0].block), "parent load must follow the call");
        if case != ChildCase::Discarded {
            let child = named_local(&body, "child");
            let copied = named_local(&body, "copied");
            assert_ne!(child, copied, "the copy must have its own actual MIR local");
            assert!(descendants.contains(&child) && pointer_copies(&body, child).contains(&copied),
                "the copied local must descend from the actual returned destination");
            if case == ChildCase::CopiedWrite {
                let slot = |local| super::SlotRef::Local(subject.fn_did,
                    ctx.slots.fn_local_slots[&subject.fn_did].slot_for_local_depth(local, 0)
                        .expect("observed pointer local has a model slot"));
                let copied_slot = slot(copied);
                let parent_argument_slot = slot(parent_argument);
                assert_eq!(crate::analyses::borrow_ownership::borrow_verify::RepairMode::current(),
                    crate::analyses::borrow_ownership::borrow_verify::RepairMode::ModeA);
                assert!(commits.iter().any(|commit| commit.target == copied_slot
                    && commit.conflict.issuer == Some(parent_argument_slot)
                    && commit.conflict.requirers.contains(&copied_slot)),
                    "the copied child must have an actual Mode-A conflict commitment: {commits:?}");
                assert!(commits.iter().any(|commit| commit.target == parent_argument_slot
                    && commit.conflict.issuer == Some(parent_argument_slot)),
                    "the parent argument must have its actual Mode-A protection: {commits:?}");
            }
            let null_checks = body.basic_blocks.iter_enumerated().filter_map(|(block, data)| {
                let TerminatorKind::Call { func, args, destination, target, .. } = &data.terminator().kind else { return None };
                let TyKind::FnDef(callee, _) = *func.constant()?.ty().kind() else { return None };
                if tcx.item_name(callee).as_str() != "is_null" { return None; }
                assert_eq!(args.len(), 1, "the null check takes exactly its receiver");
                let argument = args[0].node.place().and_then(|place| place.as_local())
                    .expect("the null-check receiver has a plain MIR local");
                assert_copy_chain_before_call(&body, copied, argument,
                    Location { block, statement_index: data.statements.len() });
                Some((block, *destination, *target))
            }).collect::<Vec<_>>();
            assert_eq!(null_checks.len(), 1, "the copied child has its actual non-null guard");
            let (guard_call, guard_result, guard_target) = null_checks[0];
            let guard_target = guard_target.expect("null check returns to its branch");
            let TerminatorKind::SwitchInt { discr, targets } = &body.basic_blocks[guard_target].terminator().kind else {
                panic!("AUTHORING PREMISE: null-check result must select the actual child-access branch: {body:?}");
            };
            assert_eq!(discr.place().and_then(|place| place.as_local()), guard_result.as_local(),
                "the branch tests this exact is_null result");
            let nonnull = targets.target_for_value(0);
            let null = targets.target_for_value(1);
            let accesses = if case == ChildCase::CopiedWrite { &child_writes } else { &child_reads };
            assert!(!accesses.is_empty(), "required child access must exist: {case:?}, {body:?}");
            assert!(accesses.iter().all(|location| reachable(&body, guard_call, location.block)
                && reachable(&body, nonnull, location.block) && !reachable(&body, null, location.block)
                && reachable(&body, parent_loads[0].block, location.block)),
                "child accesses must follow the consumed parent read only on the non-null branch");
        }
        assert_eq!(child_writes.is_empty(), case != ChildCase::CopiedWrite,
            "the twins must differ in actual child write evidence");

        let sites = ctx.raw_boundary.inventoried_sites().filter(|(key, _, _)|
            key.caller == tcx.def_path_str(subject.fn_did.to_def_id())
                && key.block == call.block.as_u32() && key.statement_index as usize == call.statement_index
                && key.callee.path == tcx.def_path_str(callee) && key.argument_index == 0
        ).collect::<Vec<_>>();
        assert_eq!(sites.len(), 1, "one exact original-MIR parent boundary site");
        let (key, disposition, site) = sites[0];
        assert!(key.callee.foreign && site.target_stays_raw);
        assert_eq!(site.node, Some((subject.fn_did, subject.hir_id)));
        let contract = classify_contract(&key.callee, 0, &site.target).expect("exact strchr contract");
        assert_eq!(contract.returns_alias_of, Some(0));
        assert_eq!(contract.access, PointeeAccess::Read);
        println!("RB-RETALIAS {case:?}: model={kind:?}, candidate={candidate:?}, final={decided:?}, observation={observation:?}, child_reads={child_reads:?}, child_writes={child_writes:?}, disposition={disposition:?}");
        if case != ChildCase::CopiedWrite && disposition.is_open() {
            assert!(shared(decided),
                "AUTHORING PREMISE: an open bridge must have an actual decided shared borrowed source: {decided:?}");
        }
        match case {
            ChildCase::Discarded => assert!(matches!(disposition, RawBoundaryDisposition::T1 { .. }),
                "a provably discarded returned child keeps the T1 contrast: {disposition:?}"),
            ChildCase::CopiedRead => assert!(matches!(disposition, RawBoundaryDisposition::T2 { waiver_id, .. } if *waiver_id == RAW_BOUNDARY_WAIVER_ID),
                "a used readonly returned child requires the exact T2 waiver: {disposition:?}"),
            ChildCase::CopiedWrite => println!(
                "RB-RETALIAS copied-write: model-admission-protected; shared-parent-permission-consumer-witness=outstanding"),
        }

        let emission = super::emit_files(tcx, &table, &rustc_hash::FxHashSet::default(),
            &ctx.retained_c9_plans).expect("RB-RETALIAS terminal emission plan");
        let held = emission.plan.held_classes();
        let reverts = super::ast_transform::revert_set_from_classes_and_atoms(
            &held, &BTreeSet::new(), &table).expect("actual held-class reverts");
        let (files, _, _, _) = super::ast_transform::ast_emitted_files_from(
            tcx, &capture, &reverts, emission.plan.root_file.as_ref(), &table,
            Some(&emission.plan.terminal_call_plans)).expect("RB-RETALIAS AST emission");
        assert_eq!(files.len(), 1, "the unchanged fixture emits one complete source file");
        let emitted = files.into_values().next().unwrap();
        let events = emission.plan.bridge_events(&held);
        println!("RB-RETALIAS delivered {case:?}: held={held:?}\nbridge_events={events:#?}\nemitted_source={emitted}");
        if case != ChildCase::CopiedWrite {
            let owner = SignatureClassId::of(subject.fn_did);
            assert!(emission.plan.class_finalization.classes.get(&owner)
                .is_some_and(super::plan::SignatureClassPlan::is_ready),
                "shared source class must be terminally Ready: {:?}", emission.plan.class_finalization);
            assert!(!held.contains(&owner) && reverts.keeps(owner),
                "the shared source class must survive the actual AST revert set");
            let terminal_form = super::terminal_subject_form(&table, &emission.plan.class_finalization,
                (subject.fn_did, subject.hir_id));
            assert!(matches!(terminal_form,
                super::decision::seam::Form::Ref { mutable: false }
                    | super::decision::seam::Form::Slice { mutable: false }),
                "the applied source interface must remain shared borrowed: {terminal_form:?}");

            let source_file = tcx.sess.source_map().lookup_source_file(site.span.lo());
            let file = match super::file_key(&source_file.name).expect("exact strchr site file") {
                super::plan::FileKey::Real(path) => path.display().to_string(),
                super::plan::FileKey::Virtual(name) => name,
            };
            let lo = site.span.lo().0 - source_file.start_pos.0;
            let hi = site.span.hi().0 - source_file.start_pos.0;
            let same_site = events.iter().filter(|event| event.site.owner_class == owner
                && event.site.caller == subject.fn_did
                && event.site.callee == BridgeCalleeId::Foreign(key.callee.path.clone())
                && event.site.arm == "c" && event.site.position == "arg0"
                && event.site.file == file && event.site.lo == lo && event.site.hi == hi)
                .collect::<Vec<_>>();
            assert_eq!(same_site.iter().filter(|event| event.stage == BridgeReceiptStage::Plan).count(), 1,
                "the exact original strchr argument has one bridge plan: {same_site:#?}");
            let terminal = same_site.iter().filter(|event| event.stage == BridgeReceiptStage::Terminal)
                .collect::<Vec<_>>();
            assert_eq!(terminal.len(), 1, "the exact original strchr argument has one terminal bridge: {same_site:#?}");
            let terminal = terminal[0];
            assert_eq!(terminal.state, BridgeReceiptState::Applied,
                "a planned/held receipt cannot stand in for delivery: {terminal:#?}");
            assert_eq!(terminal.expected_form, "raw");
            assert_eq!(terminal.found_form, terminal_form.key());
            let (tier, waiver) = if case == ChildCase::Discarded {
                (BridgeRetentionTier::T1, None)
            } else {
                (BridgeRetentionTier::T2, Some(RAW_BOUNDARY_WAIVER_ID))
            };
            assert_eq!(terminal.retention, tier, "terminal tier at the exact strchr site");
            assert_eq!(terminal.waiver_id.as_deref(), waiver, "terminal waiver at the exact strchr site");
        }
        emitted
    }).expect("owned-storage RB-RETALIAS input type-checks");
    assert!(
        super::verify::type_checks_str(&emitted),
        "RB-RETALIAS final emitted tree must type/borrow-check: {case:?}\n{emitted}"
    );
    let declarations = super::delivery_custody::inventory_source("retalias-delivered.rs", &emitted)
        .expect("independent final-source declaration inventory");
    let parent = declarations
        .iter()
        .find(|declaration| {
            declaration.owner == "target"
                && declaration.binding == "p"
                && declaration.parameter_index == Some(1)
        })
        .expect("the actual delivered target::p declaration");
    if case == ChildCase::CopiedWrite {
        assert!(
            matches!(
                parent.type_shape,
                super::delivery_custody::TypeShape::RawPointer { mutable: false, .. }
            ),
            "the model-admission negative must remain raw in the final source: {parent:?}"
        );
    } else {
        assert!(
            matches!(
                parent.type_shape,
                super::delivery_custody::TypeShape::Reference { mutable: false, .. }
            ),
            "the shared source must actually be delivered as a borrowed declaration: {parent:?}"
        );
    }
}

#[test]
fn retalias_semantics_discarded_child_keeps_t1() {
    check(ChildCase::Discarded);
}

#[test]
fn retalias_semantics_copied_readonly_child_requires_t2() {
    check(ChildCase::CopiedRead);
}

#[test]
fn retalias_semantics_copied_child_write_is_model_admission_protected() {
    check(ChildCase::CopiedWrite);
}
