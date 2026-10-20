//! C18 controls for named descendants, storage kills, joins, and repair depth.

use super::*;

fn named_local(fixture: &Fixture, name: &str) -> Local {
    let locals: std::collections::BTreeSet<_> = fixture
        .named_locals
        .iter()
        .filter(|(found, _)| found == name)
        .map(|(_, local)| *local)
        .collect();
    assert_eq!(locals.len(), 1, "exact source binding {name}");
    *locals.iter().next().unwrap()
}

fn free_location(fixture: &Fixture) -> Location {
    let calls: Vec<_> = fixture
        .calls
        .iter()
        .filter(|(name, _)| name == "free")
        .collect();
    assert_eq!(calls.len(), 1, "one independently identified source free");
    calls[0].1
}

#[test]
fn e5_p_named_reborrow_and_deref_descendants_keep_entry_origin() {
    let mut missing = Vec::new();
    for (code, name, depth) in [
        (
            "pub unsafe fn reborrow(p: *mut u8) -> u8 { let q = &mut *p; *q }",
            "reborrow",
            0,
        ),
        (
            "pub unsafe fn loaded(pp: *mut *mut u8) -> u8 { let q = *pp; *q }",
            "loaded",
            1,
        ),
    ] {
        let fixture = fixture(code, name, &[(1, depth)]);
        let entry = key(&fixture, 1, depth);
        let target = IncomingTarget {
            entry,
            dereferences: depth + 1,
        };
        let q = named_local(&fixture, "q");
        assert_ne!(q, entry.parameter);
        assert_eq!(fixture.analysis.entries.len(), 1);
        let descendants: Vec<_> = fixture
            .analysis
            .binding_facts
            .iter()
            .filter(|fact| {
                fact.function == entry.function
                    && fact.local == q
                    && fact.depth == 0
                    && fact.moment == EntryMoment::AtEvent
            })
            .collect();
        if descendants.is_empty() {
            missing.push(name);
        }
        for fact in descendants {
            assert_eq!(
                fact.target, target,
                "the exact named q must retain its incoming target"
            );
        }
    }
    assert!(
        missing.is_empty(),
        "named descendant facts missing for {missing:?}"
    );
}

#[test]
fn e5_p_storage_dead_removes_named_descendant_without_ending_entry() {
    const CODE: &str = "unsafe extern \"C\" { fn free(p: *mut u8); } pub unsafe fn scoped(p: *mut u8) -> u8 { let value; { let q = p; value = *q; } free(p); value }";
    // Check the fixture's actual MIR lifetime event, independently of the
    // producer's missing-fact convention and without executing the program.
    ::utils::compilation::run_compiler_on_str(CODE, |tcx| {
        let function = tcx.hir_crate(()).owners.iter().filter_map(|owner| {
            let OwnerNode::Item(item) = owner.as_owner()?.node() else { return None };
            (matches!(item.kind, ItemKind::Fn { .. })
                && tcx.item_name(item.owner_id.def_id.to_def_id()).as_str() == "scoped")
                .then_some(item.owner_id.def_id)
        }).next().expect("source function");
        let body = tcx.mir_drops_elaborated_and_const_checked(function).borrow();
        let q = body.var_debug_info.iter().find_map(|info| {
            if info.name.as_str() != "q" { return None; }
            let rustc_middle::mir::VarDebugInfoContents::Place(place) = info.value else { return None };
            place.as_local()
        }).expect("debug-named q storage");
        let frees: Vec<_> = body.basic_blocks.iter_enumerated().filter_map(|(block, data)| {
            let call = data.terminator().as_call(tcx)?;
            matches!(call.func, CallKind::LibC(name) if name.as_str() == "free")
                .then_some(Location { block, statement_index: data.statements.len() })
        }).collect();
        assert_eq!(frees.len(), 1);
        let free = frees[0];
        let dominators = body.basic_blocks.dominators();
        assert!(body.basic_blocks.iter_enumerated().any(|(block, data)| {
            data.statements.iter().enumerate().any(|(index, statement)| {
                matches!(statement.kind, rustc_middle::mir::StatementKind::StorageDead(local) if local == q)
                    && if block == free.block { index < free.statement_index }
                       else { dominators.dominates(block, free.block) }
            })
        }), "the exact named q must have StorageDead before free(p)");
    }).unwrap_or_else(|error| error.raise());

    let fixture = fixture(CODE, "scoped", &[(1, 0)]);
    let entry = key(&fixture, 1, 0);
    let q = named_local(&fixture, "q");
    let target = IncomingTarget {
        entry,
        dereferences: 1,
    };
    assert!(
        fixture.analysis.binding_facts.iter().any(|fact| {
            fact.function == entry.function
                && fact.local == q
                && fact.depth == 0
                && fact.target == target
        }),
        "q must have been a known descendant before its storage died"
    );
    let free = free_location(&fixture);
    assert!(
        !fixture.analysis.binding_facts.iter().any(|fact| {
            fact.function == entry.function
                && fact.local == q
                && fact.location == free
                && fact.phase == SourcePhase::Call
                && fact.moment == EntryMoment::AtEvent
        }),
        "dead q must not survive as a current descendant"
    );
    let point = observation(
        &fixture,
        entry,
        free,
        SourcePhase::Call,
        EntryMoment::AtEvent,
    );
    assert!(point.live);
    assert_eq!(point.demand, Some(entry));
    assert_eq!(point.target, target);
}

#[test]
fn e5_p_conditional_and_loop_rebindings_join_without_changing_entry_target() {
    const PREAMBLE: &str = "unsafe extern \"C\" { fn free(p: *mut u8); }";
    for (source, name, stays_known) in [
        (
            "pub unsafe fn different(mut p: *mut u8, other: *mut u8, choose: bool) -> bool { let alias = p; if choose { p = other; } free(alias); p.is_null() }",
            "different",
            false,
        ),
        (
            "pub unsafe fn same(mut p: *mut u8, _other: *mut u8, choose: bool) -> bool { let alias = p; if choose { p = p; } free(alias); p.is_null() }",
            "same",
            true,
        ),
        (
            "pub unsafe fn looped(mut p: *mut u8, other: *mut u8, choose: bool) -> bool { let alias = p; let mut remaining = 2u8; while remaining != 0 { let copied = other; if choose { p = copied; } remaining -= 1; } free(alias); p.is_null() }",
            "looped",
            false,
        ),
    ] {
        let fixture = fixture(&format!("{PREAMBLE} {source}"), name, &[(1, 0)]);
        let entry = key(&fixture, 1, 0);
        let target = IncomingTarget {
            entry,
            dereferences: 1,
        };
        assert_eq!(named_local(&fixture, "p"), entry.parameter);
        assert_eq!(
            fixture.analysis.entries.len(),
            1,
            "Raw replacements do not create protectors"
        );
        let free = free_location(&fixture);
        let point = observation(
            &fixture,
            entry,
            free,
            SourcePhase::Call,
            EntryMoment::AtEvent,
        );
        assert!(point.live);
        assert_eq!(point.demand, Some(entry));
        assert_eq!(point.target, target);
        assert_eq!(
            point.current_binding,
            if stays_known {
                CurrentBinding::Incoming(target)
            } else {
                CurrentBinding::Unknown
            },
            "converged current binding for {name}"
        );
        let current: Vec<_> = fixture
            .analysis
            .binding_facts
            .iter()
            .filter(|fact| {
                fact.function == entry.function
                    && fact.local == entry.parameter
                    && fact.depth == 0
                    && fact.location == free
                    && fact.phase == SourcePhase::Call
                    && fact.moment == EntryMoment::AtEvent
            })
            .collect();
        if stays_known {
            assert_eq!(current.len(), 1);
            assert_eq!(current[0].target, target);
        } else {
            assert!(
                current.is_empty(),
                "ambiguous current origin must remain Unknown"
            );
        }
        // The loop only checks the merged binding and the stable incoming
        // obligation. Its iterations supply no dynamic-generation equality.
    }
}

#[test]
fn e5_p_inner_depth_invalidation_repairs_its_exact_registered_slot() {
    let fixture = fixture(
        "unsafe extern \"C\" { fn free(p: *mut u8); } pub unsafe fn inner(pp: *mut *mut u8) { let q = *pp; free(q); }",
        "inner",
        &[(1, 1)],
    );
    let outer = key(&fixture, 1, 0);
    let inner = key(&fixture, 1, 1);
    assert_ne!(outer.slot, inner.slot);
    assert_eq!(
        fixture
            .analysis
            .entries
            .iter()
            .map(|entry| entry.key)
            .collect::<Vec<_>>(),
        vec![inner]
    );
    let target = IncomingTarget {
        entry: inner,
        dereferences: 2,
    };
    assert_eq!(obligation(&fixture, inner).target, target);
    let free = free_location(&fixture);
    let point = observation(
        &fixture,
        inner,
        free,
        SourcePhase::Call,
        EntryMoment::AtEvent,
    );
    assert_eq!(point.target, target);
    assert_eq!(point.demand, Some(inner));
    assert_eq!(
        fixture.analysis.repair_target_for_invalidation(
            inner,
            free,
            SourcePhase::Call,
            EntryMoment::AtEvent,
        ),
        Ok(Some(inner.slot))
    );
    assert_eq!(
        fixture.analysis.repair_target_for_invalidation(
            outer,
            free,
            SourcePhase::Call,
            EntryMoment::AtEvent,
        ),
        Err(EntryCoverageError::MissingEntry(outer))
    );
}
