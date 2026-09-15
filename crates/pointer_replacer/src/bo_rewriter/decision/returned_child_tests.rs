//! W-C5: a shared view borrowed into a contract-less local callee that may
//! hand a pointer back. Reduced from heman's `kmRay2IntersectTriangle` (`ray`,
//! at `8e84dc6d`: `borrowed-into-raw-param`, the site `kmVec2Subtract arg 2`
//! blocked `ordinary-argument-permission:write-through-shared-view`).

const RAY: &str = r###"
#[derive(Copy, Clone)]
#[repr(C)]
pub struct kmVec2 { pub x: f32, pub y: f32 }
#[derive(Copy, Clone)]
#[repr(C)]
pub struct kmRay2 { pub start: kmVec2, pub dir: kmVec2 }
pub unsafe fn kmVec2Subtract(pOut: *mut kmVec2, pV1: *const kmVec2, pV2: *const kmVec2) -> *mut kmVec2 {
    (*pOut).x = (*pV1).x - (*pV2).x;
    (*pOut).y = (*pV1).y - (*pV2).y;
    return pOut;
}
pub unsafe fn kmVec2Length(pIn: *const kmVec2) -> f32 { ((*pIn).x * (*pIn).x + (*pIn).y * (*pIn).y).sqrt() }
pub unsafe fn kmVec2Dot(pV1: *const kmVec2, pV2: *const kmVec2) -> f32 { (*pV1).x * (*pV2).x + (*pV1).y * (*pV2).y }
pub unsafe fn kmRay2IntersectLineSegment(ray: *const kmRay2, p1: *const kmVec2, p2: *const kmVec2, intersection: *mut kmVec2) -> u8 {
    let ua = ((*p2).x - (*p1).x) * ((*ray).start.y - (*p1).y) - ((*p2).y - (*p1).y) * ((*ray).start.x - (*p1).x);
    if ua >= 0.0 && ua <= 1.0 {
        (*intersection).x = (*ray).start.x + ua * (*ray).dir.x;
        (*intersection).y = (*ray).start.y + ua * (*ray).dir.y;
        return 1;
    }
    0
}
pub unsafe fn kmRay2IntersectTriangle(ray: *const kmRay2, p1: *const kmVec2, p2: *const kmVec2, p3: *const kmVec2,
    intersection: *mut kmVec2, distance_out: *mut f32) -> u8 {
    let mut intersect = kmVec2 { x: 0., y: 0. };
    let mut final_intersect = kmVec2 { x: 0., y: 0. };
    let mut distance = 10000.0f32;
    let mut intersected = 0u8;
    if kmRay2IntersectLineSegment(ray, p1, p2, &mut intersect) != 0 {
        let mut tmp = kmVec2 { x: 0., y: 0. };
        let this_distance = kmVec2Length(kmVec2Subtract(&mut tmp, &mut intersect, &(*ray).start));
        let mut this_normal = kmVec2 { x: (*p2).y - (*p1).y, y: (*p1).x - (*p2).x };
        if this_distance < distance && kmVec2Dot(&mut this_normal, &(*ray).dir) < 0.0f32 {
            final_intersect.x = intersect.x;
            final_intersect.y = intersect.y;
            distance = this_distance;
            intersected = 1;
        }
    }
    if intersected != 0 {
        (*intersection).x = final_intersect.x;
        (*intersection).y = final_intersect.y;
        if distance != 0. { *distance_out = distance; }
    }
    intersected
}
"###;

fn fixture() -> String {
    format!(
        "#![allow(dead_code,unused_unsafe,unused_mut,unused_assignments,unused_variables,non_snake_case,non_camel_case_types)]\n{RAY}"
    )
}

fn decisions(input: &str) -> Vec<(String, super::Decision)> {
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        crate::bo_rewriter::decide_table_with_ctx_config(
            tcx,
            Some((
                crate::bo_rewriter::A5Mode::PreciseReplay,
                Some(crate::bo_rewriter::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .unwrap()
        .0
        .entries
        .iter()
        .map(|(s, d)| (s.label.clone(), d.clone()))
        .collect()
    })
    .unwrap()
}

fn decision<'a>(table: &'a [(String, super::Decision)], label: &str) -> &'a super::Decision {
    &table
        .iter()
        .find(|(l, _)| l == label)
        .unwrap_or_else(|| panic!("{label}"))
        .1
}

/// `ray` is borrowed (`&(*ray).start`) into `kmVec2Subtract`'s raw `pV2`; the
/// callee hands `pOut` back and the caller uses it (`kmVec2Length(…)`), so
/// K18′'s read-only walk cannot admit it. `pV2`'s summary is `NoRetain` and
/// `kmVec2` reaches no pointer: nothing handed back descends from `ray`.
#[test]
fn w5c_returned_child_pointer_free_no_retain_admits_the_shared_view() {
    let input = fixture();
    let table = decisions(&input);
    assert!(
        matches!(
            decision(&table, "kmRay2IntersectTriangle::ray"),
            super::Decision::Ref { mutable: false }
        ),
        "{:?}",
        decision(&table, "kmRay2IntersectTriangle::ray")
    );
    // The site itself: T1 `ref-shared-to-raw-const` on the local summary.
    let site = ::utils::compilation::run_compiler_on_str(&input, |tcx| {
        let (_, ctx) = crate::bo_rewriter::decide_table_with_ctx_config(
            tcx,
            Some((
                crate::bo_rewriter::A5Mode::PreciseReplay,
                Some(crate::bo_rewriter::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .unwrap();
        ctx.raw_boundary
            .receipts_tsv()
            .lines()
            .filter(|l| {
                l.contains("kmRay2IntersectTriangle::ray#1") && l.contains("kmVec2Subtract\t2")
            })
            .map(str::to_owned)
            .collect::<Vec<_>>()
    })
    .unwrap();
    assert!(
        site.iter()
            .any(|l| l.contains("\tT1\tref-shared-to-raw-const\t")),
        "{site:?}"
    );
    let emitted = crate::bo_rewriter::emit_tests::ast_emitted_source_of(&input).unwrap();
    let text = emitted.split_whitespace().collect::<Vec<_>>().join(" ");
    // `&kmVec2` coerces to `*const kmVec2`: the T1 site needs no bridge text.
    // (Whether the owner's CLASS is applied is a placement fact: over the
    // batch-8 composition the return reborrow of `kmVec2Subtract(…)` and this
    // argument's glue nest across two classes — report 015.)
    assert!(
        text.contains("kmVec2Subtract(&mut tmp, &mut intersect, &(*ray).start)"),
        "{emitted}"
    );
    assert!(crate::bo_rewriter::verify::type_checks_str(&emitted));
    if let Ok(root) = std::env::var("CRAT_W5C_FIXTURE_CAPTURE") {
        std::fs::create_dir_all(&root).unwrap();
        std::fs::write(format!("{root}/ray-triangle-original.rs"), &input).unwrap();
        std::fs::write(format!("{root}/ray-triangle-emitted.rs"), &emitted).unwrap();
    }
}

/// W-C5's own verdict: the ARGUMENT's pointee (`kmVec2`, what `pV2` points
/// to) reaching a pointer could hand a child back through a load, so the
/// pointee is not pointer-free and W-C5 admits nothing. (The final decision
/// is no longer this control's to assert: over the batch-8 composition
/// another lane's returned-child evidence admits the site on its own — the
/// pointer handed back is `pOut`, argument 0 — which is sound here.)
#[test]
fn w5c_returned_child_pointer_bearing_pointee_is_not_pointer_free() {
    let input = fixture()
        .replace(
            "pub struct kmVec2 { pub x: f32, pub y: f32 }",
            "pub struct kmVec2 { pub x: f32, pub y: f32, pub aux: *mut f32 }",
        )
        .replace(
            "kmVec2 { x: 0., y: 0. }",
            "kmVec2 { x: 0., y: 0., aux: 0 as *mut f32 }",
        )
        .replace(
            "y: (*p1).x - (*p2).x }",
            "y: (*p1).x - (*p2).x, aux: 0 as *mut f32 }",
        );
    let parameters = |input: &str| {
        ::utils::compilation::run_compiler_on_str(input, |tcx| {
            let vec2 = tcx
                .hir_body_owners()
                .find(|d| tcx.item_name(d.to_def_id()).as_str() == "kmVec2Subtract")
                .unwrap();
            super::returned_child_descent::pointer_free_parameters(tcx, vec2).collect::<Vec<_>>()
        })
        .unwrap()
    };
    assert!(parameters(&input).is_empty());
    assert_eq!(parameters(&fixture()), vec![0, 1, 2]);
}

/// A callee that hands the argument itself back retains it: the view stays
/// refused whatever the pointee holds.
#[test]
fn w5c_returned_child_returned_argument_stays_refused() {
    let input = fixture().replace(
        "    (*pOut).y = (*pV1).y - (*pV2).y;\n    return pOut;",
        "    (*pOut).y = (*pV1).y - (*pV2).y;\n    return pV2 as *mut kmVec2;",
    );
    let table = decisions(&input);
    assert!(
        !matches!(
            decision(&table, "kmRay2IntersectTriangle::ray"),
            super::Decision::Ref { .. }
        ),
        "{:?}",
        decision(&table, "kmRay2IntersectTriangle::ray")
    );
}

/// A callee whose retention is unknown (it passes the argument on to an
/// opaque function, a T2-waived boundary) may hand the argument back; a
/// pointer-free pointee does not settle that, so the view stays refused.
#[test]
fn w5c_returned_child_unknown_retention_stays_refused() {
    let input = fixture()
        .replace(
            "pub unsafe fn kmVec2Subtract(",
            "extern \"C\" { fn opaque(p: *const kmVec2) -> *mut kmVec2; }\npub unsafe fn kmVec2Subtract(",
        )
        .replace(
            "    (*pOut).y = (*pV1).y - (*pV2).y;\n    return pOut;",
            "    (*pOut).y = (*pV1).y - (*pV2).y;\n    return opaque(pV2);",
        );
    let table = decisions(&input);
    assert!(
        !matches!(
            decision(&table, "kmRay2IntersectTriangle::ray"),
            super::Decision::Ref { .. }
        ),
        "{:?}",
        decision(&table, "kmRay2IntersectTriangle::ray")
    );
}
