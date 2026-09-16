//! Wave 6 — the nested-edit composition in the AST pass (relay 009 §3):
//! an OUTER edit rendered over a RE-RENDERED inner. Two shapes: a seam over a
//! seam (wave-5c's `kmRay2IntersectTriangle` reduction — the return family's
//! shared reborrow of the raw-returning `kmVec2Subtract(..)` over the
//! shared-weakening of one of its arguments) and a use graft over a
//! receiver-input view (wave-6o's optional store over this lane's
//! native-result view). The fixture `RAY` is wave-5c's verbatim reduction
//! (`decision/returned_child_tests.rs`), copied so none of their files move.

use super::RewriteOutcome;

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

fn ray_fixture() -> String {
    format!(
        "#![allow(dead_code,unused_unsafe,unused_mut,unused_assignments,unused_variables,non_snake_case,non_camel_case_types)]\n{RAY}"
    )
}

fn rewrite(input: &str) -> RewriteOutcome {
    super::rewrite_core_injected(
        ::utils::compilation::str_to_input(input),
        None,
        super::MAX_REVERT_ROUNDS,
        &|_| {},
        false,
        false,
        false,
        Some((
            super::A5Mode::PreciseReplay,
            Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
        )),
    )
}

/// wave-5c's reduction of heman's `kmRay2IntersectTriangle`: the return
/// family's shared reborrow of the raw-returning `kmVec2Subtract(..)`
/// (`c-raw-reborrow-shared`, `kmVec2Length`'s class) strictly contains the
/// shared weakening of the call's second argument (`shared-weakening`,
/// `kmVec2Subtract`'s class). Before: `cross-class-interval-collision` held
/// both classes and, through their dependents, every subject of the fixture
/// (13 `signature-class-held` rows, nothing delivered). Now: the L07 row
/// admits the containment, the AST pass grafts the inner first and builds
/// the outer over the adapted subtree, the byte projection omits the inner
/// range; every class places, 0 reverts, and the call reads
/// `kmVec2Length(&*kmVec2Subtract(&mut tmp, &(intersect), &(*ray).start))`.
#[test]
fn w6l_shared_reborrow_composes_over_the_weakened_argument() {
    let input = ray_fixture();
    let RewriteOutcome::Emitted {
        source,
        degradations,
        reverted_count,
        raw_boundary_artifacts,
        ..
    } = rewrite(&input)
    else {
        panic!("ray emission degraded")
    };
    println!("W6L-RAY-EMITTED reverted={reverted_count}\n{source}\nW6L-RAY-END\n{degradations:?}");
    assert_eq!(reverted_count, 0);
    let text = source.split_whitespace().collect::<String>();
    assert!(
        text.contains("kmVec2Length(&*kmVec2Subtract(&muttmp,&(intersect),&(*ray).start))"),
        "{text}"
    );
    assert!(text.contains("fnkmVec2Length(pIn:&kmVec2)->f32"), "{text}");
    // `kmVec2Subtract` hands `pOut` back: the dead-return tie (wave 4 of
    // this lane) borrows the return from that parameter.
    assert!(
        text.contains(
            "fnkmVec2Subtract<'a>(pOut:&'amutkmVec2,pV1:&kmVec2,pV2:*constkmVec2)->&'amutkmVec2"
        ),
        "{text}"
    );
    assert!(
        text.contains("fnkmRay2IntersectTriangle(ray:&kmRay2,p1:&kmVec2,p2:&kmVec2,p3:&kmVec2,intersection:&mutkmVec2,distance_out:&mutf32)->u8"),
        "{text}"
    );
    assert!(
        !degradations
            .iter()
            .any(|d| format!("{:?}", d.reason).contains("SignatureClassHeld")),
        "{degradations:?}"
    );
    assert!(
        raw_boundary_artifacts.class_collisions.lines().count() <= 1,
        "{}",
        raw_boundary_artifacts.class_collisions
    );
}
