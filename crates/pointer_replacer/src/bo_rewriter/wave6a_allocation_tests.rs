//! wave-6a — allocation-rooted forms (seat addendum 400, R400-3).
//!
//! Rule **W6A-B1** (`decision/slice_local_construction.rs`): an unannotated
//! slice local is typed by its sealed constructor, so the dissolution's veto
//! keeps its `Slice` decision and the planner places no declaration splice;
//! a safe slice handed to a settled slice parameter is a zero-syntax pass.
//!
//! Corpus-derived fixtures: heman `transform_to_distance` + `edt` and
//! `transform_to_coordfield` + `edt_with_payload` (shape (b),
//! `slice-local-construction`), quadtree `quadtree_node_new` + `test_node`
//! (shape (a): a callee returning a fresh allocation — the frame read).

/// quadtree `src::src::node::quadtree_node_new` and `src::test::test_node`,
/// reduced: the struct keeps three pointer fields, the three predicate callees
/// keep their real bodies.
pub(super) const QUADTREE_NODE_NEW: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, non_camel_case_types)]
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}
#[repr(C)]
pub struct quadtree_node {
    pub ne: *mut quadtree_node,
    pub nw: *mut quadtree_node,
    pub point: *mut i32,
}
pub type quadtree_node_t = quadtree_node;
pub unsafe extern "C" fn quadtree_node_isleaf(mut node: *mut quadtree_node_t) -> i32 {
    return ((*node).point != 0 as *mut core::ffi::c_void as *mut i32) as i32;
}
pub unsafe extern "C" fn quadtree_node_isempty(mut node: *mut quadtree_node_t) -> i32 {
    return (((*node).nw).is_null() && ((*node).ne).is_null()
        && quadtree_node_isleaf(node) == 0) as i32;
}
pub unsafe extern "C" fn quadtree_node_new() -> *mut quadtree_node_t {
    let mut node = 0 as *mut quadtree_node_t;
    node = malloc(::std::mem::size_of::<quadtree_node_t>()) as *mut quadtree_node_t;
    if node.is_null() {
        return 0 as *mut quadtree_node_t;
    }
    (*node).ne = 0 as *mut quadtree_node;
    (*node).nw = 0 as *mut quadtree_node;
    (*node).point = 0 as *mut i32;
    return node;
}
pub unsafe extern "C" fn test_node() -> i32 {
    let mut node = quadtree_node_new();
    let mut ok = 0;
    if quadtree_node_isleaf(node) == 0 {
        ok += 1;
    }
    if quadtree_node_isempty(node) != 0 {
        ok += 1;
    }
    ok
}
"#;

/// heman `src::src::distance::transform_to_distance` and `edt`, reduced to the
/// first loop; the four scratch arrays and `edt`'s body are the corpus's.
pub(super) const HEMAN_TRANSFORM: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, non_camel_case_types)]
extern "C" {
    fn calloc(count: usize, size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}
#[repr(C)]
pub struct heman_image {
    pub width: i32,
    pub height: i32,
    pub data: *mut f32,
}
static INF: f32 = 1e20;
unsafe extern "C" fn edt(mut f: *mut f32, mut d: *mut f32, mut z: *mut f32, mut w: *mut u16, mut n: i32) {
    let mut k = 0 as i32;
    let mut s: f32 = 0.;
    *w.offset(0 as i32 as isize) = 0 as i32 as u16;
    *z.offset(0 as i32 as isize) = -INF;
    *z.offset(1 as i32 as isize) = INF;
    let mut q = 1 as i32;
    while q < n {
        s = (*f.offset(q as isize) + (q * q) as f32
            - (*f.offset(*w.offset(k as isize) as isize)
                + (*w.offset(k as isize) as i32 * *w.offset(k as isize) as i32) as f32))
            / (2 as i32 * q - 2 as i32 * *w.offset(k as isize) as i32) as f32;
        while s <= *z.offset(k as isize) {
            k -= 1;
            s = (*f.offset(q as isize) + (q * q) as f32
                - (*f.offset(*w.offset(k as isize) as isize)
                    + (*w.offset(k as isize) as i32 * *w.offset(k as isize) as i32) as f32))
                / (2 as i32 * q - 2 as i32 * *w.offset(k as isize) as i32) as f32;
        }
        k += 1;
        *w.offset(k as isize) = q as u16;
        *z.offset(k as isize) = s;
        *z.offset((k + 1 as i32) as isize) = INF;
        q += 1;
    }
    k = 0 as i32;
    let mut q_0 = 0 as i32;
    while q_0 < n {
        while *z.offset((k + 1 as i32) as isize) < q_0 as f32 {
            k += 1;
        }
        *d.offset(q_0 as isize) = ((q_0 - *w.offset(k as isize) as i32)
            * (q_0 - *w.offset(k as isize) as i32)) as f32
            + *f.offset(*w.offset(k as isize) as isize);
        q_0 += 1;
    }
}
unsafe extern "C" fn transform_to_distance(mut sdf: *mut heman_image) {
    let mut width = (*sdf).width;
    let mut height = (*sdf).height;
    let mut size = width * height;
    let mut ff = calloc(size as usize, ::std::mem::size_of::<f32>()) as *mut f32;
    let mut dd = calloc(size as usize, ::std::mem::size_of::<f32>()) as *mut f32;
    let mut zz = calloc(((height + 1 as i32) * (width + 1 as i32)) as usize, ::std::mem::size_of::<f32>()) as *mut f32;
    let mut ww = calloc(size as usize, ::std::mem::size_of::<u16>()) as *mut u16;
    let mut x: i32 = 0;
    x = 0 as i32;
    while x < width {
        let mut f = ff.offset((height * x) as isize);
        let mut d = dd.offset((height * x) as isize);
        let mut z = zz.offset(((height + 1 as i32) * x) as isize);
        let mut w = ww.offset((height * x) as isize);
        let mut y = 0 as i32;
        while y < height {
            *f.offset(y as isize) = *((*sdf).data).offset(((y * width) as isize) + (x as isize));
            y += 1;
        }
        edt(f, d, z, w, height);
        let mut y_0 = 0 as i32;
        while y_0 < height {
            *((*sdf).data).offset(((y_0 * width) as isize) + (x as isize)) = *d.offset(y_0 as isize);
            y_0 += 1;
        }
        x += 1;
    }
    let mut y_1: i32 = 0;
    y_1 = 0 as i32;
    while y_1 < height {
        let mut f_0 = ff.offset((width * y_1) as isize);
        let mut d_0 = dd.offset((width * y_1) as isize);
        let mut z_0 = zz.offset(((width + 1 as i32) * y_1) as isize);
        let mut w_0 = ww.offset((width * y_1) as isize);
        let mut x_0 = 0 as i32;
        while x_0 < width {
            *f_0.offset(x_0 as isize) = *((*sdf).data).offset(((y_1 * width) as isize) + (x_0 as isize));
            x_0 += 1;
        }
        edt(f_0, d_0, z_0, w_0, width);
        let mut x_1 = 0 as i32;
        while x_1 < width {
            *((*sdf).data).offset(((y_1 * width) as isize) + (x_1 as isize)) = *d_0.offset(x_1 as isize);
            x_1 += 1;
        }
        y_1 += 1;
    }
    free(ff as *mut core::ffi::c_void);
    free(dd as *mut core::ffi::c_void);
    free(zz as *mut core::ffi::c_void);
    free(ww as *mut core::ffi::c_void);
}
"#;

/// heman `src::src::distance::transform_to_coordfield` and `edt_with_payload`,
/// reduced to the first loop; the payload arrays are the corpus's per-column
/// `calloc`/`free` pair beside the four computed views.
pub(super) const HEMAN_COORDFIELD: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, non_camel_case_types)]
extern "C" {
    fn calloc(count: usize, size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}
#[repr(C)]
pub struct heman_image {
    pub width: i32,
    pub height: i32,
    pub data: *mut f32,
}
static INF: f32 = 1e20;
unsafe extern "C" fn edt_with_payload(mut f: *mut f32, mut d: *mut f32, mut z: *mut f32, mut w: *mut u16, mut n: i32, mut payload_in: *mut f32, mut payload_out: *mut f32) {
    let mut k = 0 as i32;
    let mut s: f32 = 0.;
    *w.offset(0 as i32 as isize) = 0 as i32 as u16;
    *z.offset(0 as i32 as isize) = -INF;
    *z.offset(1 as i32 as isize) = INF;
    let mut q = 1 as i32;
    while q < n {
        s = (*f.offset(q as isize) + (q * q) as f32
            - (*f.offset(*w.offset(k as isize) as isize)
                + (*w.offset(k as isize) as i32 * *w.offset(k as isize) as i32) as f32))
            / (2 as i32 * q - 2 as i32 * *w.offset(k as isize) as i32) as f32;
        while s <= *z.offset(k as isize) {
            k -= 1;
            s = (*f.offset(q as isize) + (q * q) as f32
                - (*f.offset(*w.offset(k as isize) as isize)
                    + (*w.offset(k as isize) as i32 * *w.offset(k as isize) as i32) as f32))
                / (2 as i32 * q - 2 as i32 * *w.offset(k as isize) as i32) as f32;
        }
        k += 1;
        *w.offset(k as isize) = q as u16;
        *z.offset(k as isize) = s;
        *z.offset((k + 1 as i32) as isize) = INF;
        q += 1;
    }
    k = 0 as i32;
    let mut q_0 = 0 as i32;
    while q_0 < n {
        while *z.offset((k + 1 as i32) as isize) < q_0 as f32 {
            k += 1;
        }
        *d.offset(q_0 as isize) = ((q_0 - *w.offset(k as isize) as i32)
            * (q_0 - *w.offset(k as isize) as i32)) as f32
            + *f.offset(*w.offset(k as isize) as isize);
        *payload_out.offset((q_0 * 2 as i32) as isize) =
            *payload_in.offset((*w.offset(k as isize) as i32 * 2 as i32) as isize);
        *payload_out.offset((q_0 * 2 as i32 + 1 as i32) as isize) =
            *payload_in.offset((*w.offset(k as isize) as i32 * 2 as i32 + 1 as i32) as isize);
        q_0 += 1;
    }
}
unsafe extern "C" fn transform_to_coordfield(mut sdf: *mut heman_image, mut cf: *mut heman_image) {
    let mut width = (*sdf).width;
    let mut height = (*sdf).height;
    let mut size = width * height;
    let mut ff = calloc(size as usize, ::std::mem::size_of::<f32>()) as *mut f32;
    let mut dd = calloc(size as usize, ::std::mem::size_of::<f32>()) as *mut f32;
    let mut zz = calloc(((height + 1 as i32) * (width + 1 as i32)) as usize, ::std::mem::size_of::<f32>()) as *mut f32;
    let mut ww = calloc(size as usize, ::std::mem::size_of::<u16>()) as *mut u16;
    let mut x: i32 = 0;
    x = 0 as i32;
    while x < width {
        let mut pl1 = calloc((height * 2 as i32) as usize, ::std::mem::size_of::<f32>()) as *mut f32;
        let mut pl2 = calloc((height * 2 as i32) as usize, ::std::mem::size_of::<f32>()) as *mut f32;
        let mut f = ff.offset((height * x) as isize);
        let mut d = dd.offset((height * x) as isize);
        let mut z = zz.offset(((height + 1 as i32) * x) as isize);
        let mut w = ww.offset((height * x) as isize);
        let mut y = 0 as i32;
        while y < height {
            *f.offset(y as isize) = *((*sdf).data).offset(((y * width) as isize) + (x as isize));
            *pl1.offset((y * 2 as i32) as isize) =
                *((*cf).data).offset(((2 as i32 * (y * width + x)) as isize) + (0 as i32 as isize));
            *pl1.offset((y * 2 as i32 + 1 as i32) as isize) =
                *((*cf).data).offset(((2 as i32 * (y * width + x)) as isize) + (1 as i32 as isize));
            y += 1;
        }
        edt_with_payload(f, d, z, w, height, pl1, pl2);
        let mut y_0 = 0 as i32;
        while y_0 < height {
            *((*sdf).data).offset(((y_0 * width) as isize) + (x as isize)) = *d.offset(y_0 as isize);
            *((*cf).data).offset(((2 as i32 * (y_0 * width + x)) as isize) + (0 as i32 as isize)) =
                *pl2.offset((2 as i32 * y_0) as isize);
            *((*cf).data).offset(((2 as i32 * (y_0 * width + x)) as isize) + (1 as i32 as isize)) =
                *pl2.offset((2 as i32 * y_0 + 1 as i32) as isize);
            y_0 += 1;
        }
        free(pl1 as *mut core::ffi::c_void);
        free(pl2 as *mut core::ffi::c_void);
        x += 1;
    }
    free(ff as *mut core::ffi::c_void);
    free(dd as *mut core::ffi::c_void);
    free(zz as *mut core::ffi::c_void);
    free(ww as *mut core::ffi::c_void);
}
"#;

/// The corpus census runs A5 in precise-replay mode over the frozen benchmark
/// graph; the fixtures run the same configuration so site proofs resolve.
pub(super) fn rewrite_precise(name: &str, src: &str) -> super::RewriteOutcome {
    use super::{A5Mode, WholeProgramAttestation};
    let dir = std::env::temp_dir().join(format!("crat-wave6a-{name}-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let root = dir.join("lib.rs");
    std::fs::write(&root, src).unwrap();
    let result = super::rewrite_m1_path_a5_injected(
        &root,
        A5Mode::PreciseReplay,
        Some(WholeProgramAttestation::FrozenBenchmarkGraph),
        &|_| {},
    );
    std::fs::remove_dir_all(dir).unwrap();
    result
}

pub(super) struct Emitted {
    pub(super) source: String,
    pub(super) reverted: usize,
    pub(super) emitted: usize,
    pub(super) degradations: Vec<super::decision::Degradation>,
    pub(super) artifacts: super::RawBoundaryArtifacts,
}

pub(super) fn emitted(name: &str, src: &str) -> Emitted {
    match rewrite_precise(name, src) {
        super::RewriteOutcome::Emitted {
            source,
            degradations,
            reverted_count,
            emitted_count,
            raw_boundary_artifacts,
            ..
        } => Emitted {
            source,
            reverted: reverted_count,
            emitted: emitted_count,
            degradations,
            artifacts: raw_boundary_artifacts,
        },
        super::RewriteOutcome::Degraded {
            reason,
            degradations,
            first_diags,
            ..
        } => panic!("{name} must emit: {reason}\n{degradations:#?}\n{first_diags:#?}"),
    }
}

pub(super) fn compact(text: &str) -> String {
    text.chars().filter(|c| !c.is_whitespace()).collect()
}

pub(super) fn reason_of(
    degradations: &[super::decision::Degradation],
    subject: &str,
) -> Option<String> {
    degradations
        .iter()
        .find(|d| d.subject == subject)
        .map(|d| d.reason.key().to_owned())
}

/// The corpus shape: four unannotated computed views over four distinct
/// `calloc` roots, two of them Slice-family (`f`, `d`), two thin (`z`, `w`).
/// Every `f`/`d` row becomes a fallback-extent `from_raw_parts_mut` view at
/// its own initializer, its element uses index, and the call to `edt` keeps
/// its text: `&mut [f32]` at `&[f32]` / `&mut [f32]` is Rust's own coercion.
#[test]
#[ignore = "W6A-B1 at the batch-6 head: the Return-stage class-finalizer wall (report 001 STOP 1, wave-5d) — GREEN at 30d69d95; un-ignore when the head carries the finalizer answer"]
fn w6a_b1_heman_transform_to_distance_delivers_the_four_computed_views() {
    let out = emitted("heman-distance", HEMAN_TRANSFORM);
    let src = compact(&out.source);
    assert_eq!(out.reverted, 0, "{}", out.source);
    for (local, root, offset) in [
        ("f", "ff", "(height*x)"),
        ("d", "dd", "(height*x)"),
        ("f_0", "ff", "(width*y_1)"),
        ("d_0", "dd", "(width*y_1)"),
    ] {
        let construction = format!(
            "letmut{local}:&mut[f32]=core::slice::from_raw_parts_mut({root}.offset({offset}asisize),crate::FALLBACK_SLICE_EXTENT);"
        );
        assert!(src.contains(&construction), "{local}: {}", out.source);
        assert_eq!(
            reason_of(
                &out.degradations,
                &format!("transform_to_distance::{local}")
            ),
            None,
            "{local} must not degrade: {:#?}",
            out.degradations
        );
    }
    // Element uses index; no raw offset use of a delivered view survives.
    assert!(src.contains("f[(y)asusize]="), "{}", out.source);
    assert!(src.contains("=d[(y_0)asusize];"), "{}", out.source);
    assert!(src.contains("f_0[(x_0)asusize]="), "{}", out.source);
    assert!(src.contains("=d_0[(x_1)asusize];"), "{}", out.source);
    for raw in ["*f.offset(", "*d.offset(", "*f_0.offset(", "*d_0.offset("] {
        assert!(!src.contains(&compact(raw)), "{raw}: {}", out.source);
    }
    // The calls keep their text: zero syntax at the settled slice parameters.
    assert!(src.contains("edt(f,d,z,w,height);"), "{}", out.source);
    assert!(
        src.contains("edt(f_0,d_0,z_0,w_0,width);"),
        "{}",
        out.source
    );
    // The thin views stay exactly where they were (their callee params hold).
    assert_eq!(
        reason_of(&out.degradations, "transform_to_distance::z").as_deref(),
        Some("copy-source-coupled")
    );
    assert_eq!(
        reason_of(&out.degradations, "transform_to_distance::w").as_deref(),
        Some("copy-source-coupled")
    );
    assert!(src.contains("letmutz=zz.offset("), "{}", out.source);
    // Four fallback-extent construction receipts, each with the waiver id.
    use super::mechanical_receipt::{MechanicalStage, MechanicalState};
    let applied = |stage: MechanicalStage, state: MechanicalState| {
        stage == MechanicalStage::Terminal && state == MechanicalState::Applied
    };
    let constructions = out
        .artifacts
        .slice_construction_rows
        .iter()
        .filter(|row| row.extent.is_fallback() && applied(row.terminal.stage, row.terminal.state))
        .count();
    assert_eq!(
        constructions, 4,
        "{:#?}",
        out.artifacts.slice_construction_rows
    );
    // The two calls: the `&mut [f32] → &[f32]` positions (`f`, `f_0`) carry
    // this rule's coercion receipt; the equal-form positions (`d`, `d_0`)
    // complete under wave-5c's same-slice carrier rule.
    let adapters = |adapter: &str| {
        out.artifacts
            .slice_use_rows
            .iter()
            .filter(|row| row.adapter == adapter && applied(row.terminal.stage, row.terminal.state))
            .count()
    };
    assert_eq!(
        adapters("owned-existing-c-interface:zero-syntax"),
        2,
        "{:#?}",
        out.artifacts.slice_use_rows
    );
    assert_eq!(
        adapters("owned-existing-c-same-slice"),
        2,
        "{:#?}",
        out.artifacts.slice_use_rows
    );
    assert_eq!(out.emitted, 6);
    // The delivery-custody instrument (main 033) reads the emitted tree and
    // refuses an inferred declaration; every admitted binding is explicit.
    let declarations =
        super::delivery_custody::inventory_source("lib.rs", &out.source).expect("inventory");
    for local in ["f", "d", "f_0", "d_0"] {
        let row = declarations
            .iter()
            .find(|row| row.owner == "transform_to_distance" && row.binding == local)
            .unwrap_or_else(|| panic!("{local}: {declarations:#?}"));
        assert!(row.type_is_fully_explicit, "{local}: {row:#?}");
        assert_eq!(row.explicit_type.as_deref(), Some("&mut [f32]"), "{row:#?}");
    }
}

/// The second corpus function: the same views beside the per-column payload
/// allocations (`pl1`, `pl2`, Box-family locals that stay raw at this frame)
/// at a seven-argument call. Only `f`/`d` move.
#[test]
#[ignore = "W6A-B1 at the batch-6 head: the Return-stage class-finalizer wall (report 001 STOP 1, wave-5d) — GREEN at 30d69d95; un-ignore when the head carries the finalizer answer"]
fn w6a_b1_heman_transform_to_coordfield_delivers_f_and_d_beside_raw_payloads() {
    let out = emitted("heman-coordfield", HEMAN_COORDFIELD);
    let src = compact(&out.source);
    assert_eq!(out.reverted, 0, "{}", out.source);
    for local in ["f", "d"] {
        assert_eq!(
            reason_of(
                &out.degradations,
                &format!("transform_to_coordfield::{local}")
            ),
            None,
            "{:#?}",
            out.degradations
        );
    }
    assert!(
        src.contains("letmutf:&mut[f32]=core::slice::from_raw_parts_mut(ff.offset((height*x)asisize),crate::FALLBACK_SLICE_EXTENT);"),
        "{}",
        out.source
    );
    assert!(
        src.contains("edt_with_payload(f,d,z,w,height,pl1,pl2);"),
        "{}",
        out.source
    );
    assert!(src.contains("f[(y)asusize]="), "{}", out.source);
    assert!(src.contains("=d[(y_0)asusize];"), "{}", out.source);
    // The payload locals keep their raw text and their C free sites.
    assert!(
        src.contains("*pl1.offset((y*2asi32)asisize)="),
        "{}",
        out.source
    );
    assert!(
        src.contains("free(pl1as*mutcore::ffi::c_void);"),
        "{}",
        out.source
    );
    for local in ["pl1", "pl2", "z", "w"] {
        assert!(
            reason_of(
                &out.degradations,
                &format!("transform_to_coordfield::{local}")
            )
            .is_some(),
            "{local} is not this rule's: {:#?}",
            out.degradations
        );
    }
    assert_eq!(out.emitted, 4);
}

/// Control: an ANNOTATED slice local is not this rule's — it still takes the
/// declaration splice, so the planner branch is exercised only by the
/// unannotated population.
#[test]
#[ignore = "W6A-B1 at the batch-6 head: the Return-stage class-finalizer wall (report 001 STOP 1, wave-5d) — GREEN at 30d69d95; un-ignore when the head carries the finalizer answer"]
fn w6a_b1_annotated_slice_local_keeps_the_declaration_splice() {
    let src = HEMAN_TRANSFORM.replace(
        "let mut f = ff.offset((height * x) as isize);",
        "let mut f: *mut f32 = ff.offset((height * x) as isize);",
    );
    let out = emitted("heman-annotated", &src);
    let text = compact(&out.source);
    assert_eq!(out.reverted, 0, "{}", out.source);
    assert!(
        text.contains("letmutf:&mut[f32]=core::slice::from_raw_parts_mut(ff.offset((height*x)asisize),crate::FALLBACK_SLICE_EXTENT);"),
        "{}",
        out.source
    );
    assert_eq!(
        reason_of(&out.degradations, "transform_to_distance::f"),
        None
    );
}

/// The frame read for shape (a): quadtree `quadtree_node_new` returns a
/// fresh `malloc` (model Raw on its return and local), `test_node::node`
/// receives it (model Ref); at this frame the receiver reports
/// `return-not-adapted` and the callee local `kind-raw`. Pinned so the
/// shape-(a) build starts from a recorded RED.
#[test]
fn w6a_a_quadtree_frame_read_receiver_is_return_not_adapted() {
    let out = emitted("quadtree", QUADTREE_NODE_NEW);
    assert_eq!(out.reverted, 0, "{}", out.source);
    assert_eq!(
        reason_of(&out.degradations, "test_node::node").as_deref(),
        Some("return-not-adapted")
    );
    assert_eq!(
        reason_of(&out.degradations, "quadtree_node_new::node").as_deref(),
        Some("kind-raw")
    );
    assert!(
        compact(&out.source).contains("quadtree_node_isleaf(&*node)"),
        "{}",
        out.source
    );
}

/// **The rule's soundness control.** An unannotated copy of a parameter the
/// model calls `Ref` (`let p = a;` then `p[1]`) stays exactly where the base
/// leaves it — `copy-source-coupled` — because constructing a slice over a
/// binding that becomes a thin reference would widen that reference
/// (R395-2, fix-2). The annotated twin of this shape widens at the base
/// today (`let p: *mut i32 = a;` → `p: &[i32] = from_raw_parts(a, 1024)` with
/// `a: &i32`); that is reported, not repaired, here.
#[test]
fn w6a_b1_copy_of_a_reference_root_is_refused() {
    let src = "#![allow(dead_code, unused_unsafe, unused_variables)]\n\
               pub unsafe fn f(a: *mut i32) -> i32 { let p = a; *p.offset(1) }\n";
    let decisions = super::emit_tests::decisions_of(src);
    let reason = decisions
        .iter()
        .find(|(name, is_param, _)| name == "p" && !is_param)
        .map(|(_, _, reason)| reason.clone());
    assert_eq!(
        reason.as_deref(),
        Some("copy-source-coupled"),
        "{decisions:#?}"
    );
}

/// brotli `ZopfliCostModelSetFromLiteralCosts`, reduced: two unannotated
/// locals rooted in FIELD places of a delivered `&mut` parameter — an inline
/// array decay (`(*self_0).cost_cmd_.as_mut_ptr()`, exact length 704) and a
/// raw pointer field load (`(*self_0).literal_costs_`, fallback extent).
/// Neither widens `self_0`: the constructed slice is over the field's own
/// pointer value, so the reference-root refusal does not apply.
pub(super) const BROTLI_COST_MODEL: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, non_camel_case_types, non_snake_case)]
#[repr(C)]
pub struct ZopfliCostModel {
    pub cost_cmd_: [f32; 704],
    pub literal_costs_: *mut f32,
    pub num_bytes_: usize,
}
unsafe extern "C" fn ZopfliCostModelSetFromLiteralCosts(mut self_0: *mut ZopfliCostModel, mut position: usize) {
    let mut literal_costs = (*self_0).literal_costs_;
    let mut literal_carry = 0.0f64 as f32;
    let mut cost_cmd = ((*self_0).cost_cmd_).as_mut_ptr();
    let mut num_bytes = (*self_0).num_bytes_;
    let mut i: usize = 0;
    *literal_costs.offset(0 as i32 as isize) = 0.0f64 as f32;
    i = 0 as i32 as usize;
    while i < num_bytes {
        literal_carry += *literal_costs.offset(i.wrapping_add(1 as i32 as usize) as isize);
        *literal_costs.offset(i.wrapping_add(1 as i32 as usize) as isize) =
            *literal_costs.offset(i as isize) + literal_carry;
        literal_carry -= *literal_costs.offset(i.wrapping_add(1 as i32 as usize) as isize)
            - *literal_costs.offset(i as isize);
        i = i.wrapping_add(1);
    }
    i = 0 as i32 as usize;
    while i < 704 as i32 as usize {
        *cost_cmd.offset(i as isize) = 0.0f64 as f32;
        i = i.wrapping_add(1);
    }
}
"#;

/// `literal_costs` (a raw pointer value loaded from a field of `self_0`)
/// delivers with the fallback extent: the slice covers that pointer's pointee,
/// never `self_0`'s memory. `cost_cmd` (the inline array field's decay) is
/// REFUSED although its length is exact: `self_0` becomes `&mut ZopfliCostModel`
/// and a `from_raw_parts_mut` over its own field would be a second live safe
/// view the compiler cannot relate to `self_0` — the sound form is a
/// reborrow (`&mut self_0.cost_cmd_[..]`), not this rule's constructor.
#[test]
fn w6a_b1_field_rooted_locals_split_by_what_memory_the_slice_covers() {
    let out = emitted("brotli-cost-model", BROTLI_COST_MODEL);
    let src = compact(&out.source);
    assert_eq!(out.reverted, 0, "{}", out.source);
    assert!(
        src.contains("mutself_0:&mutZopfliCostModel"),
        "{}",
        out.source
    );
    assert!(
        src.contains("letmutliteral_costs:&mut[f32]=core::slice::from_raw_parts_mut((*self_0).literal_costs_,crate::FALLBACK_SLICE_EXTENT);"),
        "{}",
        out.source
    );
    assert!(src.contains("literal_costs[i]"), "{}", out.source);
    assert_eq!(
        reason_of(
            &out.degradations,
            "ZopfliCostModelSetFromLiteralCosts::literal_costs"
        ),
        None,
        "{:#?}",
        out.degradations
    );
    assert!(
        src.contains("letmutcost_cmd=((*self_0).cost_cmd_).as_mut_ptr();"),
        "{}",
        out.source
    );
    assert!(
        src.contains("*cost_cmd.offset(iasisize)="),
        "{}",
        out.source
    );
    assert_eq!(
        reason_of(
            &out.degradations,
            "ZopfliCostModelSetFromLiteralCosts::cost_cmd"
        )
        .as_deref(),
        Some("place-read-pointee"),
        "{:#?}",
        out.degradations
    );
}

/// **Rule W6A-T1, first corpus shape** (`ti_cci` + the smoke test): the
/// struct splits, the allocating callee returns `Box<ti_buffer>`, the freeing
/// callee takes `Box<ti_buffer>` and drops, every receiver is a `Box`, every
/// tail access indexes, the `Copy` / `Clone` impls go, `reverted = 0`.
#[test]
fn w6a_t1_tulip_cci_and_smoke_deliver_the_split_struct() {
    let out = emitted("tulip-cci", super::wave6a_fixture_tulip::TULIP_BUFFER);
    let src = compact(&out.source);
    assert_eq!(out.reverted, 0, "{}", out.source);
    assert_eq!(out.emitted, 4, "{}", out.source);
    assert!(src.contains("pubvals:Box<[f64]>,}"), "{}", out.source);
    assert!(!src.contains("Copyforti_buffer"), "{}", out.source);
    assert!(!src.contains("Cloneforti_buffer"), "{}", out.source);
    assert!(
        src.contains("fnti_buffer_new(mutsize:std::os::raw::c_int)->Box<ti_buffer>{"),
        "{}",
        out.source
    );
    assert!(
        src.contains("letmutret:Box<ti_buffer>=Box::new(crate::ti_buffer{size:0asi32,pushes:0asi32,index:0asi32,sum:0asf64,vals:vec![0asf64;(((size-1asstd::os::raw::c_int))+1)asusize].into_boxed_slice(),});"),
        "{}",
        out.source
    );
    assert!(
        src.contains("fnti_buffer_free(mutbuffer:Box<ti_buffer>){drop(buffer);}"),
        "{}",
        out.source
    );
    assert!(
        src.contains("letmutsum:Box<ti_buffer>=ti_buffer_new(period);"),
        "{}",
        out.source
    );
    assert!(
        src.contains("(*sum).vals[((*sum).index)asusize]=today;"),
        "{}",
        out.source
    );
    assert!(
        src.contains("acc+=fabs(avg-(*sum).vals[(j)asusize]);"),
        "{}",
        out.source
    );
    assert!(src.contains("ti_buffer_free(sum);"), "{}", out.source);
    assert!(
        src.contains("letmutb:Box<ti_buffer>=ti_buffer_new(3asstd::os::raw::c_int);"),
        "{}",
        out.source
    );
    for raw in [
        "malloc(s as",
        "as_mut_ptr().offset(",
        "free(buffer",
        "*mut ti_buffer",
    ] {
        assert!(!src.contains(&compact(raw)), "{raw}: {}", out.source);
    }
    for subject in [
        "ti_buffer_new::ret",
        "ti_buffer_free::buffer",
        "ti_cci::sum",
        "test_buffer::b",
    ] {
        assert_eq!(
            reason_of(&out.degradations, subject),
            None,
            "{subject}: {:#?}",
            out.degradations
        );
    }
    let receipts = out.artifacts.flexible_tail_receipts.clone();
    assert!(receipts.contains("crate::ti_buffer\tadmitted\tflexible-tail-split struct=crate::ti_buffer tail=vals element=f64 declared_len=1 allocations=1 receivers=2 owning_returns=1 owning_params=1 tail_edits=6 impls_removed=2"), "{receipts}");
    let declarations =
        super::delivery_custody::inventory_source("lib.rs", &out.source).expect("inventory");
    for (owner, binding) in [
        ("ti_cci", "sum"),
        ("test_buffer", "b"),
        ("ti_buffer_new", "ret"),
    ] {
        let row = declarations
            .iter()
            .find(|row| row.owner == owner && row.binding == binding)
            .unwrap_or_else(|| panic!("{owner}::{binding}: {declarations:#?}"));
        assert!(row.type_is_fully_explicit, "{row:#?}");
        assert_eq!(
            row.explicit_type.as_deref(),
            Some("Box<ti_buffer>"),
            "{row:#?}"
        );
    }
}

/// **Second corpus shape** (`ti_stoch`): two buffers in one owner, the second
/// fed from the first, both transferred to the freeing callee at the end.
#[test]
fn w6a_t1_tulip_stoch_two_buffers_in_one_owner() {
    let src_text = format!(
        "{}{}",
        super::wave6a_fixture_tulip::TULIP_HEADER,
        super::wave6a_fixture_tulip::TULIP_STOCH_BODY
    );
    let out = emitted("tulip-stoch", &src_text);
    let src = compact(&out.source);
    assert_eq!(out.reverted, 0, "{}", out.source);
    assert!(
        src.contains("letmutk_sum:Box<ti_buffer>=ti_buffer_new(kslow);"),
        "{}",
        out.source
    );
    assert!(
        src.contains("letmutd_sum:Box<ti_buffer>=ti_buffer_new(dperiod);"),
        "{}",
        out.source
    );
    assert!(
        src.contains("(*d_sum).vals[((*d_sum).index)asusize]=k;"),
        "{}",
        out.source
    );
    assert!(
        src.contains("ti_buffer_free(k_sum);ti_buffer_free(d_sum);"),
        "{}",
        out.source
    );
    assert!(src.contains("pubvals:Box<[f64]>,}"), "{}", out.source);
    for subject in [
        "ti_buffer_new::ret",
        "ti_buffer_free::buffer",
        "ti_stoch::k_sum",
        "ti_stoch::d_sum",
    ] {
        assert_eq!(
            reason_of(&out.degradations, subject),
            None,
            "{subject}: {:#?}",
            out.degradations
        );
    }
    assert_eq!(out.emitted, 4, "{}", out.source);
}

/// Control: a foreign consumer takes the struct by pointer — the layout may
/// not change; the transaction holds typed and every row keeps
/// `box-flexible-tail-held`.
#[test]
fn w6a_t1_struct_crossing_a_foreign_boundary_is_held() {
    let src_text = format!(
        "{}{}",
        super::wave6a_fixture_tulip::TULIP_HEADER,
        super::wave6a_fixture_tulip::TULIP_CROSSING_BODY
    );
    let out = emitted("tulip-crossing", &src_text);
    let src = compact(&out.source);
    assert!(
        src.contains("pubvals:[std::os::raw::c_double;1],"),
        "{}",
        out.source
    );
    assert!(!src.contains("Box<ti_buffer>"), "{}", out.source);
    assert_eq!(
        reason_of(&out.degradations, "crossing::b").as_deref(),
        Some("box-flexible-tail-held"),
        "{:#?}",
        out.degradations
    );
    assert_eq!(
        reason_of(&out.degradations, "ti_buffer_new::ret").as_deref(),
        Some("box-flexible-tail-held")
    );
    assert!(
        out.artifacts
            .flexible_tail_receipts
            .contains("ti_buffer\theld\tflexible-tail-crosses-boundary:extern:ti_buffer_dump"),
        "{}",
        out.artifacts.flexible_tail_receipts
    );
}

/// Control: a caller reads the buffer after handing it to the freeing callee,
/// so the callee's parameter is not an owning transfer at every caller — the
/// transaction holds typed (`param-caller-retains`) and nothing moves.
#[test]
fn w6a_t1_caller_using_the_buffer_after_transfer_is_held() {
    let src_text = format!(
        "{}{}",
        super::wave6a_fixture_tulip::TULIP_HEADER,
        super::wave6a_fixture_tulip::TULIP_RETAINED_BODY
    );
    let out = emitted("tulip-retained", &src_text);
    let src = compact(&out.source);
    assert!(!src.contains("Box<ti_buffer>"), "{}", out.source);
    assert_eq!(
        reason_of(&out.degradations, "retained::b").as_deref(),
        Some("box-flexible-tail-held"),
        "{:#?}",
        out.degradations
    );
    assert!(
        out.artifacts.flexible_tail_receipts.contains(
            "ti_buffer\theld\tflexible-tail-param-caller-retains:retained:used-after-transfer"
        ),
        "{}",
        out.artifacts.flexible_tail_receipts
    );
}
