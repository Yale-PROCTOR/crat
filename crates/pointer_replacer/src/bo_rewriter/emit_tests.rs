//! **S2b.0a witnesses — multi-file emission.**
//!
//! These exist because M1's ten goldens are all single-source: the string entry
//! point was fully exercised by its own suite and simultaneously unexercised
//! against the shape it will be run on. 10 of the 20 frozen-corpus programs
//! carry subjects across 2–110 files, so "which file does this edit belong to"
//! is not a question the goldens could ever have asked.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::PathBuf,
    sync::atomic::{AtomicUsize, Ordering},
};

use super::{Emission, decide_table, emit_files, plan::FileKey, verify};

static NEXT_FIXTURE: AtomicUsize = AtomicUsize::new(0);

/// AST-only golden helper after atomic class finalization. It intentionally
/// lives in this test module so the one-production-emission-path ratchet keeps
/// counting only shipping call sites.
pub(super) fn ast_emitted_source_of(input: &str) -> Result<String, String> {
    match ::utils::compilation::run_compiler_on_input(
        ::utils::compilation::str_to_input(input),
        |tcx| {
            let capture = super::ast_transform::capture_ast(tcx)?;
            let (table, ctx) = super::decide_table_with_ctx(tcx)?;
            let emission = emit_files(
                tcx,
                &table,
                &rustc_hash::FxHashSet::default(),
                &ctx.retained_c9_plans,
            )?;
            let held = emission.plan.held_classes();
            let reverts = super::ast_transform::revert_set_from_classes_and_atoms(
                &held,
                &std::collections::BTreeSet::new(),
                &table,
            )?;
            let (files, _, _) = super::ast_transform::ast_emitted_files_from(
                tcx,
                &capture,
                &reverts,
                emission.plan.root_file.as_ref(),
                &table,
            )?;
            files
                .into_values()
                .next()
                .ok_or_else(|| "AST golden emitted no source file".to_owned())
        },
    ) {
        Ok(inner) => inner,
        Err(why) => Err(format!("{why:?}")),
    }
}

/// A throwaway multi-file crate on disk. Removed on drop.
struct Fixture(PathBuf);

impl Fixture {
    fn new(files: &[(&str, &str)]) -> Self {
        let sequence = NEXT_FIXTURE.fetch_add(1, Ordering::Relaxed);
        let dir = std::env::temp_dir().join(format!(
            "crat-emit-fixture-{}-{sequence}",
            std::process::id()
        ));
        fs::create_dir_all(&dir).expect("create emission fixture directory");
        for (name, text) in files {
            let path = dir.join(name);
            if let Some(parent) = path.parent() {
                fs::create_dir_all(parent).expect("create fixture subdirectory");
            }
            fs::write(path, text).expect("write emission fixture file");
        }
        Self(dir)
    }

    fn root(&self) -> PathBuf {
        self.0.join("lib.rs")
    }

    /// Every file in the fixture tree, by relative path, with its bytes.
    /// Compared in-process rather than shelling out — a byte comparison here is
    /// the evidence, not a tool's summary of one.
    fn snapshot(&self) -> BTreeMap<PathBuf, Vec<u8>> {
        fn walk(
            dir: &std::path::Path,
            base: &std::path::Path,
            out: &mut BTreeMap<PathBuf, Vec<u8>>,
        ) {
            for entry in fs::read_dir(dir).expect("fixture tree readable") {
                let entry = entry.expect("fixture entry");
                let path = entry.path();
                if entry.file_type().expect("file type").is_dir() {
                    walk(&path, base, out);
                } else {
                    let key = path.strip_prefix(base).expect("under base").to_path_buf();
                    out.insert(key, fs::read(&path).expect("fixture file readable"));
                }
            }
        }
        let mut out = BTreeMap::new();
        walk(&self.0, &self.0, &mut out);
        out
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn emit(fixture: &Fixture) -> Emission {
    emit_injected(fixture, &|_| {})
}

/// **BRANCH 2 — an INJECTION at the plan boundary**, the `plan/mod.rs` arm-3
/// precedent and the same seam `rewrite_m1_path_injected` already uses.
///
/// Since S3.6-1 step 2 the decision phase refuses every emission that would
/// launder a reference into a raw context — which is the gate's whole job, and
/// which makes a deliberately-broken emission **unconstructible from source**.
/// Measured, not assumed: every raw context a converted value can reach is
/// either gated (field store, return, foreign argument, `static mut`) or is
/// itself a subject and converts with its source (an annotated local).
///
/// So the broken emission is injected as DATA rather than coaxed out of a
/// fixture. The fixture text is unchanged; only the decision differs, which is
/// what keeps every property the original witnesses rested on — line numbers,
/// file names, error counts — true by construction rather than by re-derivation.
fn emit_injected(
    fixture: &Fixture,
    inject: &(dyn Fn(&mut super::decision::DecisionTable) + Sync),
) -> Emission {
    ::utils::compilation::run_compiler_on_path(&fixture.0.join("lib.rs"), |tcx| {
        let mut table = decide_table(tcx).expect("fixture yields a decision table");
        inject(&mut table);
        emit_files(tcx, &table, &rustc_hash::FxHashSet::default(), &[]).expect("emission succeeds")
    })
    .expect("fixture compiles")
}

/// Force `stash`'s parameter to a SHARED reference.
///
/// Shared is load-bearing: `&mut T → *mut T` coerces silently, so a mutable
/// injection would emit a crate that COMPILES and witness nothing. `&T` into a
/// `*mut T` field is `E0308` — the loud failure the verify layer exists to
/// read, and the one the original fixture produced before step 2 refused it.
fn force_stash_value_shared(table: &mut super::decision::DecisionTable) {
    for (subject, decision) in &mut table.entries {
        if subject.param_name.as_deref() == Some("value") {
            *decision = super::decision::Decision::Ref { mutable: false };
        }
    }
}

/// Emitted text for a file, matched on the file's *name* so the assertion does
/// not depend on how the compiler canonicalized the fixture's path.
fn text_for<'a>(emission: &'a Emission, name: &str) -> Option<&'a String> {
    emission.files.iter().find_map(|(key, text)| match key {
        FileKey::Real(path) if path.file_name()?.to_str()? == name => Some(text),
        _ => None,
    })
}

const BOX_W1_PREAMBLE: &str = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
extern \"C\" {\n\
    fn malloc(size: usize) -> *mut core::ffi::c_void;\n\
    fn calloc(count: usize, size: usize) -> *mut core::ffi::c_void;\n\
    fn memset(ptr: *mut core::ffi::c_void, value: i32, bytes: usize) -> *mut core::ffi::c_void;\n\
    fn realloc(ptr: *mut core::ffi::c_void, size: usize) -> *mut core::ffi::c_void;\n\
    fn free(ptr: *mut core::ffi::c_void);\n\
}\n";

#[test]
fn box_w1_malloc_literal_first_store_emits_box_and_free_site_drop() {
    let src = format!(
        "{BOX_W1_PREAMBLE}\n\
         pub unsafe fn f() -> i32 {{\n\
             let mut p: *mut i32 = malloc(core::mem::size_of::<i32>()) as *mut i32;\n\
             *p = 7;\n\
             let out = *p;\n\
             free(p as *mut core::ffi::c_void);\n\
             out\n\
         }}\n"
    );
    let super::RewriteOutcome::Emitted {
        source,
        degradations,
        ..
    } = super::rewrite_m1(&src)
    else {
        panic!("BOX-W1 fixture must emit");
    };
    assert!(
        source.contains("p: Box<i32>"),
        "degradations={degradations:#?}\n{source}"
    );
    assert!(source.contains("Box::new(7)"), "{source}");
    assert!(
        !source.contains("*p = 7"),
        "redundant store survived: {source}"
    );
    assert!(
        source.contains("drop(p)"),
        "C free site did not become drop: {source}"
    );
    assert!(
        !source.contains("free(p as"),
        "raw free call survived: {source}"
    );
}

/// BOX2-W1 — C2Rust lowers an unannotated allocator binding through a
/// call-destination temporary and a pointer cast before assigning the source
/// binding. The Box construction bridge must follow that one exact transparent
/// chain; the initializer supplies the inferred Box type, so no declaration
/// type splice is required.
#[test]
fn box2_w1_unannotated_calloc_cast_chain_reaches_the_subject() {
    let src = format!(
        "{BOX_W1_PREAMBLE}\n\
         pub unsafe fn f(size: usize) {{\n\
             let mut ff = calloc(size, core::mem::size_of::<f32>()) as *mut f32;\n\
             free(ff as *mut core::ffi::c_void);\n\
         }}\n"
    );
    let super::RewriteOutcome::Emitted {
        source,
        degradations,
        ..
    } = super::rewrite_m1(&src)
    else {
        panic!("BOX2-W1 fixture must emit");
    };
    assert!(
        source.contains("let mut ff = vec![0 as f32; size].into_boxed_slice()"),
        "degradations={degradations:#?}\n{source}"
    );
    assert!(source.contains("drop(ff)"), "{source}");
    assert!(!source.contains("calloc(size"), "{source}");
}

#[test]
fn box2_w1_bridge_receipt_names_the_exact_temp_chain() {
    let src = format!(
        "{BOX_W1_PREAMBLE}\n\
         pub unsafe fn f(size: usize) {{\n\
             let mut ff = calloc(size, core::mem::size_of::<f32>()) as *mut f32;\n\
             free(ff as *mut core::ffi::c_void);\n\
         }}\n"
    );
    let bridges = ::utils::compilation::run_compiler_on_str(&src, |tcx| {
        super::box_plan_artifact(tcx)
            .expect("Box plan artifact")
            .bridges
    })
    .expect("fixture compiles");
    let rows = bridges.lines().skip(1).collect::<Vec<_>>();
    assert_eq!(rows.len(), 1, "{bridges}");
    let fields = rows[0].split('\t').collect::<Vec<_>>();
    assert_eq!(fields[9], "resolved", "{bridges}");
    assert_eq!(fields[10], "-", "{bridges}");
    assert!(fields[11].contains("call-destination"), "{bridges}");
    assert!(fields[11].contains("assignment-rhs"), "{bridges}");
    assert!(fields[11].contains("assignment-lhs"), "{bridges}");
}

#[test]
fn box2_w1b_projected_pointee_stores_do_not_redefine_the_pointer_binding() {
    let src = format!(
        "{BOX_W1_PREAMBLE}\n\
         #[repr(C)] struct Image {{ width: i32, height: i32 }}\n\
         pub unsafe fn f() {{\n\
             let mut img = malloc(core::mem::size_of::<Image>()) as *mut Image;\n\
             (*img).width = 1;\n\
             (*img).height = 2;\n\
             free(img as *mut core::ffi::c_void);\n\
         }}\n"
    );
    let bridges = ::utils::compilation::run_compiler_on_str(&src, |tcx| {
        super::box_plan_artifact(tcx)
            .expect("Box plan artifact")
            .bridges
    })
    .expect("fixture compiles");
    let row = bridges.lines().nth(1).expect("one bridge row");
    let fields = row.split('\t').collect::<Vec<_>>();
    assert_eq!(fields[9], "resolved", "{bridges}");
    assert_eq!(fields[10], "-", "{bridges}");
}

/// BOX2-W2 — when no first-store or memset evidence exists, an exact
/// `count * size_of::<T>()` allocation admits the numeric default-fill slice
/// arm and preserves the evidence-backed count.
#[test]
fn box2_w2_malloc_slice_uses_numeric_default_fill() {
    let src = format!(
        "{BOX_W1_PREAMBLE}\n\
         pub unsafe fn f(n: usize) {{\n\
             let p: *mut f64 = malloc(n * core::mem::size_of::<f64>()) as *mut f64;\n\
             free(p as *mut core::ffi::c_void);\n\
         }}\n"
    );
    let super::RewriteOutcome::Emitted {
        source,
        degradations,
        ..
    } = super::rewrite_m1(&src)
    else {
        panic!("BOX2-W2 fixture must emit");
    };
    assert!(
        source.contains("p: Box<[f64]> = vec![0 as f64; n].into_boxed_slice()"),
        "degradations={degradations:#?}\n{source}"
    );
    assert!(source.contains("drop(p)"), "{source}");
}

/// BOX2-W3 — the sized twin uses the same admitted numeric vocabulary but
/// must not manufacture a slice or an extent.
#[test]
fn box2_w3_malloc_sized_uses_numeric_default_fill() {
    let src = format!(
        "{BOX_W1_PREAMBLE}\n\
         pub unsafe fn f() {{\n\
             let p: *mut i32 = malloc(core::mem::size_of::<i32>()) as *mut i32;\n\
             free(p as *mut core::ffi::c_void);\n\
         }}\n"
    );
    let super::RewriteOutcome::Emitted {
        source,
        degradations,
        ..
    } = super::rewrite_m1(&src)
    else {
        panic!("BOX2-W3 fixture must emit");
    };
    assert!(
        source.contains("p: Box<i32> = Box::new(0 as i32)"),
        "degradations={degradations:#?}\n{source}"
    );
    assert!(!source.contains("Box<[i32]>"), "{source}");
    assert!(source.contains("drop(p)"), "{source}");
}

/// BOX2-N3/R1 — a fixed header plus a separately-sized trailing allocation is
/// a representation question, not an initializer failure. Wave 2 must retain
/// the exact positive layout evidence in its dedicated hold.
#[test]
fn box2_n3_flexible_tail_is_a_typed_hold_with_layout_evidence() {
    let src = format!(
        "{BOX_W1_PREAMBLE}\n\
         #[repr(C)] struct Tail {{ len: i32, values: [f64; 1] }}\n\
         pub unsafe fn f(n: usize) {{\n\
             let bytes = core::mem::size_of::<Tail>() + (n - 1) * core::mem::size_of::<f64>();\n\
             let p: *mut Tail = malloc(bytes) as *mut Tail;\n\
             free(p as *mut core::ffi::c_void);\n\
         }}\n"
    );
    let super::RewriteOutcome::Emitted {
        source,
        degradations,
        ..
    } = super::rewrite_m1(&src)
    else {
        panic!("BOX2-N3 fixture must complete conservatively");
    };
    let row = degradations
        .iter()
        .find(|row| row.subject == "f::p")
        .expect("flexible-tail subject has a typed row");
    assert_eq!(row.reason.key(), "box-flexible-tail-held");
    let detail = row.reason.detail();
    assert!(detail.contains("root_site="), "{detail}");
    assert!(detail.contains("size_of::<Tail>"), "{detail}");
    assert!(!source.contains("Box<"), "{source}");
    let evidence = ::utils::compilation::run_compiler_on_str(&src, |tcx| {
        super::box_plan_artifact(tcx)
            .expect("Box plan artifact")
            .default_fill_candidates
    })
    .expect("fixture compiles");
    let row = evidence
        .lines()
        .nth(1)
        .expect("one flexible-tail evidence row");
    let fields = row.split('\t').collect::<Vec<_>>();
    assert_eq!(fields[3], "held", "{evidence}");
    assert_eq!(fields[4], "box-flexible-tail-held", "{evidence}");
}

#[test]
fn box2_n3_nonadmitted_struct_default_fill_stays_closed() {
    let src = format!(
        "{BOX_W1_PREAMBLE}\n\
         #[repr(C)] struct Pair {{ x: i32, y: i32 }}\n\
         pub unsafe fn f() {{\n\
             let p: *mut Pair = malloc(core::mem::size_of::<Pair>()) as *mut Pair;\n\
             free(p as *mut core::ffi::c_void);\n\
         }}\n"
    );
    let super::RewriteOutcome::Emitted {
        source,
        degradations,
        ..
    } = super::rewrite_m1(&src)
    else {
        panic!("BOX2-N3 non-admitted fixture must complete conservatively");
    };
    assert!(
        degradations
            .iter()
            .any(|row| row.subject == "f::p" && row.reason.key() == "box-initializer-unsupported"),
        "{degradations:#?}"
    );
    assert!(!source.contains("Box<Pair>"), "{source}");
}

/// BOX2-N4/B5 — a body-local owner returned through the unchanged raw
/// signature is outside the locals-only wave. Default-fill may classify its
/// construction, but the return boundary must win before any Box is emitted.
#[test]
fn box2_n4_returned_default_fill_candidate_stays_boundary_held() {
    let src = format!(
        "{BOX_W1_PREAMBLE}\n\
         pub unsafe fn f(items: usize, size: usize) -> *mut core::ffi::c_void {{\n\
             let v: *mut core::ffi::c_void = malloc(items * size);\n\
             v\n\
         }}\n"
    );
    let super::RewriteOutcome::Emitted {
        source,
        degradations,
        ..
    } = super::rewrite_m1(&src)
    else {
        panic!("BOX2-N4 fixture must complete conservatively");
    };
    assert!(
        degradations
            .iter()
            .any(|row| { row.subject == "f::v" && row.reason.key() == "box-param-caller-unknown" }),
        "{degradations:#?}"
    );
    assert!(source.contains("v: *mut core::ffi::c_void"), "{source}");
    assert!(!source.contains("Box<["), "{source}");
}

#[test]
fn box2_w5_void_byte_extent_emits_u8_box_when_no_boundary_blocks() {
    let src = format!(
        "{BOX_W1_PREAMBLE}\n\
         pub unsafe fn f(items: usize, size: usize) {{\n\
             let v: *mut core::ffi::c_void = malloc(items * size);\n\
             free(v);\n\
         }}\n"
    );
    let super::RewriteOutcome::Emitted {
        source,
        degradations,
        ..
    } = super::rewrite_m1(&src)
    else {
        panic!("BOX2-W5 fixture must emit");
    };
    assert!(
        source.contains("v: Box<[u8]> = vec![0 as u8; (items * size) as usize]"),
        "degradations={degradations:#?}\n{source}"
    );
    assert!(source.contains("drop(v)"), "{source}");
    let evidence = ::utils::compilation::run_compiler_on_str(&src, |tcx| {
        super::box_plan_artifact(tcx)
            .expect("Box plan artifact")
            .default_fill_candidates
    })
    .expect("fixture compiles");
    let row = evidence
        .lines()
        .nth(1)
        .expect("one default-fill evidence row");
    let fields = row.split('\t').collect::<Vec<_>>();
    assert_eq!(fields[3], "candidate", "{evidence}");
    assert_eq!(fields[4], "default-fill-slice-u8", "{evidence}");
    assert_eq!(fields[5], "u8", "{evidence}");
}

#[test]
fn box_n5_depth_two_local_stays_out_of_wave1() {
    let src = format!(
        "{BOX_W1_PREAMBLE}\n\
         pub unsafe fn f() {{\n\
             let p: *mut *mut i32 = malloc(core::mem::size_of::<*mut i32>()) as *mut *mut i32;\n\
             free(p as *mut core::ffi::c_void);\n\
         }}\n"
    );
    let super::RewriteOutcome::Emitted { source, .. } = super::rewrite_m1(&src) else {
        panic!("BOX-N5 fixture must complete without a Box decision");
    };
    assert!(
        source.contains("p: *mut *mut i32"),
        "depth-2 local moved: {source}"
    );
    assert!(
        !source.contains("Box<"),
        "depth-2 local entered Box wave: {source}"
    );
}

#[test]
fn box_w2_calloc_uses_licensed_slice_extent() {
    let src = format!(
        "{BOX_W1_PREAMBLE}\n\
         pub unsafe fn f(n: usize) {{\n\
             let p: *mut i32 = calloc(n, core::mem::size_of::<i32>()) as *mut i32;\n\
             free(p as *mut core::ffi::c_void);\n\
         }}\n"
    );
    let super::RewriteOutcome::Emitted { source, .. } = super::rewrite_m1(&src) else {
        panic!("BOX-W2 fixture must emit");
    };
    assert!(source.contains("p: Box<[i32]>"), "{source}");
    assert!(
        source.contains("vec![0 as i32; n].into_boxed_slice()"),
        "licensed count was not consumed: {source}"
    );
    assert!(source.contains("drop(p)"), "{source}");
    assert!(
        !source.contains("FALLBACK_SLICE_EXTENT"),
        "licensed site fabricated: {source}"
    );
}

#[test]
fn box_w3_memset_slice_uses_named_fallback_and_deletes_statement() {
    let src = format!(
        "{BOX_W1_PREAMBLE}\n\
         pub unsafe fn f(n: usize) {{\n\
             let mut p: *mut i32 = malloc(n * core::mem::size_of::<i32>()) as *mut i32;\n\
             p = memset(p as *mut core::ffi::c_void, 0, n * core::mem::size_of::<i32>()) as *mut i32;\n\
             free(p as *mut core::ffi::c_void);\n\
         }}\n"
    );
    let super::RewriteOutcome::Emitted {
        source,
        degradations,
        ..
    } = super::rewrite_m1(&src)
    else {
        panic!("BOX-W3 fixture must emit");
    };
    assert!(
        source.contains("p: Box<[i32]>"),
        "degradations={degradations:#?}\n{source}"
    );
    assert!(
        source.contains("crate::FALLBACK_SLICE_EXTENT"),
        "fallback arm missing: {source}"
    );
    assert_eq!(
        source.matches("const FALLBACK_SLICE_EXTENT").count(),
        1,
        "{source}"
    );
    assert!(
        !source.contains("= memset("),
        "zeroing assignment survived: {source}"
    );
    assert!(source.contains("drop(p)"), "{source}");
    let raw = ::utils::compilation::run_compiler_on_str(&src, |tcx| {
        super::raw_boundary_trace_artifacts(tcx).expect("Box W3 raw-boundary receipts")
    })
    .expect("Box W3 receipt fixture compiles");
    let owned = raw
        .dispositions
        .lines()
        .skip(1)
        .map(|line| line.split('\t').collect::<Vec<_>>())
        .filter(|fields| fields.get(10) == Some(&"owned-by-box"))
        .collect::<Vec<_>>();
    assert_eq!(owned.len(), 2, "{}", raw.dispositions);
    assert!(
        owned.iter().any(|fields| {
            fields.get(3) == Some(&"memset")
                && fields.get(9) == Some(&"box")
                && fields.get(14) == Some(&"box-initializer-consumed")
        }),
        "memset was not typed as Box-owned: {}",
        raw.dispositions
    );
    assert!(
        owned.iter().any(|fields| {
            fields.get(3) == Some(&"free")
                && fields.get(9) == Some(&"box")
                && fields.get(14) == Some(&"box-lifecycle-owned")
        }),
        "free was not typed as Box-owned: {}",
        raw.dispositions
    );
}

#[test]
fn task90_c2_box_w3_site_ownership_trace_dump() {
    let src = format!(
        "{BOX_W1_PREAMBLE}\n\
         pub unsafe fn f(n: usize) {{\n\
             let mut p: *mut i32 = malloc(n * core::mem::size_of::<i32>()) as *mut i32;\n\
             p = memset(p as *mut core::ffi::c_void, 0, n * core::mem::size_of::<i32>()) as *mut i32;\n\
             free(p as *mut core::ffi::c_void);\n\
         }}\n"
    );
    let (raw, box_plan) = ::utils::compilation::run_compiler_on_str(&src, |tcx| {
        (
            super::raw_boundary_trace_artifacts(tcx).expect("raw trace"),
            super::box_plan_artifact(tcx).expect("Box plan"),
        )
    })
    .expect("Box trace fixture compiles");
    eprintln!("BOX-W3 RAW SUBJECTS\n{}", raw.subjects);
    eprintln!("BOX-W3 RAW SITES\n{}", raw.sites);
    eprintln!("BOX-W3 RAW DISPOSITIONS\n{}", raw.dispositions);
    eprintln!("BOX-W3 BOX PLAN\n{}", box_plan.tsv);
}

#[test]
fn box_w4_exact_copy_chain_threads_one_owner_to_the_free_site() {
    let src = format!(
        "{BOX_W1_PREAMBLE}\n\
         pub unsafe fn f() -> i32 {{\n\
             let mut p: *mut i32 = malloc(core::mem::size_of::<i32>()) as *mut i32;\n\
             *p = 9;\n\
             let q: *mut i32 = p;\n\
             let out = *q;\n\
             free(q as *mut core::ffi::c_void);\n\
             out\n\
         }}\n"
    );
    let outcome = super::rewrite_m1(&src);
    let super::RewriteOutcome::Emitted {
        source,
        degradations,
        ..
    } = outcome
    else {
        let super::RewriteOutcome::Degraded {
            reason,
            degradations,
            unplaceable,
            ..
        } = outcome
        else {
            unreachable!()
        };
        panic!(
            "BOX-W4 fixture must emit: reason={reason} degradations={degradations:#?} \
             unplaceable={unplaceable:#?}"
        );
    };
    assert!(
        source.contains("p: Box<i32>"),
        "degradations={degradations:#?}\nsource binding did not convert: {source}"
    );
    assert!(
        source.contains("q: Box<i32> = p"),
        "move binding did not convert: {source}"
    );
    assert!(
        source.contains("drop(q)"),
        "free responsibility did not follow q: {source}"
    );
    assert_eq!(source.matches("Box::new(9)").count(), 1, "{source}");
}

#[test]
fn box_n2_sibling_copy_split_does_not_create_two_boxes() {
    let src = format!(
        "{BOX_W1_PREAMBLE}\n\
         pub unsafe fn f() -> i32 {{\n\
             let mut p: *mut i32 = malloc(core::mem::size_of::<i32>()) as *mut i32;\n\
             *p = 9;\n\
             let q: *mut i32 = p;\n\
             let r: *mut i32 = p;\n\
             *q + *r\n\
         }}\n"
    );
    let super::RewriteOutcome::Emitted { source, .. } = super::rewrite_m1(&src) else {
        panic!("BOX-N2 fixture must complete conservatively");
    };
    assert!(
        !source.contains("Box<"),
        "sibling split over-licensed Box: {source}"
    );
}

#[test]
fn box_w6_mutually_exclusive_free_sites_both_become_drops() {
    let src = format!(
        "{BOX_W1_PREAMBLE}\n\
         pub unsafe fn f(flag: bool) {{\n\
             let mut p: *mut i32 = malloc(core::mem::size_of::<i32>()) as *mut i32;\n\
             *p = 3;\n\
             if flag {{\n\
                 free(p as *mut core::ffi::c_void);\n\
             }} else {{\n\
                 free(p as *mut core::ffi::c_void);\n\
             }}\n\
         }}\n"
    );
    let super::RewriteOutcome::Emitted {
        source,
        degradations,
        ..
    } = super::rewrite_m1(&src)
    else {
        panic!("BOX-W6 fixture must emit");
    };
    assert!(
        source.contains("p: Box<i32>"),
        "degradations={degradations:#?}\n{source}"
    );
    assert_eq!(source.matches("drop(p)").count(), 2, "{source}");
    assert!(!source.contains("free(p as"), "{source}");
}

#[test]
fn box_n1_scope_exit_uses_implicit_close_waiver() {
    use super::decision::box_facts::ImplicitCloseKind;

    assert_eq!(
        ImplicitCloseKind::Overwrite.receipt(),
        "waiver-drop(overwrite)"
    );
    assert_eq!(
        ImplicitCloseKind::ScopeExit.receipt(),
        "waiver-drop(scope-exit)"
    );
    assert_eq!(ImplicitCloseKind::Unwind.receipt(), "waiver-drop(unwind)");
}

#[test]
fn box_w7_overwrite_uses_plain_assignment_and_auto_drop() {
    let src = format!(
        "{BOX_W1_PREAMBLE}\n\
         pub unsafe fn f() -> i32 {{\n\
             let mut p: *mut i32 = malloc(core::mem::size_of::<i32>()) as *mut i32;\n\
             *p = 1;\n\
             p = malloc(core::mem::size_of::<i32>()) as *mut i32;\n\
             *p = 2;\n\
             let out = *p;\n\
             free(p as *mut core::ffi::c_void);\n\
             out\n\
         }}\n"
    );
    let super::RewriteOutcome::Emitted {
        source,
        degradations,
        ..
    } = super::rewrite_m1(&src)
    else {
        panic!("BOX-W7 fixture must emit");
    };
    assert!(
        source.contains("p: Box<i32> = Box::new(1)"),
        "degradations={degradations:#?}\n{source}"
    );
    assert!(
        source.contains("p = Box::new(2)"),
        "plain overwrite missing: {source}"
    );
    assert!(
        !source.contains("forget"),
        "omission-preserving form survived: {source}"
    );
    assert_eq!(source.matches("drop(p)").count(), 1, "{source}");
}

#[test]
fn box_w8_nullable_owner_uses_none_some_and_take() {
    let src = format!(
        "{BOX_W1_PREAMBLE}\n\
         pub unsafe fn f() {{\n\
             let mut p: *mut i32 = 0 as *mut i32;\n\
             p = malloc(core::mem::size_of::<i32>()) as *mut i32;\n\
             *p = 7;\n\
             free(p as *mut core::ffi::c_void);\n\
         }}\n"
    );
    let super::RewriteOutcome::Emitted {
        source,
        degradations,
        ..
    } = super::rewrite_m1(&src)
    else {
        panic!("BOX-W8 fixture must emit");
    };
    assert!(
        source.contains("p: Option<Box<i32>> = None"),
        "degradations={degradations:#?}\n{source}"
    );
    assert!(source.contains("p = Some(Box::new(7))"), "{source}");
    assert!(source.contains("drop(p.take())"), "{source}");
    assert!(
        !source.contains("unwrap"),
        "nullable Box used unchecked unwrap: {source}"
    );
}

#[test]
fn box_w5_realloc_is_one_atomic_consume_and_replacement() {
    let src = format!(
        "{BOX_W1_PREAMBLE}\n\
         pub unsafe fn f(n: usize, m: usize) {{\n\
             let mut p: *mut i32 = calloc(n, core::mem::size_of::<i32>()) as *mut i32;\n\
             p = realloc(p as *mut core::ffi::c_void, m * core::mem::size_of::<i32>()) as *mut i32;\n\
             free(p as *mut core::ffi::c_void);\n\
         }}\n"
    );
    let super::RewriteOutcome::Emitted {
        source,
        degradations,
        ..
    } = super::rewrite_m1(&src)
    else {
        panic!("BOX-W5 fixture must emit");
    };
    assert!(
        source.contains("p: Box<[i32]>"),
        "degradations={degradations:#?}\n{source}"
    );
    assert!(
        source.contains("Vec::from(p)"),
        "old Box was not consumed: {source}"
    );
    assert!(
        source.contains(".resize("),
        "replacement extent was not applied: {source}"
    );
    assert!(source.contains("into_boxed_slice()"), "{source}");
    assert_eq!(source.matches("drop(p)").count(), 1, "{source}");
    assert!(
        !source.contains("realloc(p as"),
        "raw realloc survived: {source}"
    );
}

#[test]
fn box_d4_emitted_mir_drop_observer_distinguishes_close_sites() {
    let source = "#![allow(dead_code, unused_assignments)]\n\
                  pub fn explicit() { let p: Box<i32> = Box::new(1); drop(p); }\n\
                  pub fn scope() { let p: Box<i32> = Box::new(1); let _ = *p; }\n\
                  pub fn overwrite() { let mut p: Box<i32> = Box::new(1); p = Box::new(2); let _ = *p; }\n";
    let drops = super::verify::box_mir_drops_str(source).expect("observe emitted MIR drops");

    assert!(
        drops.iter().all(|drop| drop.function != "explicit"),
        "an explicit drop call must consume the Box without an implicit MIR Drop: {drops:#?}"
    );
    assert!(
        drops.iter().any(|drop| drop.function == "scope"),
        "scope-close MIR Drop was not observed: {drops:#?}"
    );
    assert!(
        drops.iter().any(|drop| drop.function == "overwrite"),
        "overwrite/unwind MIR Drop was not observed: {drops:#?}"
    );
}

#[test]
fn box_d4_unreceipted_implicit_drop_is_rejected() {
    let source =
        "#![allow(dead_code)]\npub fn f() { let p: Box<i32> = Box::new(1); let _ = *p; }\n";
    let drops = super::verify::box_mir_drops_str(source).expect("observe emitted MIR drops");
    assert!(!drops.is_empty(), "fixture must contain an implicit Drop");
    let error = super::verify::reconcile_box_mir_drops(&drops, &[])
        .expect_err("an implicit Drop without a waiver receipt must fail");
    assert!(error.contains("unreceipted"), "wrong failure: {error}");
}

#[test]
fn box_d4_overwrite_scope_and_unwind_drops_receive_distinct_receipts() {
    let source = "#![allow(dead_code, unused_assignments)]\n\
                  pub fn f() { let mut p: Box<i32> = Box::new(1); p = Box::new(2); let _ = *p; }\n";
    let drops = super::verify::box_mir_drops_str(source).expect("observe emitted MIR drops");
    let receipt = super::verify::reconcile_box_mir_drop_policies(
        &drops,
        &[super::verify::BoxMirDropPolicy {
            subject: "f::p#1".to_owned(),
            function: "f".to_owned(),
            local_name: Some("p".to_owned()),
            overwrite_sites: vec!["<original>:2:57".to_owned()],
            retained_sink: false,
            optional: false,
            implicit_scope_close: true,
        }],
    )
    .expect("all implicit drops are authorized");
    assert!(receipt.contains("waiver-drop(overwrite)"), "{receipt}");
    assert!(receipt.contains("waiver-drop(scope-exit)"), "{receipt}");
    assert!(receipt.contains("waiver-drop(unwind)"), "{receipt}");
    assert!(receipt.contains("<original>:2:57"), "{receipt}");
}

const ROOT_WITH_MODULE: &str = "#![allow(dead_code, unused_unsafe)]\npub mod m;\n";
const MODULE_SUBJECT: &str = "pub unsafe fn bump(p: *mut i32) -> i32 {\n    *p += 1;\n    *p\n}\n";

/// **RED (i).** A crate root plus a module, with the subject in the *module*:
/// the module's text is rewritten and the root — which has no subject — is not
/// emitted at all.
///
/// This is the shape 10 corpus programs have and no golden has: the file that
/// gets edited is not the file the compiler was pointed at.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** remove the
/// `files.insert(..)` in `emit_files`'s per-file loop and this fails — nothing
/// is emitted for the module.
#[test]
fn a_subject_in_a_module_is_emitted_into_that_module() {
    let fixture = Fixture::new(&[("lib.rs", ROOT_WITH_MODULE), ("m.rs", MODULE_SUBJECT)]);
    let emission = emit(&fixture);

    let module = text_for(&emission, "m.rs").expect("the module was emitted");
    assert!(
        module.contains("p: &mut i32"),
        "the module's subject was not rewritten: {module}"
    );
    assert!(
        text_for(&emission, "lib.rs").is_none(),
        "the crate root has no subject and must not be emitted: {:?}",
        emission.files.keys().collect::<Vec<_>>()
    );
    assert!(emission.rollbacks.is_empty(), "{:?}", emission.rollbacks);
    assert!(
        emission.unplaceable.is_empty(),
        "{:?}",
        emission.unplaceable
    );
}

/// **RED (ii) — the file-collapse witness.** Subjects in BOTH files, with
/// *different pointee types*, so an edit landing in the wrong file is visible
/// rather than merely mis-positioned.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** collapse the grouping
/// in `emit_files` — key every edit under one `FileKey` — and this fails. That
/// is the exact defect the map shape exists to make unrepresentable: offsets are
/// file-relative, so a collapsed plan splices one file's ranges into another's
/// text and produces a plausible-looking result.
#[test]
fn each_edit_lands_in_its_own_file() {
    let fixture = Fixture::new(&[
        (
            "lib.rs",
            "#![allow(dead_code, unused_unsafe)]\npub mod other;\npub unsafe fn root_bump(p: *mut i32) -> i32 {\n    *p += 1;\n    *p\n}\n",
        ),
        (
            "other.rs",
            "pub unsafe fn other_bump(q: *mut i64) -> i64 {\n    *q += 1;\n    *q\n}\n",
        ),
    ]);
    let emission = emit(&fixture);

    assert_eq!(
        emission.files.len(),
        2,
        "both files carry a subject, so both must be emitted: {:?}",
        emission.files.keys().collect::<Vec<_>>()
    );
    let root = text_for(&emission, "lib.rs").expect("root emitted");
    let other = text_for(&emission, "other.rs").expect("module emitted");

    assert!(
        root.contains("p: &mut i32"),
        "the root's own subject was not rewritten in the root: {root}"
    );
    assert!(
        other.contains("q: &mut i64"),
        "the module's own subject was not rewritten in the module: {other}"
    );
    // The discriminator: each file kept ITS pointee type. A collapsed grouping
    // splices the other file's range and cannot preserve both.
    assert!(
        !root.contains("i64"),
        "the module's edit leaked into the root: {root}"
    );
    assert!(
        !other.contains("i32"),
        "the root's edit leaked into the module: {other}"
    );
    assert!(emission.rollbacks.is_empty(), "{:?}", emission.rollbacks);
}

/// **RED (iii) — the unplaceable guard.** A macro-generated declaration has no
/// source range anyone can splice; it is recorded with its reason and
/// attribution rather than silently skipped.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** remove the
/// `span.from_expansion()` guard in `emit_files`'s `span_to_loc` and this fails
/// — `unplaceable` is empty and the decision disappears without a trace.
#[test]
fn a_macro_generated_declaration_is_recorded_as_unplaceable() {
    let fixture = Fixture::new(&[(
        "lib.rs",
        "#![allow(dead_code, unused_unsafe)]\nmacro_rules! mk {\n    () => {\n        pub unsafe fn mac_bump(p: *mut i32) -> i32 {\n            *p += 1;\n            *p\n        }\n    };\n}\nmk!();\n",
    )]);
    let emission = emit(&fixture);

    assert_eq!(
        emission.unplaceable.len(),
        1,
        "the macro-generated subject must be recorded, not dropped: {:?}",
        emission.unplaceable
    );
    assert_eq!(
        emission.unplaceable[0].reason,
        "span is macro-generated and cannot be spliced into source"
    );
    assert!(
        emission.unplaceable[0].detail.contains('p'),
        "the record must attribute the subject: {:?}",
        emission.unplaceable[0]
    );
    assert!(
        emission.files.is_empty(),
        "nothing is emitted for an unplaceable subject: {:?}",
        emission.files.keys().collect::<Vec<_>>()
    );
}

// ---------------------------------------------------------------------------
// S2b.0a.2 — verify from a temp copy. The isolation witness lands HERE, before
// any corpus contact, by ruling: the frozen tree's digest is a standing
// invariant, so the guard that protects it must exist before the first run that
// could threaten it.
// ---------------------------------------------------------------------------

/// **RED.** A rewritten two-file crate compiles *as a crate* from the temp copy
/// — which the string gate cannot express, because modules resolve relative to
/// the root's directory.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** remove the overwrite
/// loop in `materialize` and this fails. The `contains` assertion is what makes
/// that deletion detectable: the untouched copy still type-checks, so a witness
/// that only asserted the gate passed would survive the deletion — the
/// outcome-counting shape that already cost one repair this slice.
#[test]
fn a_rewritten_two_file_crate_type_checks_from_a_temp_copy() {
    let fixture = Fixture::new(&[("lib.rs", ROOT_WITH_MODULE), ("m.rs", MODULE_SUBJECT)]);
    let emission = emit(&fixture);
    let temp = verify::materialize(&fixture.root(), &emission.files).expect("materialize");

    let copied = fs::read_to_string(temp.root().parent().expect("temp dir").join("m.rs"))
        .expect("module present in the copy");
    assert!(
        copied.contains("p: &mut i32"),
        "the copy does not carry the rewrite: {copied}"
    );
    assert!(
        verify::type_checks_crate(temp.root()),
        "the rewritten crate must type-check as a crate"
    );
}

/// **Non-vacuity.** The temp-copy gate can FAIL. Without this, every passing
/// result above is compatible with a gate that always says yes.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** make
/// `type_checks_crate` return `true` unconditionally and this fails.
#[test]
fn a_broken_rewrite_fails_the_temp_copy_gate() {
    let fixture = Fixture::new(&[("lib.rs", ROOT_WITH_MODULE), ("m.rs", MODULE_SUBJECT)]);
    let mut emission = emit(&fixture);
    for text in emission.files.values_mut() {
        *text =
            "pub unsafe fn bump(p: &mut i32) -> i32 {\n    let _x: u8 = \"not a u8\";\n    *p\n}\n"
                .to_owned();
    }
    let temp = verify::materialize(&fixture.root(), &emission.files).expect("materialize");

    assert!(
        !verify::type_checks_crate(temp.root()),
        "a crate with a type error passed the hard gate"
    );
}

/// **THE ISOLATION WITNESS.** Emitting and verifying leaves the input tree
/// byte-identical.
///
/// This is the guard standing between the rewriter and the frozen `rs-crown`
/// corpus, whose digest is an invariant of the whole evaluation. It is asserted
/// on a throwaway fixture precisely so it never has to be discovered on the
/// corpus.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** point `materialize`'s
/// write at the ORIGINAL path instead of the copy and this fails.
#[test]
fn materializing_never_touches_the_original_tree() {
    let fixture = Fixture::new(&[("lib.rs", ROOT_WITH_MODULE), ("m.rs", MODULE_SUBJECT)]);
    let before = fixture.snapshot();

    let emission = emit(&fixture);
    let temp = verify::materialize(&fixture.root(), &emission.files).expect("materialize");
    let _ = verify::type_checks_crate(temp.root());

    let after = fixture.snapshot();
    assert_eq!(
        before, after,
        "the input tree was modified by emit+verify; the frozen corpus would be next"
    );
}

// ---------------------------------------------------------------------------
// S2b.0a.4 — CORPUS SMOKE. First contact between emission and a real
// multi-file program. rgba is the smallest genuinely CROSS-FILE program in the
// frozen corpus (14 subject rows over 2 files); bst and avl are multi-file
// crates whose subjects all sit in one file, so they would not exercise
// grouping at all.
//
// Guards, per ruling: temp copies only, and the frozen tree is asserted
// byte-identical afterwards. The corpus-wide digest is checked by the
// invocation around this test.
// ---------------------------------------------------------------------------

/// Bytes of every `.rs` file under `dir`, by path.
fn tree_snapshot(dir: &std::path::Path) -> BTreeMap<PathBuf, Vec<u8>> {
    fn walk(dir: &std::path::Path, out: &mut BTreeMap<PathBuf, Vec<u8>>) {
        for entry in fs::read_dir(dir).expect("corpus dir readable") {
            let entry = entry.expect("corpus entry");
            let path = entry.path();
            if entry.file_type().expect("file type").is_dir() {
                walk(&path, out);
            } else {
                out.insert(path.clone(), fs::read(&path).expect("corpus file readable"));
            }
        }
    }
    let mut out = BTreeMap::new();
    walk(dir, &mut out);
    out
}

#[test]
#[ignore = "S2b.0a.4 corpus smoke: reads the frozen rs-crown tree"]
fn rgba_smoke_emits_and_verifies_from_a_temp_copy() {
    let crate_dir =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../benchmarks/rs-crown/rgba");
    let root = crate_dir.join("lib.rs");
    assert!(root.is_file(), "frozen corpus input missing: {root:?}");

    let before = tree_snapshot(&crate_dir);
    let outcome = super::rewrite_m1_path(&root);
    let after = tree_snapshot(&crate_dir);

    assert_eq!(
        before, after,
        "THE FROZEN CORPUS WAS MODIFIED by an emission run — temp copies only"
    );

    match outcome {
        super::RewriteOutcome::Emitted {
            files,
            emitted_count,
            degradations,
            unplaceable,
            ..
        } => {
            println!(
                "RGBA-SMOKE emitted_count={emitted_count} files_touched={} \
                 degradations={} unplaceable={}",
                files.len(),
                degradations.len(),
                unplaceable.len()
            );
            for key in files.keys() {
                println!("RGBA-SMOKE file={key:?}");
            }
            assert!(
                unplaceable.is_empty(),
                "unplaceable is expected-zero on this corpus: {unplaceable:?}"
            );
            // The POINT of this smoke: emission reached more than one file of a
            // real program. Without these two, the witness passes on an
            // emission that touched nothing — the outcome-counting shape that
            // has already cost two repairs in this slice sequence.
            assert!(
                emitted_count >= 1,
                "the smoke must emit at least one subject, not merely succeed"
            );
            assert!(
                files.len() >= 2,
                "rgba's subjects span two files; a run that touched {} file(s) \
                 did not exercise cross-file emission at all",
                files.len()
            );
        }
        super::RewriteOutcome::Degraded {
            reason,
            degradations,
            ..
        } => {
            panic!(
                "rgba did not emit: {reason} ({} degradation(s))",
                degradations.len()
            );
        }
    }
}

/// **S2b.1.2 RED — the batch revert loop.** A crate with one GOOD rewrite and
/// one that breaks type-checking: the bad one is taken back, the good one
/// survives, and the crate emits.
///
/// This is the whole point of the per-function gate. Under the old whole-crate
/// verdict this crate produced NOTHING — one bad subject discarded every good
/// rewrite in the program, which S2b.0 measured as 10 of 20 corpus programs.
///
/// `bad.rs` mirrors `ht`'s real corpus shape (a rewritten parameter stored into
/// a raw-pointer struct field); `good.rs` mirrors `g01`.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** remove
/// `reverted.extend(newly)` so nothing is ever taken back — the loop makes no
/// progress, escalates, and this fails.
#[test]
fn a_bad_rewrite_is_reverted_and_the_good_one_survives() {
    let fixture = Fixture::new(&[
        (
            "lib.rs",
            "#![allow(dead_code, unused_unsafe)]\npub mod good;\npub mod bad;\n",
        ),
        (
            "good.rs",
            "pub unsafe fn bump(p: *mut i32) -> i32 {\n    *p += 1;\n    *p\n}\n",
        ),
        ("bad.rs", BREAKS_ON_REWRITE),
    ]);

    // INJECTED since step 2 — the broken emission is supplied as data, per
    // `emit_injected`. The revert loop, the good rewrite and the crate are
    // unchanged; only the source of the bad edit is.
    match super::rewrite_m1_path_injected(&fixture.root(), 8, &force_stash_value_shared) {
        super::RewriteOutcome::Emitted {
            files,
            emitted_count,
            degradations,
            ..
        } => {
            let reverted: Vec<_> = degradations
                .iter()
                .filter(|d| d.reason == super::decision::DegradeReason::RevertedAfterVerifyFailure)
                .collect();
            assert!(
                !reverted.is_empty(),
                "nothing was recorded as reverted, so the crate passed for some \
                 other reason: {degradations:?}"
            );
            assert!(
                emitted_count >= 1,
                "the GOOD rewrite was discarded too — the loop reverted more \
                 than the error attributed"
            );
            let good = files
                .iter()
                .find(|(k, _)| format!("{k:?}").contains("good.rs"))
                .map(|(_, text)| text.clone())
                .expect("good.rs was emitted");
            assert!(
                good.contains("p: &mut i32"),
                "the good rewrite did not survive: {good}"
            );
            let bad = files
                .iter()
                .find(|(k, _)| format!("{k:?}").contains("bad.rs"));
            assert!(
                bad.is_none_or(|(_, text)| !text.contains("value: &")),
                "the bad rewrite survived the revert: {bad:?}"
            );
        }
        super::RewriteOutcome::Degraded { reason, .. } => {
            panic!("the loop failed to recover a partially-bad crate: {reason}")
        }
    }
}

/// **S2b.1.2 RED — ACCOUNTING through the loop.** A reverted subject moves from
/// emitted to degraded under its own reason key, so
/// `emitted_final + degraded` still equals the subject count.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** stop pushing the
/// `RevertedAfterVerifyFailure` degradations and this fails — the identity
/// loses exactly the reverted subjects.
#[test]
fn the_accounting_identity_survives_a_revert() {
    let fixture = Fixture::new(&[
        (
            "lib.rs",
            "#![allow(dead_code, unused_unsafe)]\npub mod good;\npub mod bad;\n",
        ),
        (
            "good.rs",
            "pub unsafe fn bump(p: *mut i32) -> i32 {\n    *p += 1;\n    *p\n}\n",
        ),
        ("bad.rs", BREAKS_ON_REWRITE),
    ]);
    // Subject count from a NO-LOOP emission: what the decision phase decided,
    // which the loop must not change.
    // PLACED subjects only, as of S2b.3. `emitted` counts placements, so an
    // unplaceable decision belongs to neither side of this identity — it is
    // accounted for in the corpus identity `emitted + degraded + unplaceable`,
    // not in the loop's. Zero on this fixture either way; the derivation is
    // corrected so it stays true when it is not.
    let subjects = {
        let emission = emit(&fixture);
        emission.plan.by_file.values().map(Vec::len).sum::<usize>()
    };

    match super::rewrite_m1_path(&fixture.root()) {
        super::RewriteOutcome::Emitted {
            emitted_count,
            degradations,
            ..
        } => {
            let reverted = degradations
                .iter()
                .filter(|d| d.reason == super::decision::DegradeReason::RevertedAfterVerifyFailure)
                .count();
            assert_eq!(
                emitted_count + reverted,
                subjects,
                "emitted {emitted_count} + reverted {reverted} != {subjects} \
                 planned subjects — the loop lost or invented one"
            );
        }
        super::RewriteOutcome::Degraded { reason, .. } => panic!("{reason}"),
    }
}

// ---------------------------------------------------------------------------
// S2b.1.1 witnesses — structural diagnostic capture. FIXTURE-VALIDATED; the
// cross-check against the rendered parser's 86 corpus diagnostics runs at 1.4.
// ---------------------------------------------------------------------------

/// The two-file crate whose rewrite breaks it, mirroring `ht`'s corpus shape:
/// a rewritten parameter stored into a raw-pointer struct field.
const BREAKS_ON_REWRITE: &str = "pub struct Holder {\n    pub slot: *mut i32,\n}\npub unsafe fn stash(value: *mut i32, holder: *mut Holder) {\n    (*holder).slot = value;\n}\n";

fn diagnose_after_rewrite(files: &[(&str, &str)]) -> (verify::Diagnosis, Fixture) {
    let fixture = Fixture::new(files);
    // INJECTED since step 2 — see `emit_injected`. The crate under diagnosis is
    // the same one these witnesses always used; only the decision that produces
    // it is now supplied rather than derived.
    let emission = emit_injected(&fixture, &force_stash_value_shared);
    let temp = verify::materialize(&fixture.root(), &emission.files).expect("materialize");
    let diagnosis = verify::diagnose_crate(temp.root());
    (diagnosis, fixture)
}

/// **RED.** A type error is located structurally — file and line, straight from
/// the diagnostic's primary span, with no rendered text parsed.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** remove the
/// `diags.lock().push(..)` in `Capture::emit_diagnostic` and this fails.
#[test]
fn structural_capture_locates_a_type_error() {
    let (d, _fixture) = diagnose_after_rewrite(&[
        (
            "lib.rs",
            "#![allow(dead_code, unused_unsafe)]\npub mod m;\n",
        ),
        ("m.rs", BREAKS_ON_REWRITE),
    ]);
    assert_eq!(d.diags.len(), 1, "expected one located diagnostic: {d:?}");
    assert_eq!(
        d.diags[0].line, 5,
        "the store is on line 5: {:?}",
        d.diags[0]
    );
    assert!(
        d.diags[0].file.ends_with("m.rs"),
        "located in the wrong file: {:?}",
        d.diags[0]
    );
}

/// **RED — COUNT INDEPENDENCE.** The error count comes from `Level` alone, never
/// from extraction. rustc emits a spanless error-level summary alongside the
/// located error, so the counts genuinely differ: **2 counted, 1 located**.
///
/// That gap is what makes this witness able to fail at all — without a naturally
/// spanless diagnostic, `errors == diags.len()` would hold either way and the
/// mutation below would be ineffective.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** derive the count from
/// extraction (`errors: diags.len()`) and this fails, 1 against 2.
#[test]
fn the_error_count_comes_from_level_not_from_extraction() {
    let (d, _fixture) = diagnose_after_rewrite(&[
        (
            "lib.rs",
            "#![allow(dead_code, unused_unsafe)]\npub mod m;\n",
        ),
        ("m.rs", BREAKS_ON_REWRITE),
    ]);
    assert_eq!(d.errors, 2, "error count must come from Level: {d:?}");
    assert_eq!(
        d.diags.len(),
        1,
        "one of the two errors is spanless and cannot be located — that is \
         precisely why the count must not be derived from extraction: {d:?}"
    );
    assert!(
        d.errors > d.diags.len(),
        "a dropped diagnostic would lower the count and fake progress for the \
         no-progress detector"
    );
}

/// **RED.** Direction is what distinguishes whose rewrite caused the error;
/// containment only says where it is.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** swap the two arms of
/// `classify` and this fails.
#[test]
fn direction_identifies_a_rewritten_value_flowing_into_a_raw_context() {
    let (d, _fixture) = diagnose_after_rewrite(&[
        (
            "lib.rs",
            "#![allow(dead_code, unused_unsafe)]\npub mod m;\n",
        ),
        ("m.rs", BREAKS_ON_REWRITE),
    ]);
    assert_eq!(
        d.diags[0].direction,
        verify::Direction::RewrittenIntoRaw,
        "the rewritten parameter flows INTO a raw context, so the containing \
         function's own rewrite is the culprit: {:?}",
        d.diags[0]
    );
}

/// **Non-vacuity, and the WARNING filter.** A crate that type-checks yields no
/// errors — without this, every count above is compatible with a capture that
/// reports errors unconditionally.
///
/// The fixture **deliberately emits a warning** (`unused_variables`, with no
/// crate-level `allow`) so that the `Level` filter is load-bearing here.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** drop the `Level` filter
/// in `emit_diagnostic` and this fails — the warning is counted as an error.
///
/// **Written after the first version SURVIVED that deletion.** It used the
/// `ROOT_WITH_MODULE` fixture, whose `#![allow(dead_code, unused_unsafe)]`
/// suppresses every warning, so there was nothing for the filter to filter and
/// the doc comment's claim that "the fixture emits warnings" was simply untrue.
#[test]
fn a_clean_crate_yields_no_diagnostics() {
    let (d, _fixture) = diagnose_after_rewrite(&[
        ("lib.rs", "pub mod m;\n"),
        (
            "m.rs",
            "pub unsafe fn bump(p: *mut i32) -> i32 {\n    let unused_thing = 5;\n    *p += 1;\n    *p\n}\n",
        ),
    ]);
    assert_eq!(d.errors, 0, "a clean rewrite reported errors: {d:?}");
    assert!(d.diags.is_empty(), "{d:?}");
    assert_eq!(d.unrenderable, 0, "{d:?}");
}

/// **S2b.1.3 — the CAP arm of the dual termination, witnessed.**
///
/// The cap is configured to its boundary (0 rounds) on a fixture that genuinely
/// needs one, so reaching the cap is real behaviour rather than a manufactured
/// loop.
///
/// **Why the boundary rather than a multi-round fixture.** The coupled shape
/// (`outer` calls `inner`, both rewritten, `inner`'s body carrying the error)
/// was built and MEASURED: it converges in ONE round, `reverted=2`, because
/// BATCH-revert takes every attributed function in the same round. Constraint
/// (a) is precisely what collapses a cascade into one round, so multi-round
/// convergence is rare *by design* and the cap is hard to reach naturally. That
/// is the mechanism working, not a gap in the fixture.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** disable the cap check
/// and this fails — the loop converges and returns `Emitted`.
#[test]
fn the_round_cap_stops_the_loop() {
    let fixture = Fixture::new(&[
        (
            "lib.rs",
            "#![allow(dead_code, unused_unsafe)]\npub mod good;\npub mod bad;\n",
        ),
        (
            "good.rs",
            "pub unsafe fn bump(p: *mut i32) -> i32 {\n    *p += 1;\n    *p\n}\n",
        ),
        ("bad.rs", BREAKS_ON_REWRITE),
    ]);
    // INJECTED since step 2 — the broken emission is supplied as data, per
    // `emit_injected`. The cap is still 0 and the loop still cannot converge;
    // only the source of the bad edit changed.
    match super::rewrite_m1_path_injected(&fixture.root(), 0, &force_stash_value_shared) {
        super::RewriteOutcome::Emitted {
            escalated,
            bisect_probes,
            ..
        } => {
            let reason = escalated.expect("the cap must have escalated");
            assert!(
                reason.contains("round cap"),
                "escalated for the wrong reason: {reason}"
            );
            assert!(bisect_probes > 0, "escalation did not reach bisect");
        }
        super::RewriteOutcome::Degraded { reason, .. } => {
            panic!("bisect failed to recover after the cap fired: {reason}")
        }
    }
}

/// `caller` passes one rewritten parameter (`q`) through and one raw parameter
/// (`r`) to `callee`, which IS rewritten. That is heman's inverted shape: the
/// culprit is the CALLEE, while the error lands inside the caller.
const INVERTED: &str = "pub unsafe fn callee(p: *mut i32) -> i32 {\n    *p\n}\npub unsafe fn caller(q: *mut i32, r: *mut i32) -> i32 {\n    *q + callee(r)\n}\n";

/// Force `caller`'s `r` to stay raw, so the rewritten `callee` is reached with a
/// raw pointer. A1's `CallSiteNotAdapted` normally prevents this — which is why
/// it is injected at the phase boundary rather than written as source.
fn keep_r_raw(table: &mut super::decision::DecisionTable) {
    for (subject, decision) in &mut table.entries {
        // Force the CALLEE to be rewritten — A1 degrades it precisely because
        // its call site is unadapted, which is the guard this injection exists
        // to step around.
        if subject.param_name.as_deref() == Some("p") {
            *decision = super::decision::Decision::Ref { mutable: false };
        }
        if subject.param_name.as_deref() == Some("q") {
            *decision = super::decision::Decision::Ref { mutable: false };
        }
        if subject.param_name.as_deref() == Some("r") {
            *decision = super::decision::Decision::Degraded(super::decision::Degradation {
                subject: "caller::r".to_owned(),
                site: "<injected>".to_owned(),
                reason: super::decision::DegradeReason::CallSiteNotAdapted,
            });
        }
    }
}

/// **CLS-W2 — an error in an unedited caller names the converted callee class.**
///
/// The inverted-direction shape: the error lands inside `caller`, so span
/// attribution reverts `caller` — but the culprit is `callee`, and the error
/// survives. Wave 3 carries the whole-call seam interval under the callee
/// class, so the first round takes back exactly that class and converges
/// without bisection.
///
/// **Why injection is legitimate here.** This is a DERIVED breach shape, not an
/// invention: reality emits it (1 of 86 corpus diagnostics, in heman), and A1's
/// `CallSiteNotAdapted` is exactly what normally prevents it — so it cannot be
/// written as ordinary source. The between-phase hook exists to test downstream
/// phases against shapes the upstream guard suppresses.
#[test]
fn an_unedited_caller_error_reverts_only_converted_callee_class() {
    let fixture = Fixture::new(&[
        (
            "lib.rs",
            "#![allow(dead_code, unused_unsafe)]\npub mod m;\n",
        ),
        ("m.rs", INVERTED),
    ]);
    match super::rewrite_m1_path_injected(&fixture.root(), 8, &keep_r_raw) {
        super::RewriteOutcome::Emitted {
            escalated,
            bisect_probes,
            reverted_count,
            ..
        } => {
            assert!(escalated.is_none(), "direct seam attribution escalated");
            assert_eq!(bisect_probes, 0, "direct attribution invoked bisect");
            assert_eq!(reverted_count, 1, "more than the callee class reverted");
        }
        super::RewriteOutcome::Degraded {
            reason,
            source,
            files,
            reverted_count,
            bisect_probes,
            raw_boundary_artifacts,
            ..
        } => {
            assert!(reason.contains("reverting every ready signature class"));
            assert_eq!(reverted_count, 1);
            assert_eq!(bisect_probes, 0);
            assert_eq!(
                source,
                std::fs::read_to_string(fixture.root()).expect("root input")
            );
            for (key, text) in files {
                if let super::plan::FileKey::Real(path) = key {
                    assert_eq!(text, std::fs::read_to_string(path).expect("input file"));
                }
            }
            assert_eq!(
                raw_boundary_artifacts
                    .unresolved_classes
                    .lines()
                    .skip(1)
                    .count(),
                1
            );
            assert_eq!(
                raw_boundary_artifacts.degraded_output_receipt,
                "degraded-unmodified-input"
            );
            assert!(raw_boundary_artifacts.bridge_events.iter().all(|event| {
                event.stage != super::bridge_receipt::BridgeReceiptStage::Terminal
                    || event.state == super::bridge_receipt::BridgeReceiptState::Dropped
            }));
            let summary = super::bridge_receipt::reconcile_bridge_events(
                &raw_boundary_artifacts.bridge_events,
            )
            .expect("Degraded terminal receipts reconcile");
            assert_eq!(summary.applied_events, 0);
        }
    }
}

/// Duplicate every entry, so `plan` emits two identical edits per subject and
/// `apply` must reject the second as overlapping.
fn duplicate_entries(table: &mut super::decision::DecisionTable) {
    let cloned = table.entries.clone();
    table.entries.extend(cloned);
}

/// **S2b.1.3 — the ROLLBACK guard, witnessed where it actually fires.**
///
/// An incoherent plan (two identical edits per subject) is rejected by the
/// PRE-LOOP structural gate, before any revert round and before bisect —
/// `bisect_probes == 0` is what proves it never got that far.
///
/// **This also locates the arm.** The post-bisect guard's `rollbacks` check was
/// suspected unwitnessed; measuring shows it is *unreachable* rather than
/// untested, because `render` applies a SUBSET of edits that already produced no
/// rollbacks, and dropping edits cannot create an overlap, an out-of-bounds
/// range, or a char-boundary violation. That arm is a stated control at its
/// guard; this witness covers the arm that can fire.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** remove the
/// `emission.rollbacks` check and this fails — the deduped edit set emits and
/// type-checks, so an incoherent plan passes silently.
#[test]
fn an_incoherent_plan_is_rejected_before_the_loop() {
    let fixture = Fixture::new(&[
        (
            "lib.rs",
            "#![allow(dead_code, unused_unsafe)]\npub mod m;\n",
        ),
        ("m.rs", MODULE_SUBJECT),
    ]);
    match super::rewrite_m1_path_injected(&fixture.root(), 8, &duplicate_entries) {
        super::RewriteOutcome::Degraded {
            reason,
            bisect_probes,
            ..
        } => {
            assert!(
                reason.contains("rolled back"),
                "rejected for the wrong reason: {reason}"
            );
            assert_eq!(
                bisect_probes, 0,
                "an incoherent plan reached bisect instead of being rejected"
            );
        }
        super::RewriteOutcome::Emitted { .. } => {
            panic!("an incoherent plan emitted")
        }
    }
}

/// **S2b.1 F3 — a FAILING outcome carries what the run attempted.**
///
/// Both outcome variants are built at exactly one site each (enforced by
/// `each_outcome_variant_has_exactly_one_filling_site`), so this witnesses the
/// field at the site every `Degraded` flows through.
///
/// **Why not an end-to-end brotli-shaped fixture.** brotli's `Degraded` arose
/// because bisect returned a non-compiling set — the F2 defect. With candidates
/// derived from the plan's `owner_fn` domain the base case holds by
/// construction, so that shape should no longer be reachable; the remaining
/// `Degraded`-with-reverted paths are the budget deferral and a materialize IO
/// error, neither constructible in a unit test without an env knob or an
/// injected filesystem failure. Witnessing the filling site is the honest
/// substitute, and the corpus re-run is what checks the shape is gone.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** re-zero
/// `reverted_count` in `OutcomeFacts::degraded` and this fails.
#[test]
fn a_failing_outcome_carries_its_reverted_count() {
    let facts = super::OutcomeFacts {
        emitted_count: 7,
        reverted_count: 3,
        files_touched: 2,
        attribution_blind: 1,
        ..Default::default()
    };
    match facts.degraded("escalation-deferred: budget".to_owned()) {
        super::RewriteOutcome::Degraded {
            emitted_count,
            reverted_count,
            files_touched,
            attribution_blind,
            ..
        } => {
            assert_eq!(
                reverted_count, 3,
                "a failing outcome zeroed its revert count — the defect this \
                 structure exists to prevent, twice over"
            );
            assert_eq!(emitted_count, 7, "the ATTEMPT must survive the failure");
            assert_eq!(files_touched, 2);
            assert_eq!(attribution_blind, 1);
        }
        super::RewriteOutcome::Emitted { .. } => panic!("degraded() built an Emitted"),
    }
}

fn census_test_solve_receipt() -> crate::analyses::borrow_ownership::model_cache::SolveReceipt {
    crate::analyses::borrow_ownership::model_cache::SolveReceipt {
        source: "cache".to_owned(),
        cache_status: "hit".to_owned(),
        fingerprint: "fixture-fingerprint".to_owned(),
        model_sha256: "fixture-model".to_owned(),
        cache_entry: Some("fixture-entry".to_owned()),
        solve_wall_s: "0.000000".to_owned(),
    }
}

#[test]
fn census_capture_keeps_the_terminal_outcome_and_emitted_tree() {
    let files = [(
        super::plan::FileKey::Real(std::path::PathBuf::from("/fixture/lib.rs")),
        "fn f() {}\n".to_owned(),
    )]
    .into_iter()
    .collect::<std::collections::BTreeMap<_, _>>();
    let facts = super::OutcomeFacts {
        observed_root: Some(std::path::PathBuf::from("/fixture")),
        escalated: Some("recovered after attribution\nwith full detail".to_owned()),
        bisect_probes: 3,
        verify_rounds: 2,
        reverted_count: 1,
        solve_receipt: Some(census_test_solve_receipt()),
        ..Default::default()
    };
    let capture = facts
        .emitted("fn f() {}\n".to_owned(), files.clone())
        .into_e1_capture()
        .expect("capture emitted outcome");
    assert_eq!(capture.outcome_kind, super::CensusOutcomeKind::Emitted);
    assert_eq!(
        capture.escalation,
        "recovered after attribution\nwith full detail"
    );
    assert_eq!((capture.bisect_probes, capture.verify_rounds), (3, 2));
    assert_eq!(capture.reverted_count, 1);
    assert_eq!(capture.emitted_files, Some(files));
}

#[test]
fn census_capture_keeps_a_degraded_reason_and_has_no_emitted_tree() {
    let reason = "escalation-required: no progress\nfull residual";
    let facts = super::OutcomeFacts {
        observed_root: Some(std::path::PathBuf::from("/fixture")),
        bisect_probes: 5,
        verify_rounds: 4,
        reverted_count: 7,
        solve_receipt: Some(census_test_solve_receipt()),
        ..Default::default()
    };
    let capture = facts
        .degraded(reason.to_owned())
        .into_e1_capture()
        .expect("capture degraded outcome");
    assert_eq!(capture.outcome_kind, super::CensusOutcomeKind::Degraded);
    assert_eq!(capture.escalation, reason);
    assert_eq!((capture.bisect_probes, capture.verify_rounds), (5, 4));
    assert_eq!(capture.reverted_count, 7);
    assert_eq!(capture.emitted_files, None);
}

/// **An EMITTED outcome carries the ruled `files_touched`, not its map size.**
///
/// The twin of `a_failing_outcome_carries_its_reverted_count`, for the arm that
/// did not have one. `Degraded` carried the ruled value all along; `emitted()`
/// DROPPED it, so the only consumer recovered a number by measuring `files`
/// instead. On the span layer the two agree — `render` returns edited files
/// only — so the defect was invisible for the whole span era and surfaced the
/// moment the AST layer's SEEDED map made them differ.
///
/// The fixture encodes exactly that disagreement: `files_touched: 0` against a
/// ONE-entry map. That is not a contrived pair, it is `bst` — converged with
/// every subject reverted, emitting its substrate unchanged, and reported as
/// touching one file against the span layer's zero.
///
/// *Mutation-tested.* **Deletion first:** drop `files_touched: self.files_touched`
/// from `OutcomeFacts::emitted` and this fails to compile, which is the
/// strongest available failure. **Faithful second:** write
/// `files_touched: files.len()` there — the exact defect, spelled as a plausible
/// fix — and this fails 1 vs 0.
#[test]
fn an_emitted_outcome_carries_the_ruled_files_touched() {
    let facts = super::OutcomeFacts {
        emitted_count: 0,
        reverted_count: 1,
        files_touched: 0,
        ..Default::default()
    };
    let mut files = std::collections::BTreeMap::new();
    files.insert(
        super::plan::FileKey::Real(std::path::PathBuf::from("/x/lib.rs")),
        "fn f() {}\n".to_owned(),
    );
    match facts.emitted("fn f() {}\n".to_owned(), files) {
        super::RewriteOutcome::Emitted {
            files_touched,
            files,
            ..
        } => {
            assert_eq!(
                files_touched, 0,
                "an emitted outcome reported its emission MAP SIZE as \
                 files_touched; the map is seeded on the AST layer, so this \
                 counts a file the rewrite never touched"
            );
            assert_eq!(
                files.len(),
                1,
                "the map itself must still carry the file — the emission is \
                 what it is; only the COUNTER was wrong, and a fix that \
                 dropped the file would trade a counter defect for an \
                 emission one"
            );
        }
        super::RewriteOutcome::Degraded { .. } => panic!("emitted() built a Degraded"),
    }
}

/// **brotli investigation (a) — PRISTINE-COPY CONTROL.**
///
/// Materialize brotli with ZERO edits and type-check the copy. This is the
/// `k == candidates.len()` base case in isolation: if an unedited copy does not
/// compile, the base case was never testable for brotli and the failure is an
/// environment/temp-copy defect rather than a loop defect.
#[test]
#[ignore = "brotli control: one full type-check of the frozen corpus program"]
fn zz_brotli_pristine_copy_control() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../benchmarks/rs-crown/brotli/lib.rs");
    assert!(root.is_file(), "frozen input missing: {root:?}");

    // IN PLACE, no copy: distinguishes "the temp copy breaks it" from "the
    // input never passed this gate".
    let in_place = verify::diagnose_crate(&root);
    println!(
        "BROTLI-CONTROL in_place errors={} diags={}",
        in_place.errors,
        in_place.diags.len()
    );
    let empty = BTreeMap::new();
    let temp = verify::materialize(&root, &empty).expect("materialize pristine copy");
    let d = verify::diagnose_crate(temp.root());
    println!(
        "BROTLI-CONTROL pristine errors={} diags={} unrenderable={}",
        d.errors,
        d.diags.len(),
        d.unrenderable
    );
    // The OLD gate semantics: FatalError propagation only, which is what
    // `type_checks_crate` meant before 1.1 routed it through `diagnose_crate`.
    let old_gate = ::utils::compilation::run_compiler_on_path(temp.root(), |tcx| {
        ::utils::type_check(tcx);
    })
    .is_ok();
    println!(
        "BROTLI-CONTROL old_gate_is_ok={old_gate} new_gate_passes={}",
        d.errors == 0
    );
    for x in d.diags.iter().take(8) {
        println!(
            "BROTLI-CONTROL diag {}:{} {:?}",
            x.file, x.line, x.direction
        );
        println!(
            "BROTLI-CONTROL   msg={}",
            &x.message[..x.message.len().min(160)]
        );
    }
}

/// **S2b.2 repair — the probe instrument must carry its payload.**
///
/// `diagnose_once` returns what the verify compile CAPTURED. This pins that it
/// is non-empty for a fixture with a known diagnostic — the test that did not
/// exist when the differential gate moved the payload assignment below the
/// `probe_only` early return, leaving `run_m1_diag` reporting
/// `struct_diags=0 status=ok` for every program from 2026-08-04 14:49 until
/// this repair.
///
/// # Why this fixture cannot go quiet
///
/// Non-emptiness rests on a **pre-existing** `invalid_reference_casting` error
/// in the unmodified source, not on the rewriter producing one. A witness that
/// depended on the rewrite emitting a *bad* rewrite would go silently vacuous
/// the moment the rewriter improved — which is the failure shape this file
/// already records four instances of. Probe mode returns the RAW capture, so
/// the baseline diagnostic is exactly what reaches the assertion.
///
/// # Branch taken (Rider 7)
///
/// `tree_base = Some(root)` — a real multi-file tree materialized to a temp
/// copy, returning through the `probe_only` arm on the loop's FIRST iteration.
/// **This is the corpus's branch**: `run_m1_diag` drives every one of the 20
/// programs through the same path. The string-entry branch
/// (`materialize_single_file`) is not exercised here and is not what the
/// transfer measures.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** delete
/// `facts.first_diags = diagnosis.diags.clone()` from the `probe_only` block —
/// reproducing the regression exactly — and this fails on an empty set.
#[test]
fn diagnose_once_returns_the_captured_diagnostics_not_an_empty_set() {
    let fixture = Fixture::new(&[
        (
            "lib.rs",
            "#![allow(dead_code, unused_unsafe)]\npub mod m;\n",
        ),
        (
            "m.rs",
            "pub unsafe fn preexisting(v: &i32) {\n    *(v as *const i32 as *mut i32) = 7;\n}\npub unsafe fn bump(p: *mut i32) -> i32 {\n    *p += 1;\n    *p\n}\n",
        ),
    ]);

    let (observed_root, diags) = super::diagnose_once(&fixture.root()).expect("the probe ran");

    assert!(
        !diags.is_empty(),
        "the probe returned an empty capture for a fixture with a known \
         diagnostic — this is the zeroed payload wearing an ok status, and it \
         is what `run_m1_diag` reported for all 20 programs"
    );
    assert!(
        diags.iter().any(|d| d.line > 0 && !d.file.is_empty()),
        "the payload carries no located diagnostic, so the transfer would have \
         nothing to compare: {diags:?}"
    );
    // The FRAME must fit the payload. A root that does not canonicalize its own
    // diagnostics is worse than no root: every path would key as itself and the
    // transfer would compare absolute paths while believing it compared
    // relative ones.
    assert!(
        diags.iter().any(|d| {
            let relative = verify::crate_relative(&d.file, &observed_root);
            relative != d.file && !relative.starts_with('/')
        }),
        "no diagnostic is under the observed root {observed_root:?}, so the \
         frame does not describe the capture: {diags:?}"
    );
}

/// **S2b.1 — a BASELINE-MASKED error must not gate.**
///
/// The fixture denies `unused_variables`, so its UNMODIFIED source already
/// reports an error-level diagnostic. The rewrite does not add one, so the crate
/// must still emit — brotli's shape in miniature, where an absolute gate made
/// even revert-all unsatisfiable.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** gate on the absolute
/// count (`diagnosis.errors == 0`) instead of the differential and this fails.
#[test]
fn a_baseline_error_does_not_gate_the_rewrite() {
    // Mirrors brotli's ACTUAL baseline diagnostic: `invalid_reference_casting`
    // is deny-by-default and, unlike a crate-level `#![deny(..)]`, does not
    // abort the decision-phase compile — which is why brotli decides 126
    // subjects and only fails at verify.
    let fixture = Fixture::new(&[
        (
            "lib.rs",
            "#![allow(dead_code, unused_unsafe)]\npub mod m;\n",
        ),
        (
            "m.rs",
            "pub unsafe fn preexisting(v: &i32) {\n    *(v as *const i32 as *mut i32) = 7;\n}\npub unsafe fn bump(p: *mut i32) -> i32 {\n    *p += 1;\n    *p\n}\n",
        ),
    ]);
    match super::rewrite_m1_path(&fixture.root()) {
        super::RewriteOutcome::Emitted {
            files,
            bisect_probes,
            escalated,
            ..
        } => {
            let text = text_for_any(&files).expect("something was emitted");
            assert!(
                text.contains("p: &mut i32"),
                "the rewrite was withheld because of a pre-existing error: {text}"
            );
            // It must emit on the LOOP's clean exit, not be recovered by bisect.
            // The differential lives at three sites (loop exit, bisect probe,
            // final guard); without pinning the path, mutating one leaves the
            // fixture recoverable by the others and the witness survives.
            assert_eq!(
                bisect_probes, 0,
                "the baseline error forced an escalation instead of being masked"
            );
            assert!(
                escalated.is_none(),
                "escalated on a baseline-masked error: {escalated:?}"
            );
        }
        super::RewriteOutcome::Degraded { reason, .. } => panic!(
            "a pre-existing baseline error gated the rewrite — the absolute-gate \
             failure mode that made brotli's base case unsatisfiable: {reason}"
        ),
    }
}

fn text_for_any(files: &BTreeMap<FileKey, String>) -> Option<String> {
    files.values().next().cloned()
}

/// **S2b.1 — a NEW error of a MASKED class must still gate.**
///
/// Multiset semantics, witnessed directly: one occurrence of a key is masked by
/// a baseline of one; a SECOND occurrence is novel. Without this the gate would
/// go blind to rewrite-introduced violations of exactly the class it masks,
/// which for the real corpus is reference casting.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** compare presence rather
/// than count in `Baseline::novel` and this fails — the repeat is masked.
#[test]
fn a_repeat_of_a_masked_class_is_still_novel() {
    let root = std::path::Path::new("/p/crate");
    let diag = |line: usize| verify::Diag {
        file: "/p/crate/src/x.rs".to_owned(),
        line,
        column: 1,
        end_line: line,
        end_column: 1,
        message: "reference casting".to_owned(),
        direction: verify::Direction::Other,
        code: None,
        related: Vec::new(),
    };
    let baseline = verify::Baseline {
        keys: std::iter::once((verify::baseline_key(&diag(1), root), 1)).collect(),
        errors: 1,
        messages_embedding_root: 0,
    };

    // One occurrence: masked — and at a DIFFERENT line, so the key is stable
    // under the line drift every edit above it causes.
    assert!(
        baseline.novel(&[diag(42)], root).is_empty(),
        "a baseline error moved by an edit was reported as novel"
    );
    // Two occurrences: the second is novel.
    let pair = [diag(42), diag(99)];
    let novel = baseline.novel(&pair, root);
    assert_eq!(
        novel.len(),
        1,
        "a rewrite-introduced repeat of a masked class was masked too"
    );
    assert_eq!(novel[0].line, 99);
}

// ---------------------------------------------------------------------------
// F.1 — the canonicalizer's KEY AGREEMENT. Rider 7: each fixture names the
// branch it exercises, and the corpus branch is covered.
// ---------------------------------------------------------------------------

/// **W1 — the two sides key the same logical file identically.**
///
/// **Rider 7 branch: UNDER-ROOT — the branch the corpus takes.** The roots are
/// deliberately CORPUS-SHAPED: one carries `rs-crown` as a path component, the
/// other a `crat-verify`-style temp name. With neutral roots a resurrected
/// string special case would take its magic branch on neither side and this
/// witness would pass while the resurrection survived.
///
/// *Mutation-tested, Rider 0 order.* **Deletions, each must fail:**
/// (i) reintroduce a basename normalization on one side;
/// (ii) reintroduce the `/rs-crown/` split.
#[test]
fn both_sides_key_the_same_file_identically() {
    let original_root = std::path::Path::new("/home/u/dev/benchmarks/rs-crown/brotli");
    let observed_root = std::path::Path::new("/var/folders/T/crat-verify-4242-0");

    let key_of = |path: &str, root: &std::path::Path| {
        verify::baseline_key(
            &verify::Diag {
                file: path.to_owned(),
                line: 1,
                column: 1,
                end_line: 1,
                end_column: 1,
                message: "same message".to_owned(),
                direction: verify::Direction::Other,
                code: None,
                related: Vec::new(),
            },
            root,
        )
    };

    let baseline = key_of(
        "/home/u/dev/benchmarks/rs-crown/brotli/src/enc/encode.rs",
        original_root,
    );
    let observed = key_of(
        "/var/folders/T/crat-verify-4242-0/src/enc/encode.rs",
        observed_root,
    );
    assert_eq!(
        baseline, observed,
        "the two sides key the same file differently — the baseline masks \
         nothing and the gate silently no-ops on the corpus"
    );
    assert_eq!(
        baseline.0, "src/enc/encode.rs",
        "key is relative to the crate root"
    );
}

/// **W2 — a path NOT under the given root keys as ITSELF.**
///
/// **Rider 7 branch: FALLBACK.** Never a basename: basenames merge distinct
/// files into one key, so a novel error in `a/x.rs` could read as the baseline
/// of `b/x.rs` and the gate would fail OPEN.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** restore a basename
/// fallback and this fails.
#[test]
fn a_path_outside_the_crate_root_keys_as_itself() {
    let root = std::path::Path::new("/home/u/dev/benchmarks/rs-crown/brotli");
    let outside = "/somewhere/else/src/enc/encode.rs";
    assert_eq!(
        verify::crate_relative(outside, root),
        outside,
        "a path outside the root was rewritten — a basename here would merge \
         distinct files into one key"
    );
    // And two distinct files sharing a basename must NOT collide.
    assert_ne!(
        verify::crate_relative("/p/a/x.rs", root),
        verify::crate_relative("/p/b/x.rs", root),
        "distinct files collapsed to one key"
    );
}

/// **S2b.2 repair-2 — gate machinery does not run on instrument paths.**
///
/// `baseline_of` COMPILES the unmodified crate. Probe mode returns before
/// `novel` is ever consulted, so on that path the compile is dead work — and
/// not harmlessly: its diagnostics are forwarded to the SAME stderr the
/// validation transfer parses as its rendered side, which put four
/// frozen-tree entries against a structural side that measures the temp copy.
///
/// # What this asserts, and what it does not
///
/// The stderr contamination is not observable in-process — the emitter writes
/// to the process's own stderr, not to anything a test can capture. So this
/// pins the CAUSE rather than the symptom: no baseline is computed at all on
/// the probe path. That implies the absence of leakage (a compile that does
/// not run emits nothing) and is strictly narrower than "only-rendered is
/// empty", which the corpus transfer checks end-to-end. Stated rather than
/// substituted silently.
///
/// **Rider 7 branch: the PROBE path on a baseline-dirty input — brotli's
/// shape**, nested two components below the root so the gate path genuinely
/// has a baseline to find.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** restore the
/// unconditional `baseline_of` above the `probe_only` return — in the shape it
/// actually had, feeding the `OutcomeFacts` literal — and this fails.
///
/// **A residual, measured rather than assumed.** A first mutation that computed
/// the baseline eagerly but left the counters assigned below the return
/// **survived**: the assertion reads the reported counters, so it detects "a
/// baseline reached the outcome", not "a compile executed". A compile whose
/// result is discarded would evade it and still contaminate stderr. Catching
/// that needs an execution counter — a test-only seam in shipping code, which
/// this track has ruled against where a data-level route exists; here there is
/// no data-level route, so the residual is stated and left to the corpus
/// transfer, which observes the stderr end-to-end.
///
/// **That coverage is compelled, not hoped for.** Under the staleness rule, a
/// change touching the probe or baseline path makes every prior transfer result
/// stale, so the transfer must be re-run before its numbers are cited again —
/// which is exactly the change class that could reintroduce a discarded
/// compile. The residual is therefore a MANAGED one: the only edits that can
/// open it are the edits that force the run that would close it.
#[test]
fn a_probe_does_not_compile_the_baseline_it_never_consults() {
    let fixture = Fixture::new(&[
        (
            "lib.rs",
            "#![allow(dead_code, unused_unsafe)]\npub mod deep;\n",
        ),
        ("deep.rs", "pub mod inner;\n"),
        (
            "deep/inner.rs",
            "pub unsafe fn preexisting(v: &i32) {\n    *(v as *const i32 as *mut i32) = 7;\n}\npub unsafe fn bump(p: *mut i32) -> i32 {\n    *p += 1;\n    *p\n}\n",
        ),
    ]);

    // NON-VACUITY CONTROL, first: the GATE path on this same fixture must see a
    // real baseline. Without it, a fixture that simply has no baseline would
    // satisfy the probe assertion below and the witness would pin nothing.
    let gate_baseline_errors = match super::rewrite_m1_path(&fixture.root()) {
        super::RewriteOutcome::Emitted {
            baseline_errors, ..
        } => baseline_errors,
        super::RewriteOutcome::Degraded {
            baseline_errors, ..
        } => baseline_errors,
    };
    assert!(
        gate_baseline_errors > 0,
        "the fixture is not baseline-dirty, so the probe assertion below would \
         hold vacuously"
    );

    // THE PROBE, on the same input: no baseline is computed at all.
    let probe = super::rewrite_core_injected(
        ::utils::compilation::path_to_input(&fixture.root()),
        Some(&fixture.root()),
        super::MAX_REVERT_ROUNDS,
        &|_| {},
        true,
        false,
        false,
        None,
    );
    match probe {
        super::RewriteOutcome::Degraded {
            baseline_keys,
            baseline_errors,
            ..
        } => {
            assert_eq!(
                (baseline_keys, baseline_errors),
                (0, 0),
                "probe mode compiled a baseline it returns before consulting. \
                 That compile's diagnostics reach the SAME stderr an \
                 instrument's consumer parses, which is how four frozen-tree \
                 entries appeared on the rendered side of a transfer that \
                 measures the temp copy"
            );
        }
        super::RewriteOutcome::Emitted { .. } => {
            panic!("probe mode returns before emission and cannot report Emitted")
        }
    }
}

/// **F.2 — the differential gate, END-TO-END on a NESTED crate.**
///
/// **Rider 7 branch: UNDER-ROOT — the branch the corpus takes.** The subject
/// lives at `deep/inner.rs`, two components below the crate root, so no basename
/// accident can make the two sides agree: the flat fixture keyed `m.rs` on both
/// sides even while the canonicalizer was broken, which is exactly how the
/// corpus defect survived its own witness.
///
/// The baseline dirt is `invalid_reference_casting` — brotli's real class,
/// deny-by-default at verify and harmless to the decision phase.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** gate on the absolute
/// count instead of the differential and this fails.
#[test]
fn a_nested_crate_masks_its_baseline_and_still_emits() {
    let fixture = Fixture::new(&[
        (
            "lib.rs",
            "#![allow(dead_code, unused_unsafe)]\npub mod deep;\n",
        ),
        ("deep.rs", "pub mod inner;\n"),
        (
            "deep/inner.rs",
            "pub unsafe fn preexisting(v: &i32) {\n    *(v as *const i32 as *mut i32) = 7;\n}\npub unsafe fn bump(p: *mut i32) -> i32 {\n    *p += 1;\n    *p\n}\n",
        ),
    ]);

    match super::rewrite_m1_path(&fixture.root()) {
        super::RewriteOutcome::Emitted {
            files,
            bisect_probes,
            escalated,
            ..
        } => {
            let nested = files
                .iter()
                .find(|(k, _)| format!("{k:?}").contains("inner.rs"))
                .map(|(_, text)| text.clone())
                .expect("the nested module was emitted");
            assert!(
                nested.contains("p: &mut i32"),
                "the rewrite was withheld by the nested crate's baseline: {nested}"
            );
            // PATH-PINNED, as in the flat witness: it must emit on the loop's
            // clean exit, not be recovered by bisect.
            assert_eq!(
                bisect_probes, 0,
                "the nested baseline forced an escalation instead of being masked"
            );
            assert!(escalated.is_none(), "escalated: {escalated:?}");
        }
        super::RewriteOutcome::Degraded { reason, .. } => panic!(
            "a nested crate's baseline gated its rewrite — the corpus shape, \
             which the flat fixture could not detect: {reason}"
        ),
    }
}

/// **S2b.3 Item 0 — `unplaceable` SURVIVES A `Degraded` OUTCOME.**
///
/// Two pre-existing facts, which until S2b.3 could not both be observed: a
/// macro-generated declaration has no spliceable range and is recorded as
/// `Unplaceable`, and probe mode returns `Degraded` before the gate. The second
/// discarded the first — `RewriteOutcome::Degraded` had no field to carry it,
/// so `OutcomeFacts::degraded` dropped it and `run_m1_emit`'s FAIL arm wrote a
/// literal `0usize` in its place.
///
/// The fixture is the one from
/// `a_macro_generated_declaration_is_recorded_as_unplaceable`, but driven
/// through the **full pipeline** rather than `emit_files` alone. That
/// reachability was checked before this witness was written, per the ruling that
/// a fixture which does not produce a nonzero count through the shipping
/// pipeline is a finding to report and not a fixture to force.
///
/// The `> 0` assertion is a NON-VACUITY guard, not decoration: a zero would mean
/// the fixture had stopped producing an `Unplaceable` at all, at which point the
/// equality below would hold for the wrong reason.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** remove
/// `unplaceable: self.unplaceable` from `OutcomeFacts::degraded` — the variant
/// then has an unfilled field and the BUILD fails, which is the strongest form
/// this witness can take. Deletion cannot produce a running-but-wrong binary
/// here, so the semantically faithful mutation follows it: `Vec::new()` in that
/// same position restores the original defect exactly, and this test fails on
/// the count.
#[test]
fn a_degraded_outcome_still_reports_its_unplaceable_decisions() {
    let fixture = Fixture::new(&[(
        "lib.rs",
        "#![allow(dead_code, unused_unsafe)]\nmacro_rules! mk {\n    () => {\n        pub unsafe fn mac_bump(p: *mut i32) -> i32 {\n            *p += 1;\n            *p\n        }\n    };\n}\nmk!();\n",
    )]);

    // The reference value, from the phase that produces it.
    let planned = emit(&fixture).unplaceable;
    assert!(
        !planned.is_empty(),
        "the fixture no longer yields an Unplaceable, so this witness would \
         pass on a zero == zero comparison"
    );

    let probe = super::rewrite_core_injected(
        ::utils::compilation::path_to_input(&fixture.root()),
        Some(&fixture.root()),
        super::MAX_REVERT_ROUNDS,
        &|_| {},
        true,
        false,
        false,
        None,
    );
    match probe {
        super::RewriteOutcome::Degraded { unplaceable, .. } => {
            assert_eq!(
                unplaceable.len(),
                planned.len(),
                "the Degraded arm lost the plan's unplaceable decisions — the \
                 shape that made every FAIL row's count a constant"
            );
            assert_eq!(
                unplaceable[0].reason, planned[0].reason,
                "the count survived but the attribution did not"
            );
        }
        super::RewriteOutcome::Emitted { .. } => {
            panic!("probe mode returns before emission and cannot report Emitted")
        }
    }
}

/// **S2b.3 Item 1 — `emitted` COUNTS PLACEMENTS, NOT DECISIONS.**
///
/// The reported `emitted` was `DecisionTable::emitted_count()`, a count of `Ref`
/// decisions. A decision `plan` cannot place produces no edit, so the two
/// numbers differ by exactly the unplaceable set and the source is unchanged in
/// that difference. Corpus exposure is zero, which is *why* this is fixed at the
/// derivation: a counter right by measurement is one corpus change from wrong,
/// and it would present as a yield figure rather than as a failure.
///
/// The macro fixture is the discriminating case — its single subject IS a `Ref`
/// decision (the non-`Ref` arm returns before the span is ever located), so the
/// old derivation reports **1** for a run that edited nothing.
///
/// The emptiness assertions are the anchor: they are what make `0` the RIGHT
/// answer rather than merely the expected one.
///
/// # Both arms, because the count reaches them by different routes
///
/// On a success path `facts.emitted_count` is **overwritten** by `kept.len()`,
/// which derives from the already-filtered `emitted_subjects`. The value built
/// at the tuple site therefore survives only on a `Degraded` return — the FAIL
/// rows. A witness on the emitting arm alone leaves the tuple site uncovered,
/// and the fix would be half-applied: placement-true on PASS rows and
/// decision-shaped on FAIL rows, the same arm asymmetry Item 0 repaired one
/// field over. So this drives the same fixture down both routes.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** delete the
/// `unplaceable_subjects.contains(..)` skip in `rewrite_core_injected` and this
/// fails 1 vs 0 on the emitting leg. Second: put the decision count back at
/// the tuple site — `entries.iter().filter(|(_, d)| matches!(d, Decision::Ref { .. })).count()` — **this SURVIVED the emitting leg alone**, which is how the
/// second route was found; it fails the probe leg below.
#[test]
fn emitted_counts_placements_not_ref_decisions() {
    let fixture = Fixture::new(&[(
        "lib.rs",
        "#![allow(dead_code, unused_unsafe)]\nmacro_rules! mk {\n    () => {\n        pub unsafe fn mac_bump(p: *mut i32) -> i32 {\n            *p += 1;\n            *p\n        }\n    };\n}\nmk!();\n",
    )]);

    // NON-VACUITY: the subject must reach `plan` as a `Ref` decision and fail to
    // place. A fixture that degraded it earlier would satisfy the count below
    // for a reason that has nothing to do with placement.
    let planned = emit(&fixture);
    assert_eq!(
        planned.unplaceable.len(),
        1,
        "the fixture stopped producing an unplaceable Ref decision, so the \
         count below no longer discriminates: {:?}",
        planned.unplaceable
    );

    match super::rewrite_m1_path(&fixture.root()) {
        super::RewriteOutcome::Emitted {
            emitted_count,
            files,
            files_touched,
            unplaceable,
            ..
        } => {
            assert_eq!(
                files_touched, 0,
                "an unplaceable required site holds its whole signature class"
            );
            let original = std::fs::read_to_string(fixture.root()).expect("fixture source");
            assert!(
                files.values().all(|text| text == &original),
                "a held class may ride the seeded AST map but its bytes must be unchanged"
            );
            assert_eq!(unplaceable.len(), 1, "{unplaceable:?}");
            assert_eq!(
                emitted_count, 0,
                "a decision that produced no edit was counted as emitted — \
                 `emitted` is still decision-shaped"
            );
        }
        super::RewriteOutcome::Degraded { reason, .. } => {
            panic!("an unplaceable-only crate emits nothing and still passes: {reason}")
        }
    }
}

/// **S2b.3 Item 1, second leg — the `Degraded` arm's `emitted_count`.**
///
/// See `emitted_counts_placements_not_ref_decisions` for why this is a separate
/// route rather than a second assertion: the success paths overwrite
/// `facts.emitted_count` with `kept.len()`, so only a non-emitting return
/// reports the value the tuple site built. Probe mode is the reachable
/// non-emitting return that does not require manufacturing a gate failure.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** the tuple site's
/// `emitted_subjects.len()` has no deletion that compiles, so the faithful
/// mutation is the original expression — put the decision count back,
/// `entries.iter().filter(|(_, d)| matches!(d, Decision::Ref { .. })).count()`, and this fails 1 vs 0. That mutation SURVIVES the emitting leg, which is exactly
/// why this leg exists.
#[test]
fn a_degraded_outcome_reports_placements_too() {
    let fixture = Fixture::new(&[(
        "lib.rs",
        "#![allow(dead_code, unused_unsafe)]\nmacro_rules! mk {\n    () => {\n        pub unsafe fn mac_bump(p: *mut i32) -> i32 {\n            *p += 1;\n            *p\n        }\n    };\n}\nmk!();\n",
    )]);
    // NON-VACUITY, as on the emitting leg: one unplaceable `Ref` decision, or
    // the zero below means nothing.
    assert_eq!(emit(&fixture).unplaceable.len(), 1);

    let probe = super::rewrite_core_injected(
        ::utils::compilation::path_to_input(&fixture.root()),
        Some(&fixture.root()),
        super::MAX_REVERT_ROUNDS,
        &|_| {},
        true,
        false,
        false,
        None,
    );
    match probe {
        super::RewriteOutcome::Degraded { emitted_count, .. } => assert_eq!(
            emitted_count, 0,
            "the non-emitting arm still reports Ref DECISIONS — placement-truth \
             stopped at the success paths"
        ),
        super::RewriteOutcome::Emitted { .. } => {
            panic!("probe mode returns before emission and cannot report Emitted")
        }
    }
}

/// **S3.0′ + wave 3 — same-named subjects stay distinct inside one atomic class.**
///
/// `mixed` has two anonymous pointer parameters, so both carry
/// `param_name: None`. Both reach `Decision::Ref` (measured, not assumed), and
/// the second one's type comes from a macro, so its span cannot be spliced and
/// `plan` records it as unplaceable. That is the shape a name-keyed identity
/// cannot represent: both parameters render `mixed::<unnamed>`, the driver's
/// unplaceable subtraction matches the FIRST one against the SECOND one's
/// record, and skips a placement that actually happened.
///
/// Measured at `ebeb99fd`, before the key was repaired: `emitted_count == 0`
/// while the emitted source read `fn mixed(_: &i32, _: ty2!())` — the rewrite is
/// right there in the output — and the ratified identity
/// `emitted + degraded + unplaceable == rows` failed `0 + 0 + 1 != 2`.
///
/// **Reachability (Rider 5) is shown, not asserted:** the assertion below is on
/// `emitted_count`, the driver's real counter, reached through `rewrite_m1` —
/// the same path the corpus sweep uses. The corpus has never exposed this only
/// because `unplaceable == 0` there, so the `contains` check never matches.
///
/// Wave 3 changes the terminal outcome: the unplaceable second parameter holds
/// the whole function-signature class, so the first parameter is now a typed
/// class-held degradation rather than a partial emission.
#[test]
fn two_subjects_with_the_same_rendered_name_stay_distinct() {
    let src = "#![allow(dead_code, unused_unsafe)]\nmacro_rules! ty2 { () => { *mut i32 } }\npub unsafe fn mixed(_: *mut i32, _: ty2!()) -> i32 { 0 }\n";
    let super::RewriteOutcome::Emitted {
        emitted_count,
        unplaceable,
        degradations,
        source,
        ..
    } = super::rewrite_m1(src)
    else {
        panic!("fixture must emit");
    };

    assert_eq!(
        unplaceable.len(),
        1,
        "the macro-typed parameter is the unplaceable one: {unplaceable:?}"
    );
    assert_eq!(
        emitted_count, 0,
        "an unplaceable required site must prevent partial signature emission"
    );
    assert!(
        !source.contains("_: &i32"),
        "the sibling parameter was partially emitted despite the class hold:\n{source}"
    );
    assert!(degradations.iter().any(|record| matches!(
        record.reason,
        super::decision::DegradeReason::SignatureClassHeld { .. }
    )));
    // The identity the corpus pin enforces, on the fixture that breaks it.
    assert_eq!(
        emitted_count + degradations.len() + unplaceable.len(),
        2,
        "emitted + degraded + unplaceable == rows, over 2 subjects"
    );
}

// ---------------------------------------------------------------------------
// S3.1 A-side — the locals subject universe
// ---------------------------------------------------------------------------

/// Decision-table rows for a fixture, as `(mir_local, name, reason)`.
fn locals_of(src: &str) -> Vec<(u32, Option<String>, String)> {
    let fixture = Fixture::new(&[("lib.rs", src)]);
    ::utils::compilation::run_compiler_on_path(&fixture.0.join("lib.rs"), |tcx| {
        let table = super::decide_table(tcx).expect("fixture yields a decision table");
        let rows = super::artifact::rows(tcx, &table);
        rows.iter()
            .filter(|r| r.arg_index.is_none())
            .map(|r| {
                (
                    r.mir_local,
                    r.param_name.clone(),
                    r.degrade_reason
                        .clone()
                        .unwrap_or_else(|| "<emitted>".to_owned()),
                )
            })
            .collect::<Vec<_>>()
    })
    .expect("fixture compiles")
}

const MALLOC: &str = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, unused_assignments)]\nextern \"C\" { fn malloc(size: usize) -> *mut core::ffi::c_void; }\n";

/// **A named pointer local is a subject; a MIR temporary is not.**
///
/// Both halves in one witness because they share a fixture and the interesting
/// property is the BOUNDARY between them: `p` is a named binding and becomes a
/// subject, while the `*mut c_void` the `malloc` call lands in is a depth-1
/// pointer with no debug entry and must not. Depth alone would admit it.
///
/// *Mutation-tested (Rider 0, deletion first):* deleting the locals range from
/// `collect_local_subjects` yields zero rows; deleting the entry-count guard
/// admits the temporary.
#[test]
fn a_named_pointer_local_is_a_subject_and_a_temporary_is_not() {
    let got = locals_of(&format!(
        "{MALLOC}pub unsafe fn f() -> i32 {{ let p: *mut i32 = malloc(4) as *mut i32; *p = 1; *p }}\n"
    ));
    assert_eq!(
        got.iter()
            .map(|(l, n, _)| (*l, n.as_deref()))
            .collect::<Vec<_>>(),
        // `_1`, not `_2`: this fn has no parameters, so `arg_count == 0` and the
        // locals range opens at `_1`. The malloc temporary is absent because it
        // carries no debug entry, which is the half of this witness that depth
        // alone would get wrong.
        vec![(1, Some("p"))],
        "exactly the named local, and no temporary: {got:?}"
    );
}

/// **Two shadowing locals are two subjects.** Name is not a key.
///
/// *Mutation-tested:* keying the universe by name collapses these to one row.
#[test]
fn two_shadowing_locals_are_two_subjects() {
    let got = locals_of(&format!(
        "{MALLOC}pub unsafe fn f() -> i32 {{ let p: *mut i32 = malloc(4) as *mut i32; *p = 1; \
         let p: *mut i32 = malloc(4) as *mut i32; *p = 2; *p }}\n"
    ));
    let names: Vec<_> = got.iter().map(|(_, n, _)| n.as_deref()).collect();
    assert_eq!(got.len(), 2, "two distinct locals, both named p: {got:?}");
    assert_eq!(names, vec![Some("p"), Some("p")]);
    assert_ne!(got[0].0, got[1].0, "distinct mir_locals: {got:?}");
}

/// **An unannotated pointer local degrades with the reason of the gate that
/// actually stops it**, and carries no `arg_index`.
///
/// The dominant corpus shape: **1,196 of 1,710** locals on the substrate of
/// record are C2Rust bindings with no declared type (raw-form era: 2,628 of
/// 3,142 — `preprocess` removed the `fresh_N` temporaries, not the class).
///
/// **Amended by the dissolution (2026-08-12).** Every vintage before it
/// asserted `no-declared-type` here: one reason over the whole 1,196, naming
/// the rewriter's splice mechanism rather than anything about the subject. The
/// ladder now speaks, and on this fixture — a leaked `malloc` result — it says
/// `kind-raw`, a fact about the program. Corpus-wide the same move accounts for
/// 475 of the 1,196.
///
/// *Mutation-tested:* restoring the `ty_span.is_none()` early return in
/// `decide_one_ladder` puts a residual key back here.
#[test]
fn an_unannotated_pointer_local_degrades_with_the_gate_that_stops_it() {
    let got = locals_of(&format!(
        "{MALLOC}pub unsafe fn f() -> i32 {{ let p = malloc(4) as *mut i32; *p = 1; *p }}\n"
    ));
    assert_eq!(got.len(), 1, "{got:?}");
    assert_eq!(got[0].2, "kind-raw", "{got:?}");
}

/// **An unannotated local that is ALREADY a reference says so** — the
/// dissolution's largest single discovery, and the one that kept the ruling's
/// STOP from firing.
///
/// `let ref mut x = place;` is C2Rust's temporary idiom and it binds `&mut T`.
/// **51 of the 52 `index-addr` subjects on the corpus are this shape**, and
/// every vintage before the dissolution reported them `no-declared-type` — a
/// claim about the rewriter's splice mechanism, applied to subjects that need
/// no rewrite at all because they are already the target form.
///
/// The shape is read from the RESOLVED type, not from the construction class:
/// 51-of-52 is a correlation, and `ty.kind()` is the fact. `unsupported-decl-shape`
/// is the existing key that carries exactly this claim — its own doc says *"or
/// a parameter that is already a reference"* — so nothing was coined for them.
///
/// **The SHAPE is asserted, not just the key**, and that is load-bearing:
/// `DeclShape::Other` fails the `!= RawPtr` test too, so a mutation restoring
/// `Other` reports the same key and a key-only assertion passes it. Measured,
/// not reasoned — the first version of this witness was written key-only and
/// its mutation came back GREEN.
///
/// *Mutation-tested:* restoring `DeclShape::Other` in the collector's
/// resolved-type fallback fails on the shape column.
#[test]
fn an_unannotated_local_that_is_already_a_reference_reports_its_shape() {
    let rows = artifact_rows_of(
        "#![allow(dead_code, unused_unsafe, unused_variables)]\n\
         pub struct S { pub a: [u32; 4] }\n\
         pub unsafe fn f(s: *mut S) {\n\
         \x20   let ref mut fresh0 = (*s).a[1];\n\
         \x20   *fresh0 |= 1;\n\
         }\n",
    );
    let fresh: Vec<_> = rows
        .iter()
        .filter(|r| r.param_name.as_deref() == Some("fresh0"))
        .collect();
    assert_eq!(fresh.len(), 1, "{rows:?}");
    assert_eq!(
        fresh[0].degrade_reason.as_deref(),
        Some("unsupported-decl-shape"),
        "{rows:?}"
    );
    assert_eq!(
        fresh[0].decl_shape,
        Some(crate::coverage_recon::schema::DeclShape::Reference),
        "the shape must come from the RESOLVED type — this subject is already \
         `&mut T` and reporting `other` for it is the pre-dissolution claim \
         wearing a new name: {rows:?}"
    );
}

/// **THE TERMINAL VETO: a subject with no splice target cannot emit**, whatever
/// form the ladder selected for it.
///
/// This is what makes the dissolution's ledger invariance STRUCTURAL rather
/// than measured. Today no real subject reaches an emitting `Slice` or `Opt`
/// without a `ty_span` — a parameter always has one, and a local is stopped by
/// `slice-local-construction` / `opt-local-construction` first — so the veto is
/// corpus-unreachable and this is the ONLY thing that can ever fail for it.
///
/// The fixture is a slice-emitting PARAMETER, chosen because a parameter walks
/// past both local-construction gates and reaches `Decision::Slice`; erasing
/// its `ty_span` at the phase boundary is then the exact state the veto exists
/// for. `ctor` is `None` for a parameter, so the residual fold is
/// `copy-source-coupled` — the no-recognized-initializer arm.
///
/// *Mutation-tested:* deleting the veto in `decide_one` emits this subject
/// (`<emitted>`), which is the ledger movement it exists to make impossible.
#[test]
fn a_subject_with_no_splice_target_cannot_emit_whatever_form_was_selected() {
    let src = "#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments)]\n\
               pub unsafe fn fill(p: *mut i32, len: usize) {\n\
               \x20   let mut i: usize = 0;\n\
               \x20   while i < len { *p.offset(i as isize) = i as i32; i += 1; }\n\
               }\n";
    let fixture = Fixture::new(&[("lib.rs", src)]);
    let (baseline, erased) =
        ::utils::compilation::run_compiler_on_path(&fixture.0.join("lib.rs"), |tcx| {
            let base = super::artifact::rows(tcx, &super::decide_table(tcx).expect("table"));
            let erased = super::decisions_with_ty_span_erased(tcx).expect("perturbed table");
            (base, erased)
        })
        .expect("fixture compiles");

    let reason = |rows: &[crate::coverage_recon::schema::Row]| {
        rows.iter()
            .find(|r| r.param_name.as_deref() == Some("p"))
            .map(|r| {
                r.degrade_reason
                    .clone()
                    .unwrap_or_else(|| "<emitted>".to_owned())
            })
            .expect("subject p present")
    };
    // The baseline is the load-bearing half: without it, a veto that vetoed
    // nothing would pass this test exactly as well, because the subject would
    // read `slice-*` in both columns.
    assert_eq!(
        reason(&baseline),
        "<emitted>",
        "the fixture must EMIT unperturbed, or the veto below is vetoing a \
         subject that was already degraded"
    );
    assert_eq!(
        reason(&erased),
        "copy-source-coupled",
        "a subject whose declared type was erased reached an emitting form and \
         the terminal veto did not stop it — the plan phase would splice at a \
         span that does not exist"
    );
}

/// **A locals row carries `arg_index: None`** — *not a parameter*, never
/// *unpaired* — while the parameter beside it keeps its 1-based index.
///
/// *Mutation-tested:* removing the `SubjectKind::Local => None` arm in
/// `artifact::rows` is a compile error; returning `Some(0)` fails this.
#[test]
fn a_locals_row_carries_no_arg_index_while_a_parameter_keeps_one() {
    let src = format!(
        "{MALLOC}pub unsafe fn f(q: *mut i32) -> i32 {{ let p: *mut i32 = malloc(4) as *mut i32; *p = 1; *p + *q }}\n"
    );
    let fixture = Fixture::new(&[("lib.rs", &src)]);
    let pairs = ::utils::compilation::run_compiler_on_path(&fixture.0.join("lib.rs"), |tcx| {
        let table = super::decide_table(tcx).expect("table");
        super::artifact::rows(tcx, &table)
            .iter()
            .map(|r| (r.mir_local, r.arg_index))
            .collect::<Vec<_>>()
    })
    .expect("compiles");
    assert!(
        pairs.contains(&(1, Some(1))),
        "the parameter keeps its index: {pairs:?}"
    );
    assert!(
        pairs.contains(&(2, None)),
        "the local carries None: {pairs:?}"
    );
}

// ---------------------------------------------------------------------------
// S3.1′ — the A1 emitability gates over the LOCALS population
// ---------------------------------------------------------------------------

/// Every subject's `(name, is_param, reason)` — parameters included.
///
/// A sibling of [`locals_of`] rather than a widening of it: `locals_of` is the
/// instrument the S3.1 witnesses above are written against, and changing what
/// it returns would put those tests under Rider 4 for no gain here.
fn artifact_rows_of(src: &str) -> Vec<crate::coverage_recon::schema::Row> {
    let fixture = Fixture::new(&[("lib.rs", src)]);
    ::utils::compilation::run_compiler_on_path(&fixture.0.join("lib.rs"), |tcx| {
        let table = super::decide_table(tcx).expect("fixture yields a decision table");
        super::artifact::rows(tcx, &table)
    })
    .expect("fixture compiles")
}

fn decisions_of(src: &str) -> Vec<(String, bool, String)> {
    artifact_rows_of(src)
        .iter()
        .map(|r| {
            (
                r.param_name
                    .clone()
                    .unwrap_or_else(|| "<unnamed>".to_owned()),
                r.arg_index.is_some(),
                r.degrade_reason
                    .clone()
                    .unwrap_or_else(|| "<emitted>".to_owned()),
            )
        })
        .collect()
}

fn reason_of(got: &[(String, bool, String)], name: &str, is_param: bool) -> String {
    got.iter()
        .find(|(n, p, _)| n == name && *p == is_param)
        .unwrap_or_else(|| panic!("no subject {name} (param={is_param}): {got:?}"))
        .2
        .clone()
}

/// **A raw-only method call on a LOCAL degrades it** — gate one, over the
/// population that had it dead.
///
/// The subject must survive shape *and* kind to reach A1 at all, so `p` is a
/// copy of a parameter (BO calls it `Ref`) rather than a `malloc` result (BO
/// would call that `Owning` or `Raw` and degrade it earlier). **A fixture that
/// degrades upstream witnesses nothing**, which is why this shape was measured
/// against the pre-repair build first: `p` came back `ref-shared`, so it
/// genuinely reached the gate and was waved through.
///
/// **Fixture op changed at S3.2′-2, deliberately.** It was `*p.offset(1)`.
/// `offset` is now a slice-ARITHMETIC op, so an arithmetic use on a local takes
/// the new `slice-local-construction` arm and this test would have been
/// asserting the wrong gate. `is_null` is a raw-only use that is *not*
/// arithmetic, so the fixture again exercises exactly the gate the test names.
/// The arithmetic case is not lost — it has its own witness below.
///
/// *Mutation-tested (Rider 0, deletion first), with the claim CORRECTED after
/// measurement:* deleting the `binding_hir` insert does **not** restore
/// `ref-shared` — an earlier draft of this comment said it would. With the map
/// empty the attribution lookup finds nothing and the collector **panics** by
/// design, naming the local and its span. Killed, but through the contradiction
/// arm rather than through this assertion.
///
/// The mutation that reproduces the ORIGINAL defect is restoring
/// `hir_id: rustc_hir::CRATE_HIR_ID` at the construction site: `p` comes back
/// `<emitted>` and this test fails on exactly that. Recorded rather than
/// silently re-pointed — a wrong mutation claim is the kind of thing that gets
/// copied forward.
#[test]
fn a_raw_only_method_on_a_local_degrades_it() {
    // RE-BASED at S3.2′-3: `is_null` on a local now selects the optional form
    // and is refused by its CONSTRUCTION guard, which is a different arm with a
    // different reason. `read` still has no image, so it is what this witness
    // needs to keep testing A1 reach over the locals universe.
    let got = decisions_of(
        "#![allow(dead_code, unused_unsafe, unused_variables)]\n\
         pub unsafe fn f(a: *mut i32) -> i32 { let p: *mut i32 = a; p.read() }\n",
    );
    assert_eq!(
        reason_of(&got, "p", false),
        "raw-pointer-operation",
        "the local reached A1 and was not stopped by it: {got:?}"
    );
}

/// **An optional LOCAL is refused at its construction site.**
///
/// `let p: Option<&i32> = <raw pointer>` is `E0308` however the uses read, so
/// the blocker is the initializer — the arm the slice forms already have.
///
/// **This arm exists because a fixture found it.** Every subject in S3.2′-3's
/// measured market is a parameter, so the corpus could not have exercised it,
/// and the first thing to reach it would have been an emitted crate that does
/// not compile.
#[test]
fn an_optional_local_is_refused_at_its_construction_site() {
    let got = decisions_of(
        "#![allow(dead_code, unused_unsafe, unused_variables)]\n\
         pub unsafe fn f(a: *mut i32) -> i32 { let p: *mut i32 = a; if p.is_null() { return 0; } *p }\n",
    );
    assert_eq!(
        reason_of(&got, "p", false),
        "opt-local-construction",
        "an optional local was not stopped at its construction site: {got:?}"
    );
}

/// **Both operands of ONE comparison use the address-observation arm.**
///
/// The population pair with no confound left: same function, same expression,
/// same span. Before the repair the parameter operand of `q == b` degraded
/// `ptr-comparison` while the local operand came back `ref-shared` — one
/// comparison, one gate, two answers, decided purely by which population the
/// operand belonged to.
///
/// Keeping the parameter assertion here is the point. A locals-only test would
/// still pass if a later change killed the gate for *everyone*, and would
/// report that as success.
///
/// *Mutation-tested (defect restoration — `hir_id` back to `CRATE_HIR_ID`;
/// the earlier draft named the `binding_hir` DELETION here, which panics
/// instead and so proves nothing about this pair):* the measured failure is
///
/// ```text
/// local operand: [("a", true, "<emitted>"), ("b", true, "ptr-comparison"), ("q", false, "<emitted>")]
/// ```
///
/// — the parameter assertion green, the local one red, with both operands of
/// the one comparison printed side by side. That single line **is** the defect.
#[test]
fn one_comparison_opens_its_parameter_and_local_operand_alike() {
    let got = decisions_of(
        "#![allow(dead_code, unused_unsafe, unused_variables)]\n\
         pub unsafe fn f(a: *mut i32, b: *mut i32) -> i32 { \
         let q: *mut i32 = a; if q == b { return 1; } 0 }\n",
    );
    assert_eq!(
        reason_of(&got, "b", true),
        "<emitted>",
        "parameter operand: {got:?}"
    );
    assert_eq!(
        reason_of(&got, "q", false),
        "<emitted>",
        "local operand: {got:?}"
    );
}

/// **The facts join reports a fact the DECISION never reached.**
///
/// This is the instrument's whole purpose, so it is what the witness tests. The
/// fixture's local is **unannotated**, so it degrades at
/// `slice-local-construction` — a slice value would have to be built at its
/// initializer — and the A1 op fact never reaches the reason field. A
/// reason-field tally therefore records nothing about its `.offset()` use, and
/// would report the op population as smaller than it is.
///
/// **The dissolution amended the expected key, not the witness.** Before it,
/// the fixture stopped at `no-declared-type`, the first predicate, and never
/// consulted A1 at all; now it reaches A1, selects the slice form, and is
/// stopped by the construction-site gate. Either way the degradation is
/// upstream of the reported fact, which is the property under test — and the
/// amended key makes the fixture a STRICTLY harder case, because the decision
/// now does consult the op it must not be the source of.
///
/// The join must still report `annotated=0` **and** `raw_op=offset` on that
/// same subject. If it cannot, it has inherited the ordering it exists to
/// bypass, and every "zero" it certifies in the reachability table is worth
/// nothing.
///
/// *Mutation-tested (Rider 0, deletion first):* replacing the `raw_only_uses`
/// lookup with `"-"` fails on the op column; deriving the row from
/// `decide_one`'s reason instead of from the facts fails the same way, which is
/// the substantive mutation — it reintroduces exactly the coupling.
#[test]
fn the_facts_join_reports_facts_the_decision_never_reached() {
    let src = "#![allow(dead_code, unused_unsafe, unused_variables)]\n\
               pub unsafe fn f(a: *mut i32) -> i32 { let p = a; *p.offset(1) }\n";
    let fixture = Fixture::new(&[("lib.rs", src)]);
    let (reason, facts) =
        ::utils::compilation::run_compiler_on_path(&fixture.0.join("lib.rs"), |tcx| {
            let table = super::decide_table(tcx).expect("table");
            let rows = super::artifact::rows(tcx, &table);
            let reason = rows
                .iter()
                .find(|r| r.arg_index.is_none())
                .and_then(|r| r.degrade_reason.clone())
                .unwrap_or_default();
            (reason, super::facts_join_tsv(tcx).expect("facts join"))
        })
        .expect("fixture compiles");

    assert_eq!(
        reason, "slice-local-construction",
        "the fixture must degrade UPSTREAM of the reported fact, or it \
         witnesses nothing"
    );
    let hdr: Vec<&str> = facts.lines().next().expect("header").split('\t').collect();
    let col = |n: &str| hdr.iter().position(|h| *h == n).expect("column present");
    let (c_param, c_ann, c_op) = (col("is_param"), col("annotated"), col("raw_op"));
    let local_row = facts
        .lines()
        .skip(1)
        .map(|l| l.split('\t').collect::<Vec<_>>())
        .find(|c| c[c_param] == "0")
        .unwrap_or_else(|| panic!("no local row in the facts join:\n{facts}"));
    assert_eq!(
        local_row[c_ann], "0",
        "the local is unannotated: {local_row:?}"
    );
    assert_eq!(
        local_row[c_op], "offset",
        "the join lost the op the decision never reached — it has inherited \
         decide_one's ordering: {local_row:?}"
    );
}

/// **`calloc` and `realloc` are told apart by CALLEE, never by arity.**
///
/// Both take two arguments, and only `calloc`'s first is an element count —
/// `realloc`'s is the pointer being resized. An arity test therefore reports a
/// **pointer expression as a length**, which is not a near-miss: it is a length
/// the emitted code would claim for a slice.
///
/// This is a regression pin on a defect that reached a de-risk run: every
/// `realloc` in libtree came back `alloc-count` with `(*v).p` as its "count".
/// Caught because the de-risk printed the size expressions rather than only
/// counting the classes — a tally would have shown a plausible histogram.
///
/// *Mutation-tested (Rider 0, deletion first):* replacing the callee match with
/// `if args.len() == 2` restores the defect and fails this test on `b`.
#[test]
fn calloc_and_realloc_are_told_apart_by_callee_not_arity() {
    let src = "#![allow(dead_code, unused_unsafe, unused_variables)]\n\
        extern \"C\" {\n\
            fn calloc(n: usize, sz: usize) -> *mut core::ffi::c_void;\n\
            fn realloc(p: *mut core::ffi::c_void, sz: usize) -> *mut core::ffi::c_void;\n\
        }\n\
        pub unsafe fn f(n: usize) -> i32 {\n\
            let a: *mut i32 = calloc(n, 4) as *mut i32;\n\
            let b: *mut i32 = realloc(a as *mut core::ffi::c_void, 8) as *mut i32;\n\
            *b\n\
        }\n";
    let fixture = Fixture::new(&[("lib.rs", src)]);
    let tsv = ::utils::compilation::run_compiler_on_path(&fixture.0.join("lib.rs"), |tcx| {
        super::facts_join_tsv(tcx).expect("facts join")
    })
    .expect("fixture compiles");

    // Indexed BY HEADER NAME, never by position. Adding the `fatness` column
    // in S3.2′-1 shifted every later index and broke this test — the exact
    // hazard `construction.rs` warns about for tabs inside snippets, one level
    // up. A positional read is a latent break for every future column.
    let hdr: Vec<&str> = tsv.lines().next().expect("header").split('\t').collect();
    let col = |name: &str| {
        hdr.iter()
            .position(|h| *h == name)
            .unwrap_or_else(|| panic!("facts join has no `{name}` column: {hdr:?}"))
    };
    let (c_param, c_len, c_size) = (col("is_param"), col("len_class"), col("size_expr"));
    let classes: Vec<(String, String)> = tsv
        .lines()
        .skip(1)
        .map(|l| l.split('\t').collect::<Vec<_>>())
        .filter(|c| c[c_param] == "0") // locals only
        .map(|c| (c[c_len].to_owned(), c[c_size].to_owned()))
        .collect();

    assert!(
        classes
            .iter()
            .any(|(k, expr)| k == "alloc-count" && expr.contains('n')),
        "calloc's element count must be recovered from its FIRST argument: {classes:?}"
    );
    assert!(
        classes.iter().any(|(k, _)| k == "alloc-size-literal"),
        "realloc must be classified by its SIZE argument, not by treating its \
         pointer argument as a count: {classes:?}"
    );
    assert!(
        !classes
            .iter()
            .any(|(k, expr)| k == "alloc-count" && expr.contains("c_void")),
        "a POINTER expression was reported as an element count — the arity \
         defect is back: {classes:?}"
    );
}

// ---------------------------------------------------------------------------
// S3.2′-1 — the fatness ENTRY VALIDATION (A-2's discipline, applied to fatness)
// ---------------------------------------------------------------------------

/// `(local name, fatness verdict)` for every pointer local in a fixture.
fn fatness_of(src: &str) -> Vec<(String, &'static str)> {
    let fixture = Fixture::new(&[("lib.rs", src)]);
    ::utils::compilation::run_compiler_on_path(&fixture.0.join("lib.rs"), |tcx| {
        let program = super::collect_program(tcx);
        let mut_facts =
            crate::analyses::borrow_ownership::mutability_facts::MutFacts::from_program(&program);
        let fat = super::fat_facts::FatFacts::from_program(&program);
        super::collect_local_subjects(tcx, &program, &mut_facts)
            .iter()
            .map(|s| {
                (
                    s.param_name
                        .clone()
                        .unwrap_or_else(|| "<unnamed>".to_owned()),
                    fat.render(s.fn_did, s.local),
                )
            })
            .collect::<Vec<_>>()
    })
    .expect("fixture compiles")
}

const FAT_HDR: &str = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, unused_assignments)]\nextern \"C\" { fn malloc(size: usize) -> *mut core::ffi::c_void; }\n";

/// **Fatness is MEASURED in, not assumed in** — A-2's condition, applied to a
/// second dependency that has never been on BO's path either.
///
/// The two positive controls live in **one function** deliberately. Either
/// alone would pass against an analysis that returns a constant, which is the
/// same defect shape the locals-A1 population pair was built to exclude: a
/// control that cannot distinguish is not a control.
///
/// *Mutation-tested (Rider 0, deletion first):* replacing `FatFacts::verdict`
/// with a constant `Some(Fatness::Arr)` — or `Ptr` — fails this test, because
/// the assertion is that the two locals **differ**, not that either has a
/// particular value.
#[test]
fn fatness_entry_validation_distinguishes_array_from_single_object() {
    let got = fatness_of(&format!(
        "{FAT_HDR}pub unsafe fn f(c: i32) -> i32 {{\n\
         let mut arr: [i32; 8] = [0; 8];\n\
         let decayed: *mut i32 = arr.as_mut_ptr();\n\
         let single: *mut i32 = malloc(4) as *mut i32;\n\
         *single = c;\n\
         *decayed.offset(1) + *single\n\
         }}\n"
    ));
    let of = |n: &str| {
        got.iter()
            .find(|(name, _)| name == n)
            .unwrap_or_else(|| panic!("no local `{n}`: {got:?}"))
            .1
    };
    assert_eq!(
        of("decayed"),
        "arr",
        "array decay must read as array: {got:?}"
    );
    assert_eq!(
        of("single"),
        "ptr",
        "a single-object allocation must not read as array: {got:?}"
    );
}

/// **`ptr` is a DEFAULT, not a conclusion** — the control the ruling did not
/// ask for, and the one that decides how the verdict may be used.
///
/// `Fatness::Arr ⊑ Fatness::Ptr` and the solver takes the **greatest** model,
/// so an unconstrained variable is maximized to `Ptr`. This fixture gives the
/// analysis *no information at all* about `opaque` — no arithmetic, no
/// indexing, no allocation — and pins that the answer is still `ptr`.
///
/// The consequence is load-bearing and runs opposite to the naive reading of
/// ruling A-1: this analysis never says *unknown*, so `ptr` **cannot** be read
/// as evidence of single-object allocation. Emitting a slice on `arr` is
/// licensed because `arr` is forced by constraints; treating `ptr` as proof of
/// thinness is not, and the `Box<T>` / `Box<[T]>` discriminator must therefore
/// rest on the allocation-size expression with fatness as corroboration only.
///
/// *Mutation-tested:* making `verdict` return `None` for unconstrained locals —
/// i.e. pretending the analysis abstains — fails this test, which is the point:
/// it does not abstain.
#[test]
fn a_pointer_with_no_array_evidence_reads_thin_by_default() {
    let got = fatness_of(&format!(
        "{FAT_HDR}pub unsafe fn f(q: *mut i32) -> i32 {{ let opaque: *mut i32 = q; 0 }}\n"
    ));
    assert_eq!(
        got.iter().find(|(n, _)| n == "opaque").map(|(_, v)| *v),
        Some("ptr"),
        "an unconstrained pointer must still receive a verdict, and it is the \
         top of the lattice — `ptr` here means NO ARRAY EVIDENCE, not `thin`: \
         {got:?}"
    );
}

/// **The negative control: a clean local is still emitted.**
///
/// Without it, "every local now degrades" would pass both witnesses above. The
/// repair must gate exactly the locals carrying a raw-only use, not the
/// population.
///
/// *Mutation-tested, claim CORRECTED after measurement:* injecting an
/// unconditional degrade before the A1 arms fails this test — and also fails
/// `a_raw_only_method_on_a_local_degrades_it`, which an earlier draft said
/// would stay green. It cannot: that witness asserts a *specific* reason, and
/// the injected one is a different reason. Only
/// `one_comparison_degrades_its_parameter_and_its_local_operand_alike` survives,
/// because the injected reason happens to be the one it expects.
///
/// The point stands, and is what the mutation establishes: this control is the
/// only test in the trio that can distinguish *"the gate works"* from *"every
/// local degrades"*. 24 tests died with it, so the injection was effective.
#[test]
fn a_local_with_no_raw_only_use_is_still_emitted() {
    let got = decisions_of(
        "#![allow(dead_code, unused_unsafe, unused_variables)]\n\
         pub unsafe fn f(a: *mut i32) -> i32 { let p: *mut i32 = a; *p }\n",
    );
    assert_eq!(
        reason_of(&got, "p", false),
        "<emitted>",
        "a clean local must survive A1: {got:?}"
    );
}

// ---------------------------------------------------------------------------
// The freed-slot gate
// ---------------------------------------------------------------------------

/// The two freed-slot fixtures, differing in **one token**: the callee of the
/// call that consumes `p`.
///
/// # Why the free is conditional — measured, not styled
///
/// The obvious fixture does not reach the gate, and why is worth recording.
/// With an unconditional `free` as the only thing that happens to the binding,
/// BO settles the slot **`Owning`** and `kind-owning` fires three arms earlier.
/// Measured on four such shapes: `free` of a parameter, of a copy of one, of a
/// `malloc` result, and of a parameter beside a second live pointer — all four
/// `owning`/`kind-owning`. **A fixture that degrades upstream witnesses
/// nothing.**
///
/// Under a *conditional* free the slot is not owning on all paths, BO retracts
/// the sink, and the kind settles `Ref` — while the program still frees it.
/// That is the leaked-free shape backlog S2-2 named, and a reference for it is a
/// reference to memory freed on the other path.
///
/// The corpus has 44 freed-`Ref` subjects, and none is reproducible in its own
/// shape here: its cast-free specimen, `lodepng_free`, settles `Ref` only
/// because a caller retracts the sink — and that same caller makes
/// `call-site-not-adapted` fire, so reproducing it would witness the reason
/// rather than the gate. This shape reaches the gate on its own.
///
/// Everything but the callee is held fixed — declaration, control flow, and the
/// absence of any in-crate reference to the function under test — and `keeper`
/// is declared in the same `extern` block with the same signature, so even the
/// callee's kind is fixed. Only the NAME differs, which is exactly what
/// `DEALLOCATORS` keys on.
fn freed_fixture(callee: &str) -> String {
    format!(
        "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
         pub unsafe fn free(q: *mut u8) {{ *q = 0; }}\n\
         pub unsafe fn keeper(q: *mut u8) {{ *q = 0; }}\n\
         pub unsafe fn releases(a: *mut u8, b: i32) {{\n\
         \x20   let p: *mut u8 = a;\n\
         \x20   if b > 0 {{ {callee}(p); }}\n\
         }}\n"
    )
}

/// **The gate — a subject that would otherwise emit is degraded as
/// `freed-slot`.**
///
/// The control half is what makes this a witness rather than an assertion: it
/// establishes that this subject reaches `Decision::Ref` when the same call goes
/// to a non-deallocator, so the freed half's degradation cannot be an artefact
/// of the fixture failing some earlier test.
///
/// *Mutation-tested (Rider 0, deletion first):* deleting the `subject.freed_at`
/// arm at the end of `decide_one` makes the freed half read `<emitted>` and
/// fails this. Second mutation: moving that arm ABOVE the `referenced` arm keeps
/// this green and fails the corpus zero-movement check instead — recorded
/// because it is the one mutation this witness deliberately does **not** catch,
/// and the reason the corpus assertion is not redundant with it.
#[test]
fn a_freed_subject_that_would_otherwise_emit_is_degraded_as_freed_slot() {
    let control = decisions_of(&freed_fixture("keeper"));
    assert_eq!(
        reason_of(&control, "p", false),
        "<emitted>",
        "the control subject must reach Ref, or the freed half witnesses \
         nothing: {control:?}"
    );

    let freed = decisions_of(&freed_fixture("free"));
    assert_eq!(
        reason_of(&freed, "p", false),
        "freed-slot",
        "a freed subject that passed every other test was still emitted: \
         {freed:?}"
    );
}

/// **Co-attribution.** A freed subject stopped by an EARLIER reason keeps that
/// reason and still carries the `freed` column.
///
/// This is the population the corpus actually has: 44 freed subjects whose BO
/// kind is `Ref`, every one of them stopped before the gate. A reason-derived
/// freed count reports that population as **empty**, because `decide_one`
/// returns at the first failing test — the same ordering blindness
/// `facts_join_tsv` exists to defeat.
///
/// *Mutation-tested (Rider 0, deletion first):* replacing `freed` in
/// `artifact::rows` with a derivation from the reason —
/// `Some(matches!(decision, Decision::Degraded(r) if r.reason.key() ==
/// "freed-slot"))` — fails this: the row reads `false` while the program plainly
/// frees the binding. The obvious spelling of that mutation,
/// `degrade_reason.as_deref() == …`, does **not compile** — the field is moved
/// into the row two lines above — which is mild structural evidence in its own
/// right that this column cannot restate the reason without going back to the
/// decision.
#[test]
fn a_freed_subject_stopped_earlier_keeps_its_reason_and_carries_the_column() {
    // **RE-BASED at S3.2′-3.** The earlier blocker used to be `p.is_null()`,
    // which no longer fires before the freed gate — a null test now selects the
    // optional form, whose own refusals come after it. `read` still degrades in
    // the raw-use block, which is where this witness needs its earlier reason to
    // come from.
    let src = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
               extern \"C\" {\n\
               \x20   fn free(p: *mut core::ffi::c_void);\n\
               }\n\
               pub unsafe fn releases(a: *mut i32, b: i32) -> i32 {\n\
               \x20   let p: *mut i32 = a;\n\
               \x20   let dead = p.read();\n\
               \x20   if b > 0 { free(p as *mut core::ffi::c_void); }\n\
               \x20   dead\n\
               }\n";
    let rows = artifact_rows_of(src);
    let row = rows
        .iter()
        .find(|r| r.param_name.as_deref() == Some("p") && r.arg_index.is_none())
        .unwrap_or_else(|| panic!("no subject `p`: {rows:?}"));

    assert_eq!(
        row.degrade_reason.as_deref(),
        Some("raw-pointer-operation"),
        "the gate displaced an earlier reason — it must fire LAST: {row:?}"
    );
    assert_eq!(
        row.freed,
        Some(true),
        "the freed fact vanished behind the earlier reason: {row:?}"
    );
}

/// The column is a FACT about the subject, not a restatement of the reason: an
/// unfreed subject reads `Some(false)`, never `None`.
///
/// `None` is producer B's value — "no derivation for this" — and producer A
/// always has one. Without this, a producer A that emitted `None` everywhere
/// would satisfy the co-attribution witness above on its `Some(true)` row alone.
///
/// *Mutation-tested (Rider 0, deletion first):* changing `artifact::rows` to
/// emit `subject.freed_at.is_some().then_some(true)` fails this.
#[test]
fn an_unfreed_subject_carries_a_present_false_not_an_absent_column() {
    let rows = artifact_rows_of(&freed_fixture("keeper"));
    let row = rows
        .iter()
        .find(|r| r.param_name.as_deref() == Some("p") && r.arg_index.is_none())
        .unwrap_or_else(|| panic!("no subject `p`: {rows:?}"));
    assert_eq!(
        row.freed,
        Some(false),
        "producer A must state the fact it has, not abstain: {row:?}"
    );
}

// ---------------------------------------------------------------------------
// S3.2′-2 — borrowed slices
// ---------------------------------------------------------------------------

/// **An arithmetic op on a LOCAL takes the slice arm, and stops at
/// construction.**
///
/// The counterpart to `a_raw_only_method_on_a_local_degrades_it`: the same
/// shape, an arithmetic op instead of a non-arithmetic one, landing on a
/// different reason. A parameter needs no construction — the caller supplies the
/// slice — but a local's initializer is a raw-pointer expression that would need
/// `from_raw_parts` and a length. Scoped out and counted, not attempted.
///
/// *Mutation-tested (Rider 0, deletion first):* deleting the `SubjectKind::Local`
/// arm in `decide_one` makes this read `slice-use-unsupported` (the local's own
/// initializer use is not `*p.offset(e)`), so the local would be silently
/// reclassified rather than named.
#[test]
fn an_arithmetic_op_on_a_local_stops_at_slice_construction() {
    let got = decisions_of(
        "#![allow(dead_code, unused_unsafe, unused_variables)]\n\
         pub unsafe fn f(a: *mut i32) -> i32 { let p: *mut i32 = a; *p.offset(1) }\n",
    );
    assert_eq!(
        reason_of(&got, "p", false),
        "slice-local-construction",
        "an arithmetic use on a local must take the slice arm and stop at \
         construction, with its own reason: {got:?}"
    );
}

/// **A non-arithmetic raw-only use blocks the slice arm — checked over the WHOLE
/// use set, not the first.**
///
/// `p` carries `offset` *and* `read`. A first-wins reading of `raw_only_uses`
/// meets `offset` first and concludes "arithmetic, emit a slice" — and
/// `p.read()` on `&[i32]` does not compile. This is the reason that map holds a
/// vector.
///
/// **RE-BASED at S3.2′-3.** The original fixture paired `offset` with
/// `is_null`, and that pair is no longer mixed-and-unsupported: it is exactly
/// g13's shape, and now selects `Option<&[T]>`. Re-basing onto `read` keeps the
/// witness testing what it was written to test — the whole-set reading — rather
/// than letting it pass by accident on a class that moved.
///
/// *Mutation-tested (Rider 0, deletion first):* replacing the `all(..)` in
/// `decide_one` with a test of `uses.first()` makes this emit a slice, and the
/// emitted crate does not type-check.
#[test]
fn a_mixed_use_set_refuses_the_slice_arm() {
    let got = decisions_of(
        "#![allow(dead_code, unused_unsafe, unused_variables)]\n\
         pub unsafe fn f(p: *mut i32) -> i32 { let v = p.read(); v + *p.offset(1) }\n",
    );
    assert_eq!(
        reason_of(&got, "p", true),
        "raw-pointer-operation",
        "a subject with a non-arithmetic use must not reach the slice arm: {got:?}"
    );
}

/// **The pair that MOVED, pinned in its new disposition.**
///
/// `{offset, is_null}` on a fat subject is g13's shape. Asserting where it lands
/// now is what keeps the re-basing above honest: without this, "the mixed-use
/// guard still works" and "the optional arm swallowed the case" look identical.
#[test]
fn arithmetic_with_a_null_test_takes_the_optional_slice_form() {
    let got = decisions_of(
        "#![allow(dead_code, unused_unsafe, unused_variables)]\n\
         pub unsafe fn f(p: *mut i32) -> i32 { if p.is_null() { return 0; } *p.offset(1) }\n",
    );
    assert_eq!(
        reason_of(&got, "p", true),
        "<emitted>",
        "the fat optional twin did not take this subject: {got:?}"
    );
}

/// **The fatness LICENSE is required, not merely corroborating in name.**
///
/// Op-facts supply the need; fatness supplies the license. Mutating the
/// conjunct away is the check that it is wired at all — on the corpus it
/// excludes 0 of 1,690, so only a fixture can distinguish "required" from
/// "present but unread".
///
/// *Mutation-tested (Rider 0, deletion first):* deleting
/// `&& fat.is_array(..)` from `decide_one`'s guard leaves this green (the
/// subject reads `arr` anyway) — recorded as the mutation this witness does
/// **not** kill, which is why the conjunct's vacuity is reported as measured
/// rather than claimed as load-bearing. What it does pin is that an arithmetic
/// subject reaching the slice arm emits a slice form at all.
#[test]
fn an_arithmetic_parameter_emits_a_slice_form() {
    let rows = artifact_rows_of(
        "#![allow(dead_code, unused_unsafe, unused_variables)]\n\
         pub unsafe fn f(p: *mut i32, n: usize) { let mut i: usize = 0; \
         while i < n { *p.offset(i as isize) = 1; i += 1; } }\n",
    );
    let row = rows
        .iter()
        .find(|r| r.param_name.as_deref() == Some("p"))
        .unwrap_or_else(|| panic!("no subject p: {rows:?}"));
    assert_eq!(
        row.outcome,
        Some(crate::coverage_recon::schema::Outcome::SliceMut),
        "an arithmetic, array-licensed parameter must take a slice form: {row:?}"
    );
    assert_eq!(
        row.approx_len,
        Some(true),
        "a parameter has no construction site, so its length is approximated \
         and the counter must say so: {row:?}"
    );
}

/// **A subject whose use-edits NEST must not produce overlapping edits.**
///
/// brotli's `DecodeSymbol` shape, and the reason brotli contributed **zero**
/// emit-frame rows to the S3.6-1 step-3 sweep: a self-advance whose index
/// expression contains a plain dereference of the same binding —
/// `table = table.offset((*table).value as isize)`.
///
/// The path visitor fires once per OCCURRENCE, so two edits are produced and
/// the outer contains the inner:
///
/// - outer, the self-advance source: span `table.offset(…)` → `&mut table[…..]`
/// - inner, the plain deref: span `(*table)` → `table[0]`
///
/// `apply` rejects the pair — "a plan that wants two rewrites of one range has
/// not decided" — and is right to.
///
/// **The overlap is only the visible half.** `index_text` renders the index
/// with `span_to_snippet`, so the outer replacement embeds `(*table)`
/// **verbatim** — text with no meaning on a `&[T]`. Dropping either edit
/// therefore yields an ill-typed crate rather than a smaller win, which is why
/// the repair degrades the subject instead of picking a winner: the flat-splice
/// model cannot express this rewrite at all.
///
/// *Mutation-tested (Rider 0, deletion first):* remove the nesting gate and
/// this fails with a rollback reading "edit overlaps an earlier edit".
#[test]
fn a_subject_whose_uses_nest_produces_no_overlapping_edits() {
    let src = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
               pub struct HuffmanCode { pub value: u32 }\n\
               pub unsafe fn decode(mut table: *mut HuffmanCode) -> u32 {\n\
               \x20   table = table.offset((*table).value as isize);\n\
               \x20   (*table).value\n\
               }\n";
    let fixture = Fixture::new(&[("lib.rs", src)]);
    let emission = emit(&fixture);
    assert!(
        emission.rollbacks.is_empty(),
        "nested use-edits reached `apply` and were rolled back; the nesting \
         must be refused at DECISION time, where the subject can degrade with \
         an attributed reason: {:?}",
        emission.rollbacks
    );
    // Not merely "no rollback" — the subject must degrade UNDER ITS OWN REASON.
    // An implementation that silently dropped one of the two edits would satisfy
    // the assertion above while emitting the stale `(*table)` text, which is the
    // failure this gate exists to prevent.
    assert_eq!(
        reason_of(&decisions_of(src), "table", true),
        "nested-use-edits",
        "the nesting must be attributed, not absorbed into another reason"
    );
}

/// **Nesting across TWO subjects refuses the inner one and KEEPS the outer.**
///
/// brotli's second shape, and the 15 of 17 collisions a per-subject check left
/// standing — `enc::block_splitter::RemapBlockIds*`,
/// `enc::brotli_bit_stream::StoreSimpleHuffmanTree`, `enc::cluster::*`:
///
/// ```ignore
/// *new_id.offset(*block_ids.offset(i as isize) as isize)
/// ```
///
/// `new_id`'s edit spans the whole outer `offset` call; `block_ids`'s sits
/// inside it. No per-subject check can see this, because neither subject's own
/// rewrites nest.
///
/// **Refusing the INNER subject is the correct pick, not merely the safe one.**
/// `index_text` renders the index by `span_to_snippet`, so the outer
/// replacement embeds `*block_ids.offset(i as isize)` verbatim — and that text
/// is well-typed precisely when `block_ids` is still a pointer. So the outer
/// rewrite stays valid *because* the inner was refused, which is why this test
/// asserts both halves: refusing the inner while also dropping the outer would
/// be sound but would give away yield the defect does not cost.
///
/// *Mutation-tested (Rider 0, deletion first):* restrict the pass to same-entry
/// pairs — the shape the first fix had — and this fails with brotli's own
/// rollback.
#[test]
fn nesting_across_two_subjects_refuses_the_inner_and_keeps_the_outer() {
    let src = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
               pub unsafe fn f(new_id: *mut u32, block_ids: *mut u32, n: usize) {\n\
               \x20   let mut i: usize = 0;\n\
               \x20   while i < n {\n\
               \x20       *new_id.offset(*block_ids.offset(i as isize) as isize) = 1;\n\
               \x20       i += 1;\n\
               \x20   }\n\
               }\n";
    let fixture = Fixture::new(&[("lib.rs", src)]);
    assert!(
        emit(&fixture).rollbacks.is_empty(),
        "cross-subject nesting reached `apply`: {:?}",
        emit(&fixture).rollbacks
    );
    let got = decisions_of(src);
    assert_eq!(
        reason_of(&got, "block_ids", true),
        "nested-use-edits",
        "the INNER subject is the one the nesting refuses: {got:?}"
    );
    assert_eq!(
        reason_of(&got, "new_id", true),
        "<emitted>",
        "the OUTER subject must survive — its embedded snippet is valid exactly \
         because the inner stayed raw: {got:?}"
    );
}

/// **The nesting gate must not fire on a subject whose uses merely SIT SIDE BY
/// SIDE** — the control for the witness above.
///
/// Without it, a gate that refused every multi-use slice subject would pass the
/// nesting test while destroying the whole slice population, and the corpus
/// would report it as a yield loss rather than as a bug.
#[test]
fn disjoint_uses_of_one_subject_still_emit_a_slice() {
    let src = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
               pub unsafe fn f(p: *mut i32, n: usize) {\n\
               \x20   let mut i: usize = 0;\n\
               \x20   while i < n { *p.offset(i as isize) = 1; i += 1; }\n\
               \x20   *p.offset(0) = 2;\n\
               }\n";
    assert_eq!(
        reason_of(&decisions_of(src), "p", true),
        "<emitted>",
        "two DISJOINT arithmetic uses must still emit; the gate keys on \
         containment, not on multiplicity"
    );
}

/// **The index rendering must survive a NON-`usize` counter — the shape the
/// corpus actually has.**
///
/// c2rust writes `*p.offset(1 as libc::c_int as isize)`: a **double** cast.
/// Stripping only the outer `as isize` leaves a `c_int`, and
/// `error[E0277]: the type `[*mut i8]` cannot be indexed by `i32`` is what the
/// corpus returned — every one of the 14 decided slices reverted, taking two
/// sibling `Ref` emissions in `heman_draw_colored_circles` with them, because
/// revert granularity is per-function.
///
/// **g11/g12 could not have caught this.** They were transcribed with a `usize`
/// counter, so stripping the cast happened to yield the right type. A golden
/// pins the dimensions it fixes; the counter type was left free, and free
/// dimensions must be either measured-representative of the corpus or covered
/// by a witness. This is that witness.
///
/// *Mutation-tested (Rider 0, deletion first):* reverting `index_text` to strip
/// the cast unconditionally — dropping the `usize` type test — makes the first
/// assertion fail, because the rewrite is then ill-typed and the verify loop
/// reverts it, leaving the source unchanged.
#[test]
fn a_non_usize_counter_is_cast_rather_than_stripped() {
    let src = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
               pub unsafe fn f(p: *mut i32) -> i32 {\n\
               \x20   *p.offset(1 as core::ffi::c_int as isize)\n\
               }\n";
    let super::RewriteOutcome::Emitted { source, .. } = super::rewrite_m1(src) else {
        panic!("fixture must emit");
    };
    assert!(
        source.contains("p[(1 as core::ffi::c_int) as usize]"),
        "a non-usize index must be parenthesised and cast, or the slice is \
         indexed by the wrong type:\n{source}"
    );
    assert!(
        source.contains("p: &[i32]"),
        "the declaration must still become a slice:\n{source}"
    );
}

/// **The `usize` path stays byte-identical to the ratified golden text.**
///
/// The type-aware repair must not buy corpus correctness by changing what g11
/// and g12 emit. Asserted on the emitted BYTES rather than left to the goldens'
/// rustfmt-canonicalised comparison, which would absorb a spurious cast as
/// whitespace-adjacent noise.
///
/// *Mutation-tested (Rider 0, deletion first):* making `index_text` cast
/// unconditionally emits `p[i as usize]` and fails this — which is exactly the
/// spec-bending option this repair declined.
#[test]
fn a_usize_counter_still_renders_a_bare_index() {
    let golden = super::goldens_for_reconciliation()
        .into_iter()
        .find(|(name, _)| *name == "g11_slice_shared")
        .expect("g11 is registered");
    let super::RewriteOutcome::Emitted { source, .. } = super::rewrite_m1(golden.1) else {
        panic!("g11 must emit");
    };
    assert!(
        source.contains("total += p[i];"),
        "a usize counter must still render bare — the ratified golden text:\n{source}"
    );
    assert!(
        !source.contains("p[i as usize]"),
        "the repair added a cast the golden does not have:\n{source}"
    );
}

/// **THE ACCEPT-SET IS THE SCOPE.** Both authorised positions emit; every known
/// neighbour position is refused with its own attribution.
///
/// # Why this test exists, stated plainly
///
/// Twice in this slice the implementation was wider than its own approved
/// scope: Amendment 1 named the use-site work only after the goldens implied
/// it, and the classifier then accepted `&mut *p.offset(e)` — a third position —
/// because it tested the deref's SHAPE without testing its CONTEXT. Scope is
/// whatever the classifier accepts, so the accept-set has to be pinned against
/// the scope rather than described in prose beside it.
///
/// Positive controls are the two authorised positions; negative controls are the
/// three neighbours the corpus actually contains. A fourth neighbour appearing
/// later fails nothing here — but it will be one line to add, and its absence is
/// now visible rather than assumed.
///
/// *Mutation-tested (Rider 0, deletion first):* removing the parent-borrow check
/// in `classify` makes the borrow-of-deref case emit, failing this.
#[test]
fn the_classifier_accept_set_equals_the_approved_scope() {
    fn reason_for(body: &str) -> String {
        let src = format!(
            "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
             pub unsafe fn f(mut p: *mut i32, n: usize) -> *mut i32 {{\n{body}\n}}\n"
        );
        let got = decisions_of(&src);
        reason_of(&got, "p", true)
    }

    // POSITIVE — the two positions Amendment 1 authorises.
    // Control: `p` is ALSO returned bare here, which is itself an unsupported
    // use, so the subject is refused even though the deref position is
    // authorised. It pins that the harness is not trivially green — and, more
    // usefully, that the accept-set is a property of ALL of a subject's uses
    // rather than of the one the test happens to be looking at.
    assert_eq!(
        reason_for(
            "    let mut i: usize = 0;\n    while i < n { let _v = *p.offset(i as isize); i += 1; }\n    p"
        ),
        "slice-use-unsupported",
        "an authorised position plus a bare use must still be refused"
    );
    for (label, body) in [
        (
            "deref read",
            "    let mut i: usize = 0;\n    let mut t = 0;\n    while i < n { t += *p.offset(i as isize); i += 1; }\n    core::ptr::null_mut()",
        ),
        (
            "deref write",
            "    let mut i: usize = 0;\n    while i < n { *p.offset(i as isize) = 1; i += 1; }\n    core::ptr::null_mut()",
        ),
        // **S3.2′-2b moved these two INTO the approved scope**, by ruling. The
        // guard tracks the scope; it does not defend the old one.
        ("plain deref", "    let _v = *p;\n    core::ptr::null_mut()"),
        (
            "self-advance",
            "    p = p.offset(1);\n    let _v = *p;\n    core::ptr::null_mut()",
        ),
    ] {
        assert_eq!(
            reason_for(body),
            "<emitted>",
            "{label} is an AUTHORISED position and must emit"
        );
    }

    // NEGATIVE — every known neighbour, each refused with its own attribution.
    for (label, body) in [
        ("borrow of deref", "    &mut *p.offset(1 as isize)"),
        // **REBIND is ratified spec (g18) but its ARM is not built** — its
        // market is 0 and S3.6-gated, so mechanism follows market. It stays a
        // negative control, and the reason it is refused has changed from "out
        // of scope" to "in scope, unbuilt". Both mean: must not emit.
        (
            "rebind",
            "    let q: *mut i32 = p.offset(1 as isize);\n    q",
        ),
        // **S3.2′-5 registers the SIGN as a refusal axis in this vocabulary.**
        // Every other entry here is refused for the shape of a *use*; this one
        // has an authorised use shape and is refused for the *argument's sign*.
        // It is listed here so the accept-set is read as "which subjects emit",
        // not merely "which use shapes are recognised" — and so a future slice
        // that lifts the gate has to edit this list to do it.
        (
            "may-be-negative offset",
            "    let _v = *p.offset(-1 as isize);\n    core::ptr::null_mut()",
        ),
    ] {
        let got = reason_for(body);
        // **Per-entry, not one shared disjunction.** S3.2′-5 adds a third
        // admissible reason; widening a single `||` for the whole loop would
        // let ANY negative control drift onto ANY of the three unnoticed, which
        // is exactly the coverage this guard exists to deny.
        let allowed: &[&str] = match label {
            "may-be-negative offset" => &["slice-neg-or-unknown-offset"],
            _ => &["slice-use-unsupported", "raw-pointer-operation"],
        };
        assert!(
            allowed.contains(&got.as_str()),
            "{label} is not emittable today and must be refused with the \
             attribution that names WHY: expected one of {allowed:?}, got {got:?}"
        );
        assert_ne!(got, "<emitted>", "{label} must not emit");
    }
}

/// **S3.2′-5 — the sign gate on the deref-through-arithmetic positions.**
///
/// The `-2` arm authorised `*p.offset(e)` ⇒ `p[(e) as usize]` while consulting
/// no sign information at all. When `e` is negative at runtime the cast wraps to
/// a huge index and the bounds check panics: memory-safe, and a **behaviour
/// change** against a program that legitimately indexed backwards. `SignFacts`
/// shipped at `-3` read by nothing and gained its first consumer at `2b` on the
/// self-advance arm *only*; this closes the remaining position.
///
/// One sign authority, no parallel notion — the gate reads the same
/// `SignFacts::may_be_negative` verdict `advance_ok` reads at `mod.rs:1799`.
///
/// **Two-sided by construction.** The `nonneg` half is not decoration: without
/// it, a gate that degraded *every* fat arithmetic subject would pass the
/// `neg-or-unknown` half alone. Deleting the gate fails the negative half;
/// widening it to unconditional fails the positive half.
#[test]
fn a_may_be_negative_offset_refuses_the_slice_form_with_its_own_reason() {
    fn reason_for(body: &str) -> String {
        let src = format!(
            "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
             pub unsafe fn f(mut p: *mut i32, n: usize, k: isize) -> *mut i32 {{\n{body}\n}}\n"
        );
        let got = decisions_of(&src);
        reason_of(&got, "p", true)
    }

    // NEGATIVE HALF — a may-be-negative offset must be refused, and refused
    // with the reason that names the *sign*, not the op and not the use shape.
    // `k` is an unconstrained `isize` parameter, so the offset-sign lattice
    // settles `Top`, which `needs_cursor()` admits through the same door as
    // `Neg`. The taint is per-LOCAL, so one tainted position taints `p`.
    for (label, body) in [
        (
            "unbounded offset",
            "    let _v = *p.offset(k);\n    core::ptr::null_mut()",
        ),
        (
            "negative literal offset",
            "    let _v = *p.offset(-1 as isize);\n    core::ptr::null_mut()",
        ),
    ] {
        assert_eq!(
            reason_for(body),
            "slice-neg-or-unknown-offset",
            "{label}: a may-be-negative offset must degrade with its own \
             attributed reason — the op is fine and the use shape is fine, so \
             neither `raw-pointer-operation` nor `slice-use-unsupported` names \
             what actually blocked it"
        );
    }

    // POSITIVE HALF — the gate must NOT swallow the `-2` arm it is protecting.
    // `i` is `usize`, so every offset is provably non-negative and the slice
    // form still emits. This is what makes the gate a gate rather than a veto.
    assert_eq!(
        reason_for(
            "    let mut i: usize = 0;\n    let mut t = 0;\n    while i < n { t += *p.offset(i as isize); i += 1; }\n    core::ptr::null_mut()"
        ),
        "<emitted>",
        "a provably non-negative offset must still emit — the gate keys on the \
         SIGN, not on the presence of arithmetic"
    );

    // **PRECEDENCE — the gate must stay LAST in the arm.**
    //
    // The two halves above pin that the gate fires and that it is conditional;
    // neither pins WHERE. Moving it above the `SliceUseUnsupported` check would
    // leave both green while silently displacing an earlier, more specific
    // reason — the "can only convert a would-be emission" property that makes
    // its movement a pre-registered count rather than an unbounded one.
    //
    // This subject is may-be-negative AND separately unsupported (`p` is also
    // returned bare). The earlier reason must win.
    assert_eq!(
        reason_for("    let _v = *p.offset(k);\n    p"),
        "slice-use-unsupported",
        "the sign gate must fire LAST: a subject that is ALSO unsupported for \
         its use shape must keep the earlier, more specific attribution. If \
         this reads `slice-neg-or-unknown-offset`, the gate has been hoisted \
         above a reason it must never displace."
    );
}

/// **S3.2′-5 hardening — the FAT-OPTIONAL twin carries the identical hazard.**
///
/// `Form::Opt { slice: true }` reaches the same `*p.offset(e)` position through
/// `accessor[index]` (`emitability.rs:522-559`) and the same `(e) as usize`
/// rendering. Before this gate it emitted unconditionally: the plain-slice arm
/// was closed and its optional twin was not, so "one sign authority, no
/// parallel notion" was a statement about one arm rather than about the
/// emitter. Zero-expected-delta debut — all 50 optional emissions measure
/// `nonneg`, so this moves nothing on the corpus and everything in principle.
///
/// **Gated on `slice`, the narrowest arm that owns the hazard.** A thin
/// optional provably has no arithmetic — form selection admits
/// `Opt { slice: false }` only under `!has_arithmetic || is_array` with
/// `slice = has_arithmetic && is_array` — so it forms no index and the sign
/// verdict is irrelevant to it. Gating the whole arm would also degrade any
/// thin optional whose sign lookup MISSES, since `may_be_negative` folds
/// `None` conservatively. That is the 61-thin-`Ref` finding a second time.
#[test]
fn a_may_be_negative_offset_refuses_the_fat_optional_form_too() {
    fn reason_for(body: &str) -> String {
        let src = format!(
            "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
             pub unsafe fn f(mut p: *mut i32, n: usize, k: isize) -> *mut i32 {{\n{body}\n}}\n"
        );
        let got = decisions_of(&src);
        reason_of(&got, "p", true)
    }
    const NULL_TEST: &str = "    if p.is_null() { return core::ptr::null_mut(); }\n";

    // NEGATIVE — the probe that exposed the gap, now a permanent fixture.
    assert_eq!(
        reason_for(
            &[
                NULL_TEST,
                "    let _v = *p.offset(k);\n    core::ptr::null_mut()"
            ]
            .concat()
        ),
        "slice-neg-or-unknown-offset",
        "a fat OPTIONAL with a may-be-negative offset must be refused for the \
         same reason its plain twin is — the hazard is the index, and the \
         `Option` wrapper does not change it"
    );

    // POSITIVE — the fat-optional arm must still emit on a provable non-negative.
    assert_eq!(
        reason_for(&[NULL_TEST, "    let mut i: usize = 0;\n    let mut t = 0;\n    while i < n { t += *p.offset(i as isize); i += 1; }\n    core::ptr::null_mut()"].concat()),
        "<emitted>",
        "a provably non-negative fat optional must still emit"
    );

    // THIN optional — a REGRESSION PIN, **not a control**, and the difference
    // was measured rather than assumed.
    //
    // Dropping the `slice &&` conjunct leaves this assertion GREEN, so it does
    // NOT witness that conjunct. Measured reason: `SignFacts` inserts a taint
    // bit only at an offset use, and a thin optional has none, so its verdict
    // is always `Some(false)` and an ungated sign check would pass it anyway.
    // The conjunct earns its place only on a lookup MISS, where
    // `may_be_negative` folds `None` to `true` — and no fixture can produce a
    // miss, since that needs the local to outrun the analysis domain.
    //
    // So the conjunct is defense-in-depth against the conservative fold, kept
    // on the P-drop precedent (retain, and state the measurement that explains
    // why nothing exercises it) rather than deleted as unreachable. This line
    // pins that thin optionals keep emitting; it does not pretend to more.
    assert_eq!(
        reason_for(&[NULL_TEST, "    let _v = *p;\n    core::ptr::null_mut()"].concat()),
        "<emitted>",
        "a THIN optional forms no index and must keep emitting"
    );

    // PRECEDENCE — last in its own arm, same rule as the slice twin.
    assert_eq!(
        reason_for(&[NULL_TEST, "    let _v = *p.offset(k);\n    p"].concat()),
        "opt-use-unsupported",
        "the fat-optional sign gate must fire LAST in its arm: a subject that \
         is ALSO unsupported for its use shape keeps the earlier attribution"
    );
}

/// **THE DISSOLUTION'S RESIDUE WITNESS — one case per construction class**
/// (user ruling RECLASSIFY-ONLY, 2026-08-12).
///
/// Every unannotated local still degrades — the pin below is not weakened by
/// one subject — but it degrades **naming the owed capability it is waiting
/// on** rather than naming the rewriter's splice mechanism.
///
/// # Where this test came from, kept adjacent
///
/// It began as the g16 capability's decision-level witness, RED, after g19 was
/// retired for being invisible to a text golden. The work-unit then retired too
/// on **F1** — the capability emits nothing, so byte identity would have been
/// satisfied by a broken implementation exactly as well as a correct one — and
/// the witness was **inverted into a status-quo pin** asserting that all four
/// classes still degrade `no-declared-type`. The dissolution supersedes the
/// key, not the pin: all four still degrade, and each now says why.
///
/// The per-class measurement that retired the g16 step is preserved, because it
/// is exactly what decided the folds below:
///
/// | class | n | inference gives a reference? | insertion `: &T` compiles? |
/// |---|---:|---|---|
/// | `copy` | 3 | yes | compiles |
/// | `other` | 2 | yes | compiles |
/// | `call-result` | 17 | no | `E0308` |
/// | `place-read` | 1 | no | `E0308` |
///
/// `call-result` and `place-read` fail structurally: their initializer type
/// comes from a callee **return type** or a **pointee/struct field**, and
/// neither is in M1's parameters-and-locals subject universe. That is what
/// `return-not-adapted` and `place-read-pointee` now say, and it is why they
/// are owed to S3.6-5 and M3 rather than to the locals-conversion follow-up —
/// which owns only `copy-source-coupled`.
///
/// **Four classes here, all nine plus `None` in
/// `decision::tests::every_construction_class_names_an_owed_capability`.** The
/// split is deliberate: this test proves the residue gate is REACHED and wired
/// to the fold table, which needs a real program; the fold table's own
/// exhaustiveness is a pure function and is tested as one. `Alloc` in
/// particular cannot be witnessed here — BO settles a `malloc` local `Owning`
/// or `Raw`, so `kind-*` fires first and the ladder never reaches the residue,
/// which is exactly why the corpus has only one such subject.
///
/// *Mutation-tested:* deleting the residue gate ahead of the co-conversion gate
/// reports `call-site-not-adapted` for all four.
#[test]
fn every_unannotated_local_class_degrades_naming_its_owed_capability() {
    fn reason_for_q(body: &str) -> String {
        let src = format!(
            "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
             pub unsafe fn src_of() -> *mut i32 {{ core::ptr::null_mut() }}\n\
             pub unsafe fn f(p: *mut i32, pp: *mut *mut i32, n: usize) -> i32 {{\n{body}\n}}\n"
        );
        reason_of(&decisions_of(&src), "q", false)
    }

    for (label, body, want) in [
        (
            "copy",
            "    let q = p;\n    *q = 7;\n    *q",
            "copy-source-coupled",
        ),
        (
            "other",
            "    let q = if n > 0 { p } else { p };\n    *q = 7;\n    *q",
            "copy-source-coupled",
        ),
        (
            "call-result",
            "    let q = src_of();\n    *q = 7;\n    *q",
            "return-not-adapted",
        ),
        (
            "place-read",
            "    let q = *pp;\n    *q = 7;\n    *q",
            "place-read-pointee",
        ),
    ] {
        assert_eq!(
            reason_for_q(body),
            want,
            "{label}: every class of unannotated local must still degrade, and \
             must name the owed capability it waits on. If this moved, either \
             something is claiming this population without a ruling — the \
             unwitnessable ledger movement F1 refused — or a residual fold has \
             been silently rerouted."
        );
    }
}

/// **S3.6-0 — the reference KIND is recorded, one positive fixture per kind.**
///
/// The split this enables was unmeasurable before: `referenced` was one map
/// fired by any `Path` resolution to a local `fn`, keeping spans and not kinds,
/// so direct calls, address-taking and fn-pointer casts — three populations with
/// three different adaptation stories — were indistinguishable.
///
/// **Each kind gets its own positive fixture**, because a classifier witnessed
/// on one kind is a classifier witnessed on nothing: the `_ => AddrTaken`
/// fallback would swallow both others and still pass a call-only test.
///
/// `is_adaptable` is asserted alongside, since it is what the census reports and
/// what any future slicing would be scoped against.
#[test]
fn a_local_fn_reference_records_which_kind_it_is() {
    use crate::bo_rewriter::decision::emitability::RefKind;

    fn kinds_of(src: &str) -> Vec<&'static str> {
        ::utils::compilation::run_compiler_on_str(src, |tcx| {
            let program = crate::bo_rewriter::collect_program(tcx);
            let facts = crate::bo_rewriter::decision::emitability::collect(tcx, &program.functions);
            let mut out: Vec<_> = facts
                .referenced
                .iter()
                .filter(|(did, _)| tcx.def_path_str(did.to_def_id()).contains("target"))
                .flat_map(|(_, refs)| refs.iter().map(|(k, _)| k.key()))
                .collect();
            out.sort_unstable();
            out.dedup();
            out
        })
        .expect("fixture compiles")
    }
    const PRE: &str = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
                       pub unsafe fn target(p: *mut i32) -> i32 { *p }\n";

    assert_eq!(
        kinds_of(&format!(
            "{PRE}pub unsafe fn c(p: *mut i32) -> i32 {{ target(p) }}\n"
        )),
        vec!["call"],
        "a direct call must record `call` — this is the ADAPTABLE population, \
         and mislabelling it pinned would understate every future market"
    );
    assert_eq!(
        kinds_of(&format!(
            "{PRE}pub unsafe fn c() -> unsafe fn(*mut i32) -> i32 {{ target }}\n"
        )),
        vec!["addr-taken"],
        "a bare path reference must record `addr-taken` — the signature is \
         pinned by whatever consumes the value"
    );
    assert_eq!(
        kinds_of(&format!(
            "{PRE}pub unsafe fn c() -> usize {{ target as unsafe fn(*mut i32) -> i32 as usize }}\n"
        )),
        vec!["fnptr-cast"],
        "a cast operand must record `fnptr-cast` — the callback-table shape F1 \
         widened this arm for, and the one it must not be conflated with"
    );

    // `is_adaptable` is ALL-or-nothing: one pinning reference is enough.
    let span = rustc_span::DUMMY_SP;
    assert!(RefKind::is_adaptable(&[(RefKind::Call, span)]));
    assert!(!RefKind::is_adaptable(&[
        (RefKind::Call, span),
        (RefKind::AddrTaken, span)
    ]));
    assert!(
        !RefKind::is_adaptable(&[]),
        "an empty reference set is not adaptable — it is NOT REFERENCED, a \
         different population, and conflating them would count the 385 \
         already-emitting functions as an S3.6 market"
    );
}

/// **S3.6-1 task 0 — the call ARGUMENT is recorded, one fixture per shape.**
///
/// The gate that blocks the adaptable population is a *signature* fact, but
/// adapting a call site is an *argument* question, and no argument fact existed:
/// `ExprKind::Call(callee, _)` bound its arguments to `_`, discarding the index,
/// the span, the shape and the caller at the one site that could record them.
///
/// **One positive fixture per shape**, for the reason S3.6-0 recorded: a
/// classifier witnessed on one value is a classifier witnessed on nothing —
/// the `_ => Other` fallback would swallow every other arm and still pass a
/// bare-local-only test.
///
/// *Mutation-tested on a committed baseline (see the slice record):* each
/// assertion below fails under a distinct single-arm deletion in
/// `classify_arg`.
#[test]
fn a_direct_call_records_each_argument_shape() {
    fn shapes_of(src: &str) -> Vec<&'static str> {
        ::utils::compilation::run_compiler_on_str(src, |tcx| {
            let program = crate::bo_rewriter::collect_program(tcx);
            let facts = crate::bo_rewriter::decision::emitability::collect(tcx, &program.functions);
            facts
                .call_args
                .iter()
                .filter(|(did, _)| tcx.def_path_str(did.to_def_id()).contains("target"))
                .flat_map(|(_, sites)| sites.iter())
                .flat_map(|site| site.args.iter().map(|a| a.shape.key()))
                .collect()
        })
        .expect("fixture compiles")
    }
    const PRE: &str = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
                       pub unsafe fn target(p: *mut i32) { *p = 1; }\n";
    let call = |body: &str| format!("{PRE}pub unsafe fn c(q: *mut i32) {{ {body} }}\n");

    assert_eq!(shapes_of(&call("target(q)")), vec!["bare-local"]);
    assert_eq!(
        shapes_of(&call("let mut x: i32 = 0; target(&mut x)")),
        vec!["addr-of-mut"],
        "an already-written `&mut` needs NO edit — it coerces to `*mut T` today \
         and satisfies `&mut T` after, so mislabelling it would invent work"
    );
    assert_eq!(
        shapes_of(&call("let mut x: i32 = 0; target(&mut x as *mut i32)")),
        vec!["addr-of-mut-cast"],
        "the cast is the only thing to remove; conflating it with a bare cast \
         would lose the fact that the operand is ALREADY a reference"
    );
    assert_eq!(
        shapes_of(&call("target(q as *mut i32)")),
        vec!["cast-of-local"]
    );
    assert_eq!(
        shapes_of(&call("target(0 as *mut i32)")),
        vec!["null-lit"],
        "a null literal BLOCKS: `&mut T` cannot represent null (E0308, measured)"
    );
    assert_eq!(
        shapes_of(&call("target(0 as usize as *mut i32)")),
        vec!["null-lit"],
        "C2Rust also writes null through an intermediate cast — a single-level \
         test would classify this as an ordinary cast and let it past the gate"
    );
    assert_eq!(
        shapes_of(&call("target(q.offset(1))")),
        vec!["raw-expr"],
        "wave 1 admits the whole expression only because its resolved type is a raw pointer"
    );

    // The INDEX is the callee's 0-based parameter position — the same key as
    // `SubjectKind::Param { hir_index }`, so the join needs no translation.
    // Without this the census could attribute every argument to parameter 0.
    let indices = ::utils::compilation::run_compiler_on_str(
        "#![allow(dead_code, unused_unsafe, unused_variables)]\n\
         pub unsafe fn target(a: *mut i32, b: *mut i32) { *a = *b; }\n\
         pub unsafe fn c(q: *mut i32, r: *mut i32) { target(r, q); }\n",
        |tcx| {
            let program = crate::bo_rewriter::collect_program(tcx);
            let facts = crate::bo_rewriter::decision::emitability::collect(tcx, &program.functions);
            facts
                .call_args
                .iter()
                .filter(|(did, _)| tcx.def_path_str(did.to_def_id()).contains("target"))
                .flat_map(|(_, sites)| sites.iter().map(|s| s.args.len()))
                .chain(
                    facts
                        .call_args
                        .iter()
                        .filter(|(did, _)| tcx.def_path_str(did.to_def_id()).contains("target"))
                        .flat_map(|(_, sites)| sites.iter())
                        .flat_map(|s| s.args.iter().map(|a| a.index)),
                )
                .collect::<Vec<_>>()
        },
    )
    .expect("fixture compiles");
    assert_eq!(
        indices,
        vec![2, 0, 1],
        "one site, two args, indices 0 then 1"
    );
}

/// **Only DIRECT calls carry arguments** — the pinned population has none.
///
/// A function reached by a fn-pointer cast has no visible argument list, which
/// is *why* it is pinned. If this arm recorded anything for that shape, the
/// pinned 640 would appear to have an adaptation market they cannot have.
///
/// The negative is paired with a positive in ONE fixture so a mechanism that
/// records nothing at all cannot satisfy it — the g19 rule.
#[test]
fn only_direct_calls_record_arguments() {
    let (called, cast) = ::utils::compilation::run_compiler_on_str(
        "#![allow(dead_code, unused_unsafe, unused_variables)]\n\
         pub unsafe fn called(p: *mut i32) { *p = 1; }\n\
         pub unsafe fn pinned(p: *mut i32) { *p = 2; }\n\
         pub unsafe fn c(q: *mut i32) -> usize {\n\
             called(q);\n\
             pinned as unsafe fn(*mut i32) as usize\n\
         }\n",
        |tcx| {
            let program = crate::bo_rewriter::collect_program(tcx);
            let facts = crate::bo_rewriter::decision::emitability::collect(tcx, &program.functions);
            let count = |needle: &str| {
                facts
                    .call_args
                    .iter()
                    .filter(|(did, _)| tcx.def_path_str(did.to_def_id()).contains(needle))
                    .map(|(_, sites)| sites.len())
                    .sum::<usize>()
            };
            (count("called"), count("pinned"))
        },
    )
    .expect("fixture compiles");

    assert_eq!(called, 1, "the direct call must be recorded");
    assert_eq!(
        cast, 0,
        "a fn-pointer cast supplies NO arguments — recording one would give the \
         pinned population a market it cannot have"
    );
}

/// **S3.6-1 task 0a — a borrowed argument records its PLACE ROOT.**
///
/// The within-site overlap gate must block a call site where two pointer
/// parameters receive *overlapping* places, and overlap is not textual
/// identity. The corpus witness is brotli's
/// `BrotliDecoderHuffmanTreeGroupInit(s, &mut (*s).literal_hgroup, …)`
/// (`brotli/lib.rs:113893`): parameter 0 gets `s`, parameter 1 gets a place
/// **inside `*s`**, both declared `*mut`, certain overlap. `heman`'s
/// `kmVec3Normalize(pOut, pOut)` (×7) is the easy case — same binding — and a
/// gate built only for it would miss brotli entirely.
///
/// So the assertion is not "a root is recorded" but **"the two arguments share
/// the same root"**, which is the question the gate actually asks.
#[test]
fn a_borrowed_argument_records_the_place_it_is_rooted_at() {
    fn roots_match(src: &str) -> (bool, usize) {
        ::utils::compilation::run_compiler_on_str(src, |tcx| {
            let program = crate::bo_rewriter::collect_program(tcx);
            let facts = crate::bo_rewriter::decision::emitability::collect(tcx, &program.functions);
            let site = facts
                .call_args
                .iter()
                .find(|(did, _)| tcx.def_path_str(did.to_def_id()).contains("target"))
                .map(|(_, sites)| sites[0].clone())
                .expect("the call site is recorded");
            let roots: Vec<_> = site.args.iter().map(|a| a.shape.place_root()).collect();
            let known = roots.iter().filter(|r| r.is_some()).count();
            (
                roots.len() == 2 && roots[0].is_some() && roots[0] == roots[1],
                known,
            )
        })
        .expect("fixture compiles")
    }

    // The brotli shape: a bare binding, and a borrow of a place INSIDE it.
    let (overlap, known) = roots_match(
        "#![allow(dead_code, unused_unsafe, unused_variables)]\n\
         pub struct Grp { pub n: i32 }\n\
         pub struct St { pub g: Grp }\n\
         pub unsafe fn target(s: *mut St, g: *mut Grp) { (*g).n = 1; let _ = s; }\n\
         pub unsafe fn c(s: *mut St) { target(s, &mut (*s).g); }\n",
    );
    assert_eq!(known, 2, "both arguments must resolve a root");
    assert!(
        overlap,
        "`s` and `&mut (*s).g` must share a place root — this is brotli's \
         BrotliDecoderHuffmanTreeGroupInit shape, certain overlap at two *mut \
         positions, and a gate that cannot see it spends a revert instead of \
         avoiding one"
    );

    // The NEGATIVE, so the test cannot be satisfied by returning one constant
    // root for everything: two genuinely distinct bases must NOT match.
    let (overlap_distinct, known_distinct) = roots_match(
        "#![allow(dead_code, unused_unsafe, unused_variables)]\n\
         pub struct Grp { pub n: i32 }\n\
         pub struct St { pub g: Grp }\n\
         pub unsafe fn target(s: *mut St, g: *mut Grp) { (*g).n = 1; let _ = s; }\n\
         pub unsafe fn c(s: *mut St, t: *mut St) { target(s, &mut (*t).g); }\n",
    );
    assert_eq!(known_distinct, 2);
    assert!(
        !overlap_distinct,
        "distinct bases must not share a root — a gate that reported overlap \
         for everything would block the whole adaptable population"
    );
}

/// **S3.6-1 task 2 — co-conversion class witnesses.**
///
/// At the file tail, per the convention `cc849953` established for the census
/// module: the harness above is shared, and a test module wedged into the
/// middle of it reads as part of the harness.
mod coconv_witnesses {
    use std::collections::BTreeMap;

    use super::Fixture;

    /// The census, parsed BY HEADER NAME.
    ///
    /// Never by position: adding the `fatness` column at S3.2′-1 shifted every
    /// later index and broke a positional reader. A positional read is a latent
    /// break for every future column.
    fn census(src: &str) -> Vec<BTreeMap<String, String>> {
        let fixture = Fixture::new(&[("lib.rs", src)]);
        let tsv = ::utils::compilation::run_compiler_on_path(&fixture.0.join("lib.rs"), |tcx| {
            crate::bo_rewriter::coconv_tsv(tcx).expect("co-conversion census")
        })
        .expect("fixture compiles");
        let hdr: Vec<String> = tsv
            .lines()
            .next()
            .expect("header")
            .split('\t')
            .map(str::to_owned)
            .collect();
        tsv.lines()
            .skip(1)
            .map(|line| {
                hdr.iter()
                    .cloned()
                    .zip(line.split('\t').map(str::to_owned))
                    .collect()
            })
            .collect()
    }

    fn raw_trace(src: &str) -> super::super::RawBoundaryArtifacts {
        ::utils::compilation::run_compiler_on_str(src, |tcx| {
            super::super::raw_boundary_trace_artifacts(tcx).expect("raw-boundary trace")
        })
        .expect("trace fixture compiles")
    }

    fn tsv_rows(tsv: &str) -> Vec<BTreeMap<String, String>> {
        let header = tsv
            .lines()
            .next()
            .expect("TSV header")
            .split('\t')
            .map(str::to_owned)
            .collect::<Vec<_>>();
        tsv.lines()
            .skip(1)
            .map(|line| {
                header
                    .iter()
                    .cloned()
                    .zip(line.split('\t').map(str::to_owned))
                    .collect()
            })
            .collect()
    }

    fn raw_receipt<'a>(
        rows: &'a [BTreeMap<String, String>],
        identity: &str,
    ) -> &'a BTreeMap<String, String> {
        rows.iter()
            .find(|row| row["subject_identity"] == identity)
            .unwrap_or_else(|| panic!("no raw-boundary receipt for {identity}: {rows:#?}"))
    }

    #[test]
    fn task90_c1_receipt_trace_dump() {
        let cases = [
            (
                "flows-into-raw-param",
                format!(
                    "{PRE}pub unsafe fn sink(p: *mut i32) -> usize {{ p as usize }}\n\
                     pub unsafe fn src(r: *mut i32) -> usize {{ *r = 1; sink(r) }}\n"
                ),
            ),
            (
                "flows-into-other-form",
                format!(
                    "{PRE}pub unsafe fn opty(o: *mut i32) -> i32 {{ if o.is_null() {{ 0 }} else {{ *o }} }}\n\
                     pub unsafe fn feeder(r: *mut i32) -> i32 {{ *r = 1; opty(r) }}\n"
                ),
            ),
            (
                "borrowed-into-raw-param",
                format!(
                    "{PRE}pub unsafe fn sink(p: *mut i32) -> usize {{ p as usize }}\n\
                     pub unsafe fn src(r: *mut i32) -> usize {{ *r = 1; sink(&mut *r) }}\n"
                ),
            ),
            (
                "escapes-via-foreign-arg",
                format!(
                    "{PRE}extern \"C\" {{ fn sink(p: *mut i32); }}\n\
                     pub unsafe fn subject(p: *mut i32) {{ *p = 1; sink(p); }}\n"
                ),
            ),
        ];
        for (name, source) in cases {
            let trace = raw_trace(&source);
            eprintln!("TRACE {name} SUBJECTS\n{}", trace.subjects);
            eprintln!("TRACE {name} DISPOSITIONS\n{}", trace.dispositions);
        }
    }

    /// One row, found by the `fn_path` suffix and MIR local.
    fn row<'a>(
        rows: &'a [BTreeMap<String, String>],
        f: &str,
        local: u32,
    ) -> &'a BTreeMap<String, String> {
        rows.iter()
            .find(|r| r["fn_path"].ends_with(f) && r["mir_local"] == local.to_string())
            .unwrap_or_else(|| {
                panic!(
                    "no census row for {f}::_{local}; rows: {:?}",
                    rows.iter()
                        .map(|r| (r["fn_path"].clone(), r["mir_local"].clone()))
                        .collect::<Vec<_>>()
                )
            })
    }

    const PRE: &str = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n";

    /// **The chain is ONE class.** g20's shape, at the decision level.
    ///
    /// `g20_bump(q)` inside `g20_via` joins the callee's parameter to the
    /// caller's, and converting either alone is `E0308` (H5, measured). The
    /// class is what makes it one decision.
    ///
    /// *Mutation-tested (deletion first):* deleting the `dsu.union` in the
    /// `BareLocal` arm leaves two singleton classes and fails on the class
    /// identity **and** on `class_size`.
    #[test]
    fn a_bare_local_argument_joins_callee_and_caller_into_one_class() {
        let rows = census(&format!(
            "{PRE}pub unsafe fn g20_bump(p: *mut i32) -> i32 {{ *p += 1; *p }}\n\
             pub unsafe fn g20_via(q: *mut i32) -> i32 {{ g20_bump(q) }}\n\
             pub unsafe fn g20_root() -> i32 {{ let mut x: i32 = 0; g20_via(&mut x) }}\n"
        ));
        let bump = row(&rows, "g20_bump", 1);
        let via = row(&rows, "g20_via", 1);
        assert_ne!(
            bump["class_id"], "-",
            "the callee parameter must be a node: {bump:?}"
        );
        assert_eq!(
            bump["class_id"], via["class_id"],
            "callee and caller must land in ONE class — converting either alone \
             is E0308: {bump:?} vs {via:?}"
        );
        assert_eq!(bump["class_size"], "2", "{bump:?}");
        assert_eq!(
            bump["admissible"], "1",
            "every argument in this chain is compatible, so the class converts: \
             {bump:?}"
        );
    }

    /// **R165-2 PAIR:** a duplicated argument keeps one safe primary and one
    /// raw-view position, without affecting the clean class beside it.
    ///
    /// The two aliased formal positions must split deterministically; treating
    /// both as safe recreates E0499, while blocking unconditionally loses the
    /// ruled T2 fallback and also fails on `g21_ok`.
    #[test]
    fn pair_w1_duplicated_argument_selects_primary_and_raw_view() {
        let rows = census(&format!(
            "{PRE}pub unsafe fn g21_ok(p: *mut i32) {{ *p = 1; }}\n\
             pub unsafe fn g21_aliased(a: *mut i32, b: *mut i32) {{ *a += *b; }}\n\
             pub unsafe fn g21_clean() {{ let mut x: i32 = 0; g21_ok(&mut x); }}\n\
             pub unsafe fn g21_dirty(q: *mut i32) {{ g21_aliased(q, q); }}\n"
        ));
        let ok = row(&rows, "g21_ok", 1);
        let a = row(&rows, "g21_aliased", 1);
        let b = row(&rows, "g21_aliased", 2);
        assert_eq!(
            a["admissible"], "1",
            "the canonical primary must stay safe: {a:?}"
        );
        assert_eq!(b["admissible"], "0", "the peer must be the raw view: {b:?}");
        assert_eq!(b["node_block"], "duplicate-place-root", "{b:?}");
        assert_eq!(
            ok["admissible"], "1",
            "a blocked class must not take the clean one with it — one blocked \
             MEMBER blocks its own class, not the crate: {ok:?}"
        );
    }

    /// **D4-W1 — one blocked member no longer blocks a clean sibling.**
    ///
    /// `g21_dirty::q` supplies both aliased positions, so the edge pulls it
    /// into the blocked component. Its own arguments are unobjectionable; it is
    /// blocked by transitivity, which is the property that makes a class the
    /// unit of decision.
    #[test]
    fn d4_w1_blocked_member_does_not_block_clean_sibling() {
        // TWO call sites of one callee: `via` supplies a clean bare local, and
        // `nulls` supplies a null literal. The null blocks `t::p`, and `via::x`
        // — whose own argument is unobjectionable — is blocked with it.
        //
        // The `aliased(q, q)` shape cannot witness this: BO itself refuses the
        // doubly-passed binding, so `q` is not a node and there is no edge to
        // carry the block. Measured, and recorded rather than worked around.
        let rows = census(&format!(
            "{PRE}pub unsafe fn t(p: *mut i32) {{ *p = 1; }}\n\
             pub unsafe fn via(x: *mut i32) {{ t(x); }}\n\
             pub unsafe fn nulls() {{ t(0 as *mut i32); }}\n"
        ));
        let p = row(&rows, "t", 1);
        let x = row(&rows, "via", 1);
        assert_eq!(p["class_id"], x["class_id"], "{p:?} vs {x:?}");
        assert_eq!(p["node_block"], "arg-null-literal", "{p:?}");
        assert_eq!(p["member_admissible"], "0", "{p:?}");
        assert_eq!(x["member_admissible"], "1", "{x:?}");
        assert_eq!(x["edge_routes"], "arm-a", "{x:?}");
        assert_eq!(
            x["node_block"], "-",
            "`x` contributes no blocker of its own and must decide independently: {x:?}"
        );
    }

    /// D4-W2 — every directed edge gets a typed route rather than inheriting a
    /// class-wide verdict. The ordinary chain is zero-syntax; the optional
    /// target is GLUE territory rather than a reason to demote its safe source.
    #[test]
    fn d4_w2_directed_edges_name_zero_and_glue_routes() {
        let zero = census(&format!(
            "{PRE}pub unsafe fn target(p: *mut i32) {{ *p = 1; }}\n\
             pub unsafe fn caller(q: *mut i32) {{ target(q); }}\n"
        ));
        assert_eq!(row(&zero, "caller", 1)["edge_routes"], "zero-syntax");

        let glue = census(&format!(
            "{PRE}pub unsafe fn optional(p: *mut i32) -> i32 {{ if p.is_null() {{ 0 }} else {{ *p }} }}\n\
             pub unsafe fn caller(q: *mut i32) -> i32 {{ *q = 1; optional(q) }}\n"
        ));
        let q = row(&glue, "caller", 1);
        assert_eq!(q["member_admissible"], "1", "{q:?}");
        assert_eq!(q["edge_routes"], "glue", "{q:?}");
    }

    #[test]
    fn d4_w1_production_keeps_clean_sibling_safe() {
        let source = format!(
            "{PRE}pub unsafe fn target(p: *mut i32) {{ *p = 1; }}\n\
             pub unsafe fn via(x: *mut i32) {{ target(x); }}\n\
             pub unsafe fn nulls() {{ target(0 as *mut i32); }}\n"
        );
        let super::super::RewriteOutcome::Emitted { source, .. } =
            super::super::rewrite_m1(&source)
        else {
            panic!("D4-W1 production fixture must emit")
        };
        assert!(source.contains("fn via(x: &mut i32)"), "{source}");
        assert!(source.contains("fn target(p: *mut i32)"), "{source}");
    }

    #[test]
    fn d4_w2_production_emits_safe_to_safe_glue() {
        let source = format!(
            "{PRE}pub unsafe fn optional(p: *mut i32) -> i32 {{ if p.is_null() {{ 0 }} else {{ *p }} }}\n\
             pub unsafe fn caller(q: *mut i32) -> i32 {{ *q = 1; optional(q) }}\n"
        );
        let super::super::RewriteOutcome::Emitted { source, .. } =
            super::super::rewrite_m1(&source)
        else {
            panic!("D4-W2 production fixture must emit")
        };
        assert!(source.contains("fn caller(q: &mut i32)"), "{source}");
        assert!(source.contains("optional(Some(q))"), "{source}");
    }

    #[test]
    fn d4_edge_receipt_carries_both_subject_identities() {
        let source = format!(
            "{PRE}pub unsafe fn target(p: *mut i32) {{ *p = 1; }}\n\
             pub unsafe fn caller(q: *mut i32) {{ target(q); }}\n"
        );
        let trace = raw_trace(&source);
        let rows = tsv_rows(&trace.d4_edges);
        let row = rows.first().expect("one D4 edge");
        assert_eq!(row["source_subject"], "caller::q#1", "{row:?}");
        assert_eq!(row["target_subject"], "target::p#1", "{row:?}");
    }

    #[test]
    fn d4_cycle_edges_are_all_receipted_and_zero_syntax() {
        let rows = census(&format!(
            "{PRE}pub unsafe fn a(p: *mut i32, n: i32) {{ if n > 0 {{ b(p, n - 1); }} }}\n\
             pub unsafe fn b(p: *mut i32, n: i32) {{ if n > 0 {{ a(p, n - 1); }} }}\n"
        ));
        for function in ["a", "b"] {
            let row = row(&rows, function, 1);
            assert_eq!(row["member_admissible"], "1", "{row:?}");
            assert_eq!(row["edge_routes"], "zero-syntax", "{row:?}");
            assert_eq!(row["required_arms"], "d4", "{row:?}");
        }
    }

    /// **The argument-shape table, one fixture per blocking shape — and a
    /// negative for the shape that does NOT block.**
    ///
    /// One shape per case for the reason task 0 recorded: a classifier
    /// witnessed on one value is witnessed on nothing, because a single
    /// catch-all arm would satisfy every positive case at once. The `&mut e`
    /// row is what stops "block everything" from passing.
    #[test]
    fn each_blocking_argument_shape_has_its_own_reason() {
        let case = |arg: &str| {
            let rows = census(&format!(
                "{PRE}pub unsafe fn target(p: *mut i32) {{ *p = 1; }}\n\
                 pub unsafe fn caller() {{ let mut x: i32 = 0; let _ = &mut x; target({arg}); }}\n"
            ));
            row(&rows, "target", 1)
                .get("class_block")
                .cloned()
                .unwrap_or_default()
        };
        assert_eq!(case("0 as *mut i32"), "arg-null-literal");
        assert_eq!(case("(&mut x) as *mut i32"), "arg-cast-form-unbuilt");
        assert_eq!(
            case("1usize as *mut i32"),
            "-",
            "a resolved raw expression is a wave-1 adapter source; no spelling heuristic blocks it"
        );
        assert_eq!(
            case("&mut x"),
            "-",
            "`&mut e` already coerces both ways and needs no edit — a table \
             that blocked it would block the second-largest shape in the corpus"
        );
    }

    /// **A shared borrow into a `&mut` position blocks.**
    ///
    /// Split from the table above because it is the one row whose verdict
    /// depends on the SUBJECT's mutability rather than on the argument alone.
    #[test]
    fn a_shared_borrow_into_a_mutable_position_blocks() {
        let rows = census(&format!(
            "{PRE}pub unsafe fn target(p: *mut i32) {{ *p = 1; }}\n\
             pub unsafe fn caller() {{ let x: i32 = 0; target(&x as *const i32 as *mut i32); }}\n\
             pub unsafe fn shared(p: *mut i32) -> i32 {{ *p }}\n\
             pub unsafe fn ok() {{ let x: i32 = 0; shared(&x as *const i32 as *mut i32); }}\n"
        ));
        // Both go through a cast, so both read the cast reason; what this pins
        // is that a *const-rooted argument never silently satisfies a `&mut`
        // position.
        assert_eq!(row(&rows, "target", 1)["admissible"], "0");
    }

    /// A converting binding that reaches a raw parameter opens only through
    /// its exact confirmed-T2 boundary receipt.
    ///
    /// `&mut T → *mut T` is an implicit coercion, so this compiles at exit 0
    /// and produces no counter movement at all (§5a, measured). The verify loop
    /// cannot absorb it as a revert because there is nothing to absorb. The
    /// receipt assertions below are therefore load-bearing.
    ///
    /// *Mutation-tested (deletion first):* deleting the caller-side arm leaves
    /// `src::r` admissible and fails here — and it fails SILENTLY in
    /// production, which is the reason the witness exists.
    #[test]
    fn a_converting_binding_into_a_raw_parameter_opens_only_with_confirmed_t2_receipt() {
        let source = format!(
            "{PRE}pub unsafe fn sink(p: *mut i32) -> usize {{ p.read() as usize }}\n\
             pub unsafe fn src(r: *mut i32) -> usize {{ *r = 1; sink(r) }}\n"
        );
        let rows = census(&source);
        let sink = row(&rows, "sink", 1);
        let src = row(&rows, "src", 1);
        assert_eq!(
            sink["class_id"], "-",
            "`sink`'s parameter is `as`-cast, so it stays raw and is not a \
             node — if it converted, this fixture would witness nothing: {sink:?}"
        );
        assert_eq!(src["node_block"], "-", "{src:?}");
        assert_eq!(src["admissible"], "1", "{src:?}");
        let trace = raw_trace(&source);
        let receipts = tsv_rows(&trace.dispositions);
        let receipt = raw_receipt(&receipts, "src::r#1");
        assert_eq!(receipt["tier"], "T2", "{receipt:?}");
        assert_eq!(receipt["template"], "ref-mut-to-raw-mut", "{receipt:?}");
        assert_eq!(receipt["target_stays_raw"], "1", "{receipt:?}");
        assert_eq!(
            receipt["waiver_id"],
            super::super::decision::raw_boundary::RAW_BOUNDARY_WAIVER_ID,
            "{receipt:?}"
        );
    }

    /// **D4-W2: a converting binding into a differently-formed SAFE parameter
    /// becomes a GLUE edge**, rather than demoting the whole class.
    ///
    /// `&mut T` into `*mut T` coerces silently and is caught here or nowhere.
    /// `&mut T` into `Option<&i32>` is `E0308` — the compiler catches it, so it
    /// costs a revert rather than soundness. Banked rule 1 is exactly that
    /// distinction, and a census reporting both as `flows-into-raw-param` files
    /// a checked risk under an unchecked reason.
    ///
    /// *Mutation-tested:* restoring the old class-wide reason makes
    /// `member_admissible` zero and removes the GLUE receipt.
    #[test]
    fn d4_w2_differently_formed_parameter_is_a_glue_edge() {
        let source = format!(
            "{PRE}pub unsafe fn opty(o: *mut i32) -> i32 {{ if o.is_null() {{ 0 }} else {{ *o }} }}\n\
             pub unsafe fn feeder(r: *mut i32) -> i32 {{ *r = 1; opty(r) }}\n"
        );
        let rows = census(&source);
        let o = row(&rows, "opty", 1);
        let r = row(&rows, "feeder", 1);
        assert_eq!(
            o["class_id"], "-",
            "`opty`'s parameter takes the OPTIONAL form, so it is not a class \
             node — if it were a plain `Ref` this fixture witnesses nothing: {o:?}"
        );
        assert_eq!(r["node_block"], "-", "{r:?}");
        assert_eq!(r["member_admissible"], "1", "{r:?}");
        assert_eq!(r["edge_routes"], "glue", "{r:?}");
        assert_eq!(r["required_arms"], "glue", "{r:?}");
        let trace = raw_trace(&source);
        let receipts = tsv_rows(&trace.dispositions);
        let receipt = raw_receipt(&receipts, "feeder::r#1");
        assert_eq!(receipt["tier"], "T2", "{receipt:?}");
        assert_eq!(receipt["target_stays_raw"], "0", "{receipt:?}");
        assert_eq!(receipt["atom_group"], "-", "{receipt:?}");
    }

    /// **The PINNED population is excluded structurally, not in prose.**
    ///
    /// A function reached by a fn-pointer cast has its signature fixed by every
    /// table it appears in, and the pinned 640 are deferred to M2/M3. The
    /// hypothetical the class builder asks about is
    /// `RefGate::LiftAdaptable` — not `Lift` — so a pinned parameter is never a
    /// node and cannot enter a class.
    ///
    /// **PAIRED** with an adaptable callee in the same crate: a builder that
    /// produced no nodes at all would satisfy the pinned half by itself.
    #[test]
    fn a_pinned_callee_contributes_no_class_nodes_without_attestation() {
        let source = format!(
            "{PRE}pub unsafe fn pinned(p: *mut i32) {{ *p = 1; }}\n\
             pub unsafe fn adaptable(p: *mut i32) {{ *p = 2; }}\n\
             pub unsafe fn tbl() -> usize {{ pinned as unsafe fn(*mut i32) as usize }}\n\
             pub unsafe fn call() {{ let mut x: i32 = 0; adaptable(&mut x); }}\n"
        );
        let rows = census(&source);
        assert_eq!(
            row(&rows, "pinned", 1)["class_id"],
            "-",
            "an unattested fn-pointer-cast callee must contribute no node"
        );
        assert_ne!(
            row(&rows, "adaptable", 1)["class_id"],
            "-",
            "the adaptable callee in the SAME crate must be a node, or the \
             pinned assertion is satisfied by a builder that produces nothing"
        );
    }

    /// **P1 — non-boundary escape shapes block under their OWN reasons.**
    ///
    /// Return, field, and static stores remain conservative. Addendum 139
    /// migrates only the exact foreign site carrying the asserted T2 receipt.
    ///
    /// **Paired with a non-escaping node in the same crate** — a gate that
    /// blocked everything would satisfy every positive case at once.
    ///
    /// *Mutation-tested (deletion first):* deleting the escape loop makes each
    /// of these read `-` and fails.
    #[test]
    fn escape_shapes_stay_conservative_except_the_receipted_foreign_boundary() {
        // One whole source per case: the shapes need different signatures, and
        // splicing a signature through a helper is how the first draft of this
        // fixture produced a crate that did not compile.
        const HDR: &str = "extern \"C\" { fn sink(p: *mut i32); }\n\
             pub struct S { pub f: *mut i32 }\n\
             pub static mut G: *mut i32 = 0 as *mut i32;\n\
             pub unsafe fn safe_one(k: *mut i32) { *k = 9; }\n";
        let case = |sig: &str| {
            let rows = census(&format!("{PRE}{HDR}{sig}"));
            (
                row(&rows, "subject", 1)["node_block"].clone(),
                row(&rows, "safe_one", 1)["admissible"].clone(),
            )
        };
        let cases = [
            (
                "pub unsafe fn subject(p: *mut i32) -> *mut i32 { *p = 1; return p; }\n",
                "escapes-via-return",
            ),
            (
                "pub unsafe fn subject(p: *mut i32) { *p = 1; sink(p); }\n",
                "escapes-via-foreign-arg",
            ),
            (
                "pub unsafe fn subject(p: *mut i32, s: *mut S) { *p = 1; (*s).f = p; }\n",
                "escapes-via-field-store",
            ),
            (
                "pub unsafe fn subject(p: *mut i32) { *p = 1; G = p; }\n",
                "escapes-via-static-store",
            ),
        ];
        for (sig, expected) in cases {
            let (blocked, beside) = case(sig);
            if expected == "escapes-via-foreign-arg" {
                assert_eq!(blocked, "-", "for {sig}");
                let source = format!("{PRE}{HDR}{sig}");
                let trace = raw_trace(&source);
                let receipts = tsv_rows(&trace.dispositions);
                let receipt = raw_receipt(&receipts, "subject::p#1");
                assert_eq!(receipt["tier"], "T2", "{receipt:?}");
                assert_eq!(receipt["template"], "ref-mut-to-raw-mut", "{receipt:?}");
                assert_eq!(receipt["target_stays_raw"], "1", "{receipt:?}");
                assert_eq!(
                    receipt["waiver_id"],
                    super::super::decision::raw_boundary::RAW_BOUNDARY_WAIVER_ID,
                    "{receipt:?}"
                );
            } else {
                assert_eq!(blocked, expected, "for {sig}");
            }
            assert_eq!(
                beside, "1",
                "the non-escaping node beside it must stay admissible, or the \
                 gate is satisfied by blocking everything: {sig}"
            );
        }
    }

    /// A BORROW of a converting binding into a raw parameter opens only at its
    /// exact confirmed-T2 site.
    ///
    /// `f(&mut *r)` today reborrows a raw pointer; after `r` converts it
    /// reborrows a **reference**, so the raw pointer the callee retains can
    /// outlive the borrow. The conversion changes the case's character, which
    /// is what puts it inside banked rule 2 — the gap the adversarial review
    /// named, and the one the record did not previously cover.
    ///
    /// **Its own reason, not `flows-into-raw-param`**: the argument is a
    /// reborrow rather than the binding, so it forms no class edge and the
    /// owed repair differs.
    #[test]
    fn a_borrow_into_a_raw_parameter_opens_only_with_confirmed_t2_receipt() {
        let source = format!(
            "{PRE}pub unsafe fn sink(p: *mut i32) -> usize {{ p.read() as usize }}\n\
             pub unsafe fn src(r: *mut i32) -> usize {{ *r = 1; sink(&mut *r) }}\n"
        );
        let rows = census(&source);
        assert_eq!(
            row(&rows, "sink", 1)["class_id"],
            "-",
            "the callee parameter must stay raw, or the fixture witnesses nothing"
        );
        assert_eq!(row(&rows, "src", 1)["node_block"], "-");
        assert_eq!(row(&rows, "src", 1)["admissible"], "1");
        let trace = raw_trace(&source);
        let receipts = tsv_rows(&trace.dispositions);
        let receipt = raw_receipt(&receipts, "src::r#1");
        assert_eq!(receipt["tier"], "T2", "{receipt:?}");
        assert_eq!(receipt["template"], "ref-mut-to-raw-mut", "{receipt:?}");
        assert_eq!(receipt["target_stays_raw"], "1", "{receipt:?}");
        assert_eq!(
            receipt["waiver_id"],
            super::super::decision::raw_boundary::RAW_BOUNDARY_WAIVER_ID,
            "{receipt:?}"
        );
    }

    /// **P2's visibility split — the same expression is checked or blind
    /// depending on whether its BASE converts.**
    ///
    /// §5a measured it on the pinned toolchain: `init(s, &mut (*s).g)` with a
    /// REFERENCE base is `E0499` ×2 — caught — while the same shape over a raw
    /// base compiles with zero diagnostics. So `through_deref` alone does not
    /// decide blindness; the base's own fate does, and that is why the flag had
    /// to be recorded rather than inferred from the shape.
    ///
    /// This pins the FACT the split rests on. It reads the two measurement
    /// columns, which are `-` for a non-node and therefore never a verdict on
    /// a subject that is not in a class.
    ///
    /// *Mutation-tested (deletion first):* making `blind` ignore
    /// `converts.contains(base)` collapses the two columns together and fails.
    #[test]
    fn a_borrow_through_a_converting_base_is_not_compiler_blind() {
        let rows = census(&format!(
            "{PRE}pub struct S {{ pub g: i32 }}\n\
             pub unsafe fn init(s: *mut S, g: *mut i32) {{ *g = 1; (*s).g = 2; }}\n\
             pub unsafe fn c(s: *mut S) {{ init(s, &mut (*s).g); }}\n"
        ));
        let hdr_present =
            rows[0].contains_key("p2_blind_only") && rows[0].contains_key("p2_all_pairs");
        assert!(hdr_present, "the P2 measurement columns must be exported");
        // The contained-place site: `s` and a place inside `*s` at two pointer
        // positions. Under EVERY rule this pair must block -- the roots are the
        // same binding, so it is not the split that catches it.
        let init_s = row(&rows, "init", 1);
        if init_s["class_id"] != "-" {
            assert_eq!(
                init_s["p2_all_pairs"], "0",
                "maximal conservatism must block a same-root mutable pair: {init_s:?}"
            );
        }
    }

    /// **RETIRED and REPLACED — the task-2 zero-delta pin.**
    ///
    /// `an_admissible_class_moves_no_decision_at_task_two` asserted that the
    /// production ladder still degraded `call-site-not-adapted` for an
    /// admissible class. Its own recorded mutation note read: *"switching the
    /// production `decide` call to `LiftAdaptable` makes the reason `-` and
    /// fails here. That mutation is exactly task 3."*
    ///
    /// Step 3 **is** that mutation. The pin fired precisely as designed and its
    /// era ended, so it is retired openly rather than edited into agreement —
    /// the g19 rule. What replaces it is the lift-era invariant stated
    /// positively, under **its own name**, so nothing pretends to be the old
    /// pin still holding.
    ///
    /// *Mutation-tested (deletion first):* the recorded mutation reverted
    /// production to `RefGate::BlockAll`, which made the chain degrade again and
    /// failed this. ⚠ **That variant was deleted at M-3 as measured-dead, so the
    /// mutation is no longer performable as written**; the equivalent today is to
    /// make `RefKind::is_adaptable` return `false`, which blocks every reference
    /// and reproduces the same failure.
    #[test]
    fn an_admissible_class_converts_after_the_lift() {
        let rows = census(&format!(
            "{PRE}pub unsafe fn g20_bump(p: *mut i32) -> i32 {{ *p += 1; *p }}\n\
             pub unsafe fn g20_via(q: *mut i32) -> i32 {{ g20_bump(q) }}\n\
             pub unsafe fn g20_root() -> i32 {{ let mut x: i32 = 0; g20_via(&mut x) }}\n"
        ));
        let bump = row(&rows, "g20_bump", 1);
        assert_eq!(bump["admissible"], "1", "{bump:?}");

        let src = format!(
            "{PRE}pub unsafe fn g20_bump(p: *mut i32) -> i32 {{ *p += 1; *p }}\n\
             pub unsafe fn g20_via(q: *mut i32) -> i32 {{ g20_bump(q) }}\n\
             pub unsafe fn g20_root() -> i32 {{ let mut x: i32 = 0; g20_via(&mut x) }}\n"
        );
        let fixture = Fixture::new(&[("lib.rs", &src)]);
        let reasons =
            ::utils::compilation::run_compiler_on_path(&fixture.0.join("lib.rs"), |tcx| {
                let table = crate::bo_rewriter::decide_table(tcx).expect("table");
                crate::bo_rewriter::artifact::rows(tcx, &table)
                    .iter()
                    .filter_map(|r| r.degrade_reason.clone())
                    .collect::<Vec<_>>()
            })
            .expect("fixture compiles");
        assert!(
            !reasons.iter().any(|r| r == "call-site-not-adapted"),
            "the lift must retire call-site-not-adapted for an admissible \
             class: {reasons:?}"
        );
    }
}

/// **S3.6-1 task 2 — the attribution repair, and the escape census.**
mod attribution_and_escapes {
    use std::{
        collections::{BTreeMap, BTreeSet},
        path::Path,
    };

    use super::Fixture;
    use crate::bo_rewriter::{
        AttributionRule, EditSite, EmittedSite, attribute, attribute_with_rule,
        bridge_receipt::SignatureClassId,
        edit_sites,
        plan::{Edit, FileKey, Justification, Plan},
        verify::{Diag, Direction},
    };

    fn class(did: rustc_hir::def_id::LocalDefId) -> SignatureClassId {
        SignatureClassId::of(did)
    }

    fn diag(file: &str, line: usize) -> Diag {
        Diag {
            file: file.to_owned(),
            line,
            column: 1,
            end_line: line,
            end_column: 1,
            message: "mismatched types".to_owned(),
            direction: Direction::RawIntoRewritten,
            code: Some("E0308".to_owned()),
            related: Vec::new(),
        }
    }

    #[test]
    fn cls_w2_and_rule_precedence_keep_exact_class_sets() {
        assert_eq!(
            AttributionRule::ALL.map(AttributionRule::key),
            [
                "exact-edit",
                "exact-seam",
                "related-span",
                "enclosing-region",
                "unresolved",
            ]
        );
        let fixture = Fixture::new(&[("lib.rs", "pub fn class_a() {}\npub fn class_b() {}\n")]);
        ::utils::compilation::run_compiler_on_path(&fixture.0.join("lib.rs"), |tcx| {
            let mut classes = tcx
                .hir_body_owners()
                .map(|did| class(did))
                .collect::<Vec<_>>();
            classes.sort();
            let [left, right] = classes.as_slice() else { panic!("two class fixture") };
            let root = Path::new("/crate");
            let sites = [EmittedSite {
                owner_class: *left,
                file: "/crate/caller.rs".to_owned(),
                fn_path: "display-only".to_owned(),
                lo_line: 30,
                hi_line: 35,
            }];
            let edits = [
                EditSite {
                    owner_class: Some(*left),
                    file: "/crate/caller.rs".to_owned(),
                    fn_path: "same-display".to_owned(),
                    lo_line: 10,
                    lo_column: 1,
                    hi_line: 10,
                    hi_column: usize::MAX,
                    edit_id: "ordinary".to_owned(),
                    site_kind: "subject-declaration",
                    atom_ids: Vec::new(),
                    atom_covered: false,
                },
                EditSite {
                    owner_class: Some(*right),
                    file: "/crate/caller.rs".to_owned(),
                    fn_path: "same-display".to_owned(),
                    lo_line: 20,
                    lo_column: 1,
                    hi_line: 20,
                    hi_column: usize::MAX,
                    edit_id: "callee-seam".to_owned(),
                    site_kind: "seam-adapter",
                    atom_ids: Vec::new(),
                    atom_covered: false,
                },
                EditSite {
                    owner_class: Some(*right),
                    file: "/crate/caller.rs".to_owned(),
                    fn_path: "same-display".to_owned(),
                    lo_line: 21,
                    lo_column: 1,
                    hi_line: 21,
                    hi_column: usize::MAX,
                    edit_id: "mir-interface-inventory".to_owned(),
                    site_kind: "interface-inventory-site",
                    atom_ids: Vec::new(),
                    atom_covered: false,
                },
                EditSite {
                    owner_class: Some(*left),
                    file: "/crate/caller.rs".to_owned(),
                    fn_path: "left".to_owned(),
                    lo_line: 40,
                    lo_column: 1,
                    hi_line: 40,
                    hi_column: usize::MAX,
                    edit_id: "multi-left".to_owned(),
                    site_kind: "subject-use",
                    atom_ids: Vec::new(),
                    atom_covered: false,
                },
                EditSite {
                    owner_class: Some(*right),
                    file: "/crate/caller.rs".to_owned(),
                    fn_path: "right".to_owned(),
                    lo_line: 40,
                    lo_column: 1,
                    hi_line: 40,
                    hi_column: usize::MAX,
                    edit_id: "multi-right".to_owned(),
                    site_kind: "subject-use",
                    atom_ids: Vec::new(),
                    atom_covered: false,
                },
            ];
            let run = |diagnostic: Diag| {
                attribute_with_rule(
                    &diagnostic,
                    &Default::default(),
                    root,
                    &sites,
                    &edits,
                    &BTreeSet::new(),
                    root,
                )
            };
            assert_eq!(
                run(diag("/crate/caller.rs", 10)).rule,
                AttributionRule::ExactEdit
            );
            let seam = run(diag("/crate/caller.rs", 20));
            assert_eq!(seam.rule, AttributionRule::ExactSeam);
            assert_eq!(seam.classes, BTreeSet::from([*right]));
            assert_eq!(
                run(diag("/crate/caller.rs", 21)).rule,
                AttributionRule::ExactSeam,
                "MIR inventory intervals are exact seam sites"
            );
            let mut related = diag("/crate/caller.rs", 99);
            related.related.push(super::super::verify::RelatedDiag {
                file: "/crate/caller.rs".to_owned(),
                line: 20,
                column: 1,
                end_line: 20,
                end_column: 1,
                message: "callee seam".to_owned(),
            });
            assert_eq!(run(related).rule, AttributionRule::RelatedSpan);
            assert_eq!(
                run(diag("/crate/caller.rs", 32)).rule,
                AttributionRule::EnclosingRegion
            );
            let multi = run(diag("/crate/caller.rs", 40));
            assert_eq!(multi.rule, AttributionRule::ExactEdit);
            assert_eq!(multi.classes, BTreeSet::from([*left, *right]));
            let mut reversed = edits.to_vec();
            reversed.reverse();
            let reversed_multi = attribute_with_rule(
                &diag("/crate/caller.rs", 40),
                &Default::default(),
                root,
                &sites,
                &reversed,
                &BTreeSet::new(),
                root,
            );
            assert_eq!(reversed_multi, multi, "input order changed attribution");
            assert_eq!(
                run(diag("/crate/caller.rs", 99)).rule,
                AttributionRule::Unresolved
            );
        })
        .expect("attribution fixture compiles");
    }

    /// D9-W1 — whole-function pretty-printing may move a bridge several lines
    /// below its input span.  Attribution must follow the preserved expression
    /// token inside that reprint; collapsing every point in the replacement to
    /// the function's first input line reproduces the R172 unresolved rows.
    #[test]
    fn d9_w1_reprinted_bridge_maps_to_its_original_site() {
        let original = "prefix\nfn caller() {\n    target(p);\n}\n";
        let lo = original.find("fn caller").expect("function start");
        let hi = original.len() - 1;
        let replacement = "fn caller() {\n    target(unsafe {\n        &*p\n    });\n}".to_owned();
        let maps = BTreeMap::from([(
            FileKey::Real("/crate/lib.rs".into()),
            crate::bo_rewriter::apply::LineMap::from_splices(original, &[(lo, hi, replacement)]),
        )]);
        let owner = class(rustc_hir::def_id::CRATE_DEF_ID);
        let edits = [EditSite {
            owner_class: Some(owner),
            file: "/crate/lib.rs".to_owned(),
            fn_path: "crate::caller".to_owned(),
            lo_line: 3,
            lo_column: 12,
            hi_line: 3,
            hi_column: 13,
            edit_id: "d9-bridge".to_owned(),
            site_kind: "seam-adapter",
            atom_ids: Vec::new(),
            atom_covered: false,
        }];
        let result = attribute_with_rule(
            &diag("/tmp/observed/lib.rs", 4),
            &maps,
            Path::new("/tmp/observed"),
            &[],
            &edits,
            &BTreeSet::new(),
            Path::new("/crate"),
        );
        assert_eq!(result.rule, AttributionRule::ExactSeam);
        assert_eq!(result.classes, BTreeSet::from([owner]));
    }

    /// D9-W2 — two class-owned operands may share a source line.  The primary
    /// span's columns select only the operand it covers; line-only matching
    /// would revert both classes.
    #[test]
    fn d9_w2_same_line_operands_are_column_granular() {
        let fixture = Fixture::new(&[("lib.rs", "pub fn left() {} pub fn right() {}\n")]);
        ::utils::compilation::run_compiler_on_path(&fixture.0.join("lib.rs"), |tcx| {
            let mut classes = tcx.hir_body_owners().map(class).collect::<Vec<_>>();
            classes.sort();
            let [left, right] = classes.as_slice() else { panic!("two classes") };
            let mut diagnostic = diag("/crate/caller.rs", 10);
            diagnostic.column = 20;
            diagnostic.end_column = 21;
            let edits = [
                EditSite {
                    owner_class: Some(*left),
                    file: "/crate/caller.rs".to_owned(),
                    fn_path: "left".to_owned(),
                    lo_line: 10,
                    lo_column: 5,
                    hi_line: 10,
                    hi_column: 6,
                    edit_id: "left".to_owned(),
                    site_kind: "seam-adapter",
                    atom_ids: Vec::new(),
                    atom_covered: false,
                },
                EditSite {
                    owner_class: Some(*right),
                    file: "/crate/caller.rs".to_owned(),
                    fn_path: "right".to_owned(),
                    lo_line: 10,
                    lo_column: 20,
                    hi_line: 10,
                    hi_column: 21,
                    edit_id: "right".to_owned(),
                    site_kind: "seam-adapter",
                    atom_ids: Vec::new(),
                    atom_covered: false,
                },
            ];
            let result = attribute_with_rule(
                &diagnostic,
                &Default::default(),
                Path::new("/crate"),
                &[],
                &edits,
                &BTreeSet::new(),
                Path::new("/crate"),
            );
            assert_eq!(result.rule, AttributionRule::ExactSeam);
            assert_eq!(result.classes, BTreeSet::from([*right]));
        })
        .expect("D9-W2 input compiles");
    }

    /// **A caller-file diagnostic names the CALLEE that caused it.**
    ///
    /// This is the S3 defect the plan required repaired before any new subject
    /// emits. Call-site adaptation puts edits in files the subject does not
    /// live in, and function-extent containment attributes such a diagnostic to
    /// **nobody** — the revert loop then cannot converge on the culprit and
    /// falls through to bisect, which "may revert more than strictly
    /// necessary".
    ///
    /// **The negative half is the repair's own witness**: the same diagnostic
    /// with an empty edit list attributes to nothing, which is exactly what
    /// production did before. Without it a test could pass on an
    /// implementation that attributes everything to everyone.
    ///
    /// *Mutation-tested (deletion first):* deleting the edit-range pass leaves
    /// only the extent pass and fails on the positive half.
    #[test]
    fn a_caller_file_diagnostic_attributes_to_the_edit_that_justifies_it() {
        let root = Path::new("/crate");
        let callee = class(rustc_hir::def_id::CRATE_DEF_ID);
        // The subject's own function lives in `callee.rs`; the edit landed in
        // `caller.rs`, which holds no subject at all.
        let sites = [EmittedSite {
            owner_class: callee,
            file: "/crate/callee.rs".to_owned(),
            fn_path: "k::callee".to_owned(),
            lo_line: 1,
            hi_line: 3,
        }];
        let edits = [EditSite {
            owner_class: Some(callee),
            file: "/crate/caller.rs".to_owned(),
            fn_path: "k::callee".to_owned(),
            lo_line: 10,
            lo_column: 1,
            hi_line: 10,
            hi_column: usize::MAX,
            edit_id: "caller-edit".to_owned(),
            site_kind: "seam-adapter",
            atom_ids: Vec::new(),
            atom_covered: false,
        }];
        let diags = [diag("/crate/caller.rs", 10)];

        let owners = attribute(
            &diags,
            &Default::default(),
            root,
            &sites,
            &edits,
            &BTreeSet::new(),
            root,
        );
        assert_eq!(
            owners.into_iter().collect::<Vec<_>>(),
            vec![callee],
            "an error inside a caller-file edit must name the subject that \
             justifies the edit"
        );

        let blind = attribute(
            &diags,
            &Default::default(),
            root,
            &sites,
            &[],
            &BTreeSet::new(),
            root,
        );
        assert!(
            blind.is_empty(),
            "the pre-repair derivation must attribute this to NOBODY, or the \
             positive half witnesses nothing: {blind:?}"
        );
    }

    /// The fallback survives: a diagnostic inside a rewritten function's extent
    /// but inside no edit still attributes to that function.
    ///
    /// Without this, the repair could have been "replace extent containment
    /// with edit containment", which would have silently dropped every
    /// diagnostic that lands near an edit rather than on it — the common case.
    #[test]
    fn a_diagnostic_outside_every_edit_still_falls_back_to_the_function_extent() {
        let root = Path::new("/crate");
        let callee = class(rustc_hir::def_id::CRATE_DEF_ID);
        let sites = [EmittedSite {
            owner_class: callee,
            file: "/crate/callee.rs".to_owned(),
            fn_path: "k::callee".to_owned(),
            lo_line: 1,
            hi_line: 30,
        }];
        let edits = [EditSite {
            owner_class: Some(callee),
            file: "/crate/callee.rs".to_owned(),
            fn_path: "k::callee".to_owned(),
            lo_line: 1,
            lo_column: 1,
            hi_line: 1,
            hi_column: usize::MAX,
            edit_id: "callee-edit".to_owned(),
            site_kind: "subject-declaration",
            atom_ids: Vec::new(),
            atom_covered: false,
        }];
        let owners = attribute(
            &[diag("/crate/callee.rs", 20)],
            &Default::default(),
            root,
            &sites,
            &edits,
            &BTreeSet::new(),
            root,
        );
        assert_eq!(owners.into_iter().collect::<Vec<_>>(), vec![callee]);
    }

    /// **A STALE edit must not blind attribution — Codex adversarial review,
    /// finding P3(a), CONFIRMED by reading before it was accepted.**
    ///
    /// `edit_sites` is built once from the whole plan; `render` keeps an edit
    /// only while its owner is not reverted. Attributing through the unfiltered
    /// list is a second derivation of *"which edits are live"*, and once
    /// anything is reverted the two diverge: the stale edit matches,
    /// short-circuits the extent pass, contributes only an already-reverted
    /// owner, and the caller's `.difference(&reverted)` then empties the
    /// result — a convergent run sent to bisect.
    ///
    /// Here the caller's own function extent IS the right answer, and the fix
    /// is to filter by the same predicate `render` filters by.
    ///
    /// *Mutation-tested (deletion first):* removing the `!reverted.contains`
    /// filter makes this return empty and fails.
    #[test]
    fn a_reverted_owners_edit_does_not_blind_attribution() {
        let fixture = Fixture::new(&[(
            "lib.rs",
            "pub unsafe fn caller(p: *mut i32) { callee(p) }\n\
             pub unsafe fn callee(_p: *mut i32) {}\n",
        )]);
        ::utils::compilation::run_compiler_on_path(&fixture.0.join("lib.rs"), |tcx| {
            let mut ids = tcx.hir_body_owners().collect::<Vec<_>>();
            ids.sort_by_key(|did| tcx.def_path_str(did.to_def_id()));
            let callee = class(ids[0]);
            let caller = class(ids[1]);
            assert_ne!(callee, caller);
            let root = Path::new("/crate");
            let sites = [EmittedSite {
                owner_class: caller,
                file: "/crate/m.rs".to_owned(),
                fn_path: "same-display".to_owned(),
                lo_line: 5,
                hi_line: 15,
            }];
            let edits = [EditSite {
                owner_class: Some(callee),
                file: "/crate/m.rs".to_owned(),
                fn_path: "same-display".to_owned(),
                lo_line: 10,
                lo_column: 1,
                hi_line: 10,
                hi_column: usize::MAX,
                edit_id: "reverted-edit".to_owned(),
                site_kind: "seam-adapter",
                atom_ids: Vec::new(),
                atom_covered: false,
            }];
            let reverted = BTreeSet::from([callee]);
            let owners = attribute(
                &[diag("/crate/m.rs", 10)],
                &Default::default(),
                root,
                &sites,
                &edits,
                &reverted,
                root,
            );
            assert_eq!(
                owners.into_iter().collect::<Vec<_>>(),
                vec![caller],
                "the reverted class's edit must not suppress its homonymous twin"
            );
        })
        .expect("homonym fixture compiles");
    }

    /// `edit_sites` converts byte ranges to the LINES a diagnostic reports in.
    ///
    /// *Mutation-tested:* returning `(1, 1)` unconditionally makes the
    /// attribution test above pass by accident and fails here.
    #[test]
    fn an_edit_locates_to_the_lines_it_spans() {
        let text = "aaa\nbbb\nccc\nddd\n";
        let key = FileKey::Virtual("main.rs".to_owned());
        let mut plan = Plan::default();
        plan.by_file.insert(
            key.clone(),
            vec![Edit {
                // `ccc` starts at byte 8 and ends at 11 — line 3.
                lo: 8,
                hi: 11,
                replacement: "zzz".to_owned(),
                justification: Justification::KindDecision { kind: "Ref(mut)" },
                owner_class: Some(class(rustc_hir::def_id::CRATE_DEF_ID)),
                owner_path: "k::f".to_owned(),
                bridge: None,
                atom_ids: Vec::new(),
                subject_id: "k::f::subject".to_owned(),
                required_arms: "-".to_owned(),
                edit_kind: "fixture",
            }],
        );
        let texts = BTreeMap::from([(key, text.to_owned())]);
        let located = edit_sites(&plan, &texts);
        assert_eq!(located.len(), 1);
        assert_eq!(
            (located[0].lo_line, located[0].hi_line),
            (3, 3),
            "{located:?}"
        );
        assert_eq!(located[0].file, "main.rs");
    }

    /// **The escape shapes, one fixture per kind — plus the negative.**
    ///
    /// These are MEASURED and deliberately NOT gated: `&mut T → *mut T` coerces
    /// implicitly at all four positions, so none presents as a revert. The
    /// call-argument flow is the one S3.6-1 creates and it IS gated, in
    /// `co_conversion`; a `static mut` store, a field store and a return are
    /// pre-existing and orthogonal — the already-emitting population carries
    /// the same shape today.
    ///
    /// The `local-store` negative is what stops "everything is an escape" from
    /// passing, which would have made the corpus figure meaningless.
    #[test]
    fn each_escape_shape_is_recognised_and_a_local_store_is_not_one() {
        let kinds = |body: &str| -> Vec<String> {
            let src = format!(
                "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
                 extern \"C\" {{ fn sink(p: *mut i32); }}\n\
                 pub struct S {{ pub f: *mut i32 }}\n\
                 pub static mut G: *mut i32 = 0 as *mut i32;\n\
                 pub unsafe fn f(p: *mut i32, s: *mut S) -> *mut i32 {{ {body} }}\n"
            );
            let fixture = Fixture::new(&[("lib.rs", &src)]);
            ::utils::compilation::run_compiler_on_path(&fixture.0.join("lib.rs"), |tcx| {
                let (_table, ctx) = crate::bo_rewriter::decide_table_with_ctx(tcx).expect("table");
                let mut out: Vec<String> = ctx
                    .escapes_for_test()
                    .iter()
                    .map(|e| e.kind.key().to_owned())
                    .collect();
                out.sort_unstable();
                out.dedup();
                out
            })
            .expect("fixture compiles")
        };

        assert!(kinds("G = p; p").contains(&"static-store".to_owned()));
        assert!(kinds("(*s).f = p; p").contains(&"field-store".to_owned()));
        assert!(kinds("return p;").contains(&"return".to_owned()));
        assert!(kinds("sink(p); p").contains(&"foreign-arg".to_owned()));
        // A store into another LOCAL leaves nothing: the target is in the same
        // body, so the value has not escaped the function.
        let local_only = kinds("let mut q: *mut i32 = 0 as *mut i32; q = p; q");
        assert!(
            !local_only.contains(&"static-store".to_owned())
                && !local_only.contains(&"field-store".to_owned()),
            "a local-to-local store is not an escape: {local_only:?}"
        );
    }
}

#[test]
fn deg_w1_degraded_carries_byte_identical_unmodified_input_tree() {
    let key = super::plan::FileKey::Virtual("main.rs".to_owned());
    let module_key = super::plan::FileKey::Virtual("module.rs".to_owned());
    let original = "pub fn unchanged() {}\n".to_owned();
    let module = "pub fn module_unchanged() {}\n".to_owned();
    let outcome = super::OutcomeFacts {
        original_source: original.clone(),
        original_files: BTreeMap::from([
            (key.clone(), original.clone()),
            (module_key.clone(), module.clone()),
        ]),
        ..super::OutcomeFacts::default()
    }
    .degraded("forced-guard".to_owned());
    let super::RewriteOutcome::Degraded {
        source,
        files,
        raw_boundary_artifacts,
        ..
    } = outcome
    else {
        panic!("forced outcome must degrade")
    };
    assert_eq!(source, original);
    assert_eq!(files, BTreeMap::from([(key, source), (module_key, module)]));
    assert_eq!(
        raw_boundary_artifacts.degraded_output_receipt,
        "degraded-unmodified-input"
    );
}

#[test]
fn cls_w5_w6_recovery_replays_are_class_bounded_and_strict() {
    let source = (0..70)
        .map(|index| format!("pub fn class_{index}() {{}}"))
        .collect::<Vec<_>>()
        .join("\n");
    ::utils::compilation::run_compiler_on_str(&source, |tcx| {
        let mut ids = tcx
            .hir_body_owners()
            .map(super::bridge_receipt::SignatureClassId::of)
            .collect::<Vec<_>>();
        ids.sort();
        let heman_first_round = ids[..7].iter().copied().collect::<BTreeSet<_>>();
        let ready_universe = ids.iter().copied().collect::<BTreeSet<_>>();
        let heman_first_round = super::exact_diagnostic_classes(heman_first_round, &ready_universe);
        assert_eq!(
            heman_first_round.len(),
            7,
            "seven diagnostics exceeded seven classes"
        );

        for population in [66usize, 34usize] {
            let groups = ids[..population]
                .iter()
                .copied()
                .map(|id| vec![id])
                .collect::<Vec<_>>();
            let culprit = ids[2];
            let ready = ids[..population].iter().copied().collect::<BTreeSet<_>>();
            let (reverted, probes) =
                super::recover_class_groups(&groups, &BTreeSet::new(), |trial| {
                    trial.contains(&culprit)
                });
            assert!(probes > 0);
            assert!(super::plan::strict_recovery_subset(&ready, &reverted));
        }
    })
    .expect("recovery replay fixture compiles");

    assert!(super::recovery_budget_deferred(4.0, 3.0, 10.0));
    assert!(!super::recovery_budget_deferred(4.0, 2.0, 10.0));
}

/// **THE SEAM, END TO END.** A callee whose parameter takes the optional form,
/// called with a plain `&mut` — the caller's argument gets `Some(..)` glue.
///
/// This is the first witness that the adapter reaches emitted TEXT rather than
/// only the glue table's unit tests. It pins the whole path: the call-site walk
/// computes `(expected = Opt{mut,thin}, found = Ref{mut})`, `seam::glue`
/// produces `Some(&mut x)`, `plan` places it in the CALLER's file under the
/// CALLEE's `owner_fn`, and `apply` splices it.
///
/// *Mutation-tested (Rider 0, deletion first):* stop filling `table.seams` in
/// the driver and the emitted source keeps the bare `&mut x`, which no longer
/// satisfies `Option<&mut i32>`.
#[test]
fn a_mismatched_argument_gets_seam_glue_in_the_emitted_text() {
    let src = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
               pub unsafe fn callee(p: *mut i32) -> i32 {\n\
               \x20   if p.is_null() { 0 } else { *p }\n\
               }\n\
               pub fn caller() {\n\
               \x20   let mut x: i32 = 1;\n\
               \x20   unsafe { callee(&mut x); }\n\
               }\n";
    let super::RewriteOutcome::Emitted { source, .. } = super::rewrite_m1(src) else {
        panic!("fixture must emit");
    };
    assert!(
        source.contains("callee(Some(&mut x))"),
        "the argument must be wrapped by the seam, or the callee's optional \
         parameter is left ill-typed:\n{source}"
    );
}

// ---------------------------------------------------------------------------
// Item E call-site adaptation wave 1 — RED-first production-path witnesses.
// ---------------------------------------------------------------------------

/// Run the SAME decision/seam producer that production uses and return its
/// durable position ledger. This is deliberately not a miniature adapter
/// implementation in the harness: the fixture enters through `seam_tsv`,
/// which calls `decide_table_with_ctx` and therefore `seam::synthesize`.
fn e_adapt_seams(src: &str) -> String {
    let fixture = Fixture::new(&[("lib.rs", src)]);
    ::utils::compilation::run_compiler_on_path(&fixture.root(), |tcx| {
        super::seam_tsv(tcx).expect("wave-1 seam receipt")
    })
    .expect("wave-1 fixture compiles before rewriting")
}

/// The production rewrite/verify entry, not a harness-only rendering of a
/// `GlueSpec`.
fn e_adapt_source(src: &str) -> String {
    match super::rewrite_m1(src) {
        super::RewriteOutcome::Emitted { source, .. } => source,
        other => panic!("wave-1 fixture must survive production verify: {other:?}"),
    }
}

const E_ADAPT_PRE: &str = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n";

/// E-ADAPT-W1 — raw expressions into shared slices, covering BOTH extent arms.
///
/// The first callee has an adjacent count and must retain the licensed arm. The
/// second has no count and must name the §77 fallback. Both callers use an
/// offset expression rather than a bare local: that is the corpus shape the
/// existing argument classifier calls `Other`, so the witness is RED before
/// wave 1 even though g25/g26 already cover the glue algebra in isolation.
#[test]
fn e_adapt_w1_slice_uses_licensed_then_named_fallback_extent() {
    let src = format!(
        "{E_ADAPT_PRE}\
         pub unsafe fn with_len(p: *const i32, n: usize) -> i32 {{\n\
         \x20   let mut out = 0; let mut i = 0;\n\
         \x20   while i < n {{ out += *p.offset(i as isize); i += 1; }} out\n\
         }}\n\
         pub unsafe fn without_len(p: *const i32) -> i32 {{ *p.offset(0) + *p.offset(1) }}\n\
         pub unsafe fn caller(base: *const i32, n: usize) -> i32 {{\n\
         \x20   with_len(base.offset(0), n) + without_len(base.offset(1))\n\
         }}\n"
    );
    let seams = e_adapt_seams(&src);
    let emitted = e_adapt_source(&src);
    assert!(
        seams.contains("len-following") && seams.contains("len-fabricated"),
        "the two-arm producer must report one licensed and one fallback row:\n{seams}"
    );
    assert!(
        emitted.contains("crate::FALLBACK_SLICE_EXTENT"),
        "the missing-evidence site must use the ruled name:\n{emitted}"
    );
    assert_eq!(
        emitted
            .matches("const FALLBACK_SLICE_EXTENT: usize = 1024;")
            .count(),
        1,
        "one or many fallback sites produce exactly one survivor-derived const"
    );
}

/// E-ADAPT-W2 — null is `None`, and a maybe-null raw expression is checked at
/// the boundary. The raw expression appears once in each emitted argument;
/// no optional extraction is permitted.
#[test]
fn e_adapt_w2_optional_maps_null_to_none_without_unwrap() {
    let src = format!(
        "{E_ADAPT_PRE}\
         pub unsafe fn optional(p: *const i32) -> i32 {{\n\
         \x20   if p.is_null() {{ 0 }} else {{ *p }}\n\
         }}\n\
         pub unsafe fn caller(base: *const i32) -> i32 {{\n\
         \x20   optional(0 as *const i32) + optional(base.offset(1))\n\
         }}\n"
    );
    let seams = e_adapt_seams(&src);
    let emitted = e_adapt_source(&src);
    assert!(
        emitted.contains("optional(None)"),
        "null must become None:\n{emitted}"
    );
    assert!(
        emitted.contains("unsafe { base.offset(1).as_ref() }"),
        "a maybe-null raw expression must use the one-evaluation pointer Option API:\n{emitted}"
    );
    let caller_line = emitted
        .lines()
        .find(|line| line.contains("optional(None)"))
        .expect("the emitted caller line is present");
    assert!(
        !caller_line.contains("unwrap"),
        "wave-1 optional ADAPTERS never extract with unwrap; the converted callee body is a different layer:\n{caller_line}"
    );
    assert!(
        seams.lines().next().is_some_and(|h| h.contains("null_arm")),
        "the production receipt must carry the null arm:\n{seams}"
    );
}

/// E-ADAPT-W3 — scalar, slice, and optional adapters compose atomically at one
/// call. Every target is shared so the overlap control is not the reason this
/// fixture passes or fails.
#[test]
fn e_adapt_w3_mixed_safe_call_is_atomic_and_fully_receipted() {
    let src = format!(
        "{E_ADAPT_PRE}\
         pub unsafe fn mixed(a: *const i32, b: *const i32, c: *const i32, n: usize) -> i32 {{\n\
         \x20   let mut out = *a; let mut i = 0;\n\
         \x20   while i < n {{ out += *b.offset(i as isize); i += 1; }}\n\
         \x20   if c.is_null() {{ out }} else {{ out + *c }}\n\
         }}\n\
         pub unsafe fn caller(x: *const i32, y: *const i32) -> i32 {{\n\
         \x20   mixed(x.offset(0), y.offset(0), 0 as *const i32, 2)\n\
         }}\n"
    );
    let seams = e_adapt_seams(&src);
    let emitted = e_adapt_source(&src);
    let placed = seams
        .lines()
        .filter(|line| line.starts_with("placed\t"))
        .count();
    assert!(
        placed >= 3,
        "all three pointer positions need receipts:\n{seams}"
    );
    assert!(
        emitted.contains("mixed(") && emitted.contains("None"),
        "the whole mixed call must survive as one adapted call:\n{emitted}"
    );
}

/// The corpus's first plan-level interaction: the raw call argument contains a
/// use rewrite of its own. The AST pipeline is deliberately ordered use-first,
/// seam-second; plan validation must recognize exactly that sanctioned
/// containment without weakening ordinary overlap rejection.
#[test]
fn e_adapt_w3_nested_use_then_seam_composes_at_the_ast_choke_point() {
    let src = format!(
        "{E_ADAPT_PRE}\
         pub struct Node {{ pub value: i32, pub next: *mut Node }}\n\
         pub unsafe fn consume(p: *mut Node) -> i32 {{\n\
         \x20   if p.is_null() {{ 0 }} else {{ (*p).value }}\n\
         }}\n\
         pub unsafe fn caller(root: *mut Node) -> i32 {{\n\
         \x20   if root.is_null() {{ 0 }} else {{ consume((*root).next) }}\n\
         }}\n"
    );
    let attempt = e2_attempt(&src, &|_| {});
    assert!(
        !attempt
            .emission
            .plan
            .class_finalization
            .collisions
            .is_empty(),
        "the cross-class nested interval must be counted and listed"
    );
    assert!(
        attempt.emission.files.is_empty(),
        "a cross-class interval collision holds both classes; no edit order is selected"
    );
}

/// E-ADAPT-W4 — a non-bare raw expression into a scalar-reference target.
#[test]
fn e_adapt_w4_scalar_reference_reborrows_the_raw_expression() {
    let src = format!(
        "{E_ADAPT_PRE}\
         pub unsafe fn scalar(p: *const i32) -> i32 {{ *p }}\n\
         pub unsafe fn caller(base: *const i32) -> i32 {{ scalar(base.offset(1)) }}\n"
    );
    let seams = e_adapt_seams(&src);
    let emitted = e_adapt_source(&src);
    assert!(
        seams.contains("\treborrow\t") && seams.contains("\t0\tc-raw-reborrow-shared\t"),
        "the raw-expression bridge must be typed as the scalar template:\n{seams}"
    );
    assert!(
        emitted.contains("scalar(unsafe { &*base.offset(1) })"),
        "the call-scoped shared reborrow must surround the whole expression:\n{emitted}"
    );
}

/// E-ADAPT-N4 — fallback identity is inseparable from its receipt and name.
#[test]
fn e_adapt_n4_fallback_name_and_receipt_are_one_production_fact() {
    let src = format!(
        "{E_ADAPT_PRE}\
         pub unsafe fn sum(p: *const i32) -> i32 {{ *p.offset(0) + *p.offset(1) }}\n\
         pub unsafe fn caller(p: *const i32) -> i32 {{ sum(p.offset(0)) }}\n"
    );
    let seams = e_adapt_seams(&src);
    let emitted = e_adapt_source(&src);
    assert_eq!(seams.matches("len-fabricated").count(), 1, "{seams}");
    assert_eq!(
        emitted.matches("crate::FALLBACK_SLICE_EXTENT").count(),
        1,
        "{emitted}"
    );
    assert!(!emitted.contains("SEAM_LEN_PLACEHOLDER"), "{emitted}");
}

/// §79 classifier control — `RawIntoRewritten` describes the TYPE direction,
/// not the syntactic site. Only rustc's callee-definition relation makes this a
/// call boundary; the same direction at a local initializer is a body
/// expression and must not re-enter the 89-row adapter market.
#[test]
fn e_adapt_classifier_separates_call_boundary_from_body_expression() {
    let body = verify::Diag {
        file: "lib.rs".to_owned(),
        line: 10,
        column: 1,
        end_line: 10,
        end_column: 1,
        message: "expected reference found raw pointer".to_owned(),
        direction: verify::Direction::RawIntoRewritten,
        code: Some("E0308".to_owned()),
        related: Vec::new(),
    };
    assert!(
        !super::e1_call_site_not_adapted(&body),
        "a body initializer is not a call merely because its type direction is RawIntoRewritten"
    );

    let mut call = body.clone();
    call.related.push(verify::RelatedDiag {
        file: "lib.rs".to_owned(),
        line: 2,
        column: 1,
        end_line: 2,
        end_column: 1,
        message: "function defined here".to_owned(),
    });
    assert!(
        super::e1_call_site_not_adapted(&call),
        "the callee-definition relation is the positive call-boundary evidence"
    );
}

// ---------------------------------------------------------------------------
// Item E call-site adaptation wave 2 — RED-first production-path witnesses.
//
// Full-suite preregistration at the RED commit: five new ordinary tests move
// the landed 1,566/6/87 identity to exactly 1,571/6/87 once GREEN. The expected
// count is written before the implementation and may not be edited to fit it.
// ---------------------------------------------------------------------------

struct E2Attempt {
    fixture: Fixture,
    emission: Emission,
    receipt: String,
}

/// Inject only the form decision, then re-run the SAME seam/body synthesis and
/// AST emitter production uses. The hook is test-only; the synthesis is not.
fn e2_attempt(
    src: &str,
    inject: &(dyn Fn(&mut super::decision::DecisionTable) + Sync),
) -> E2Attempt {
    let fixture = Fixture::new(&[("lib.rs", src)]);
    let (emission, receipt) = ::utils::compilation::run_compiler_on_path(&fixture.root(), |tcx| {
        let (mut table, ctx) = super::decide_table_with_ctx(tcx).expect("wave-2 decision table");
        inject(&mut table);
        table.seams = super::decision::seam::synthesize(
            tcx,
            &ctx.facts,
            &ctx.subjects,
            &table,
            &ctx.retained_c9_plans,
            &ctx.a5_site_proofs,
            &ctx.retention,
            &ctx.lifetime_eligibility,
        );
        let receipt = super::seam_tsv_from_table(tcx, &table);
        let emission = emit_files(
            tcx,
            &table,
            &rustc_hash::FxHashSet::default(),
            &ctx.retained_c9_plans,
        )
        .expect("wave-2 attempted emission");
        (emission, receipt)
    })
    .expect("wave-2 fixture compiles before rewriting");
    E2Attempt {
        fixture,
        emission,
        receipt,
    }
}

fn raw_boundary_attempt_with(
    src: &str,
    inject: &(dyn Fn(&mut super::decision::DecisionTable) + Sync),
) -> E2Attempt {
    let fixture = Fixture::new(&[("lib.rs", src)]);
    let (emission, receipt) =
        ::utils::compilation::run_compiler_on_path(&fixture.root(), |tcx| {
            let (mut table, ctx) = super::decide_table_with_ctx_config(
                tcx,
                Some((
                    crate::analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay,
                    Some(
                        crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph,
                    ),
                )),
            )
            .expect("raw-boundary fixture decision table");
            inject(&mut table);
            let raw_boundary =
                super::decision::raw_boundary::RawBoundaryDispositionIndex::derive(
                    &ctx.raw_boundary_sites,
                    &ctx.retention,
                    &table,
                    &ctx.facts,
                    &ctx.mut_facts,
                );
            table.depth2_npo_storages = super::decision::plan_depth2_npo_storages(
                tcx,
                &table,
                &ctx.facts,
                &ctx.constructions,
            );
            table.seams = super::decision::seam::synthesize_with_raw_boundary(
                tcx,
                &ctx.facts,
                &ctx.subjects,
                &table,
                &ctx.retained_c9_plans,
                &ctx.a5_site_proofs,
                &raw_boundary,
                &ctx.coconv,
                &ctx.retention,
                &ctx.lifetime_eligibility,
            );
            let arm_requirements = super::derive_arm_requirements(
                &ctx.subjects,
                &table,
                &ctx.coconv,
                &raw_boundary,
                &ctx.exposure,
            );
            table.arm_requirements = arm_requirements;
            let receipt = format!(
                "{}\n-- addresses --\n{}\n-- lifetimes --\n{}\n-- seams --\n{}",
                raw_boundary.receipts_tsv(),
                raw_boundary.addresses_tsv(tcx),
                table.lifetime_plan.canonical_receipt(tcx),
                super::seam_tsv_from_table(tcx, &table)
            );
            let emission = emit_files(
                tcx,
                &table,
                &rustc_hash::FxHashSet::default(),
                &ctx.retained_c9_plans,
            )
            .expect("raw-boundary attempted emission");
            (emission, receipt)
        })
        .expect("raw-boundary fixture compiles before rewriting");
    E2Attempt {
        fixture,
        emission,
        receipt,
    }
}

fn force_body_forms(
    table: &mut super::decision::DecisionTable,
    raw_suffixes: &[&str],
    refs: &[(&str, bool)],
) {
    for (subject, decision) in &mut table.entries {
        if raw_suffixes
            .iter()
            .any(|suffix| subject.label.ends_with(suffix))
        {
            *decision = super::decision::Decision::Degraded(super::decision::Degradation {
                subject: subject.label.clone(),
                site: "<e2-injected>".to_owned(),
                reason: super::decision::DegradeReason::CallSiteNotAdapted,
            });
        }
        if let Some((_, mutable)) = refs
            .iter()
            .find(|(suffix, _)| subject.label.ends_with(suffix))
        {
            *decision = super::decision::Decision::Ref { mutable: *mutable };
        }
    }
}

fn e2_root_text(attempt: &E2Attempt) -> &str {
    text_for(&attempt.emission, "lib.rs").unwrap_or_else(|| {
        panic!(
            "wave-2 root emitted; class finalization: {:#?}",
            attempt.emission.plan.class_finalization
        )
    })
}

fn e2_type_checks(attempt: &E2Attempt) -> bool {
    let temp = verify::materialize(&attempt.fixture.root(), &attempt.emission.files)
        .expect("materialize wave-2 attempt");
    verify::type_checks_crate(temp.root())
}

/// E2-BODY-W1 — the local initializer uses the common scalar-reference glue.
#[test]
fn e2_body_w1_initializer_uses_the_production_scalar_adapter() {
    let src = format!(
        "{E_ADAPT_PRE}\
         pub mod src {{ pub mod json {{\n\
         pub unsafe fn json_extract_get_array_size(p: *const i32) -> i32 {{\n\
         \x20   let q: *const i32 = p; *q\n\
         }}\n\
         }} }}\n"
    );
    let attempt = e2_attempt(&src, &|table| {
        force_body_forms(
            table,
            &["json_extract_get_array_size::p"],
            &[("json_extract_get_array_size::q", false)],
        );
    });
    assert!(
        attempt.receipt.lines().any(|line| {
            line.starts_with("body-placed\t")
                && line.contains("json_extract_get_array_size")
                && line.contains("local-initializer")
        }),
        "the initializer must ride the production receipt:\n{}",
        attempt.receipt
    );
    assert!(
        e2_root_text(&attempt).contains("&*p"),
        "{}",
        e2_root_text(&attempt)
    );
    assert!(
        e2_type_checks(&attempt),
        "the adapted initializer must compile"
    );
}

/// E2-BODY-W2 — a later assignment reuses the mutable scalar adapter.
#[test]
fn e2_body_w2_assignment_uses_the_production_scalar_adapter() {
    let src = format!(
        "{E_ADAPT_PRE}\
         pub mod src {{ pub mod json {{\n\
         pub unsafe fn json_extract_get_object_size(p: *mut i32) -> i32 {{\n\
         \x20   let mut x = 0; let mut q: *mut i32 = &mut x; q = p; *q += 1; *q\n\
         }}\n\
         }} }}\n"
    );
    let attempt = e2_attempt(&src, &|table| {
        force_body_forms(
            table,
            &["json_extract_get_object_size::p"],
            &[("json_extract_get_object_size::q", true)],
        );
    });
    assert!(
        attempt.receipt.lines().any(|line| {
            line.starts_with("body-placed\t")
                && line.contains("json_extract_get_object_size")
                && line.contains("assignment-rhs")
        }),
        "the assignment must ride the production receipt:\n{}",
        attempt.receipt
    );
    assert!(
        e2_root_text(&attempt).contains("q = unsafe { &mut *p }"),
        "{}",
        e2_root_text(&attempt)
    );
    assert!(
        e2_type_checks(&attempt),
        "the adapted assignment must compile"
    );
}

/// E2-N3 — a side-effecting RHS stays residual and is never duplicated.
#[test]
fn e2_body_n3_side_effecting_assignment_is_evaluated_once_and_refused() {
    let src = format!(
        "{E_ADAPT_PRE}\
         pub mod src {{ pub mod json {{\n\
         unsafe fn next(p: *const i32, calls: &mut i32) -> *const i32 {{ *calls += 1; p }}\n\
         pub unsafe fn json_extract_get_string_size(p: *const i32, calls: &mut i32) -> i32 {{\n\
         \x20   let mut x = 0; let mut q: *const i32 = &mut x; q = next(p, calls); *q\n\
         }}\n\
         }} }}\n"
    );
    let attempt = e2_attempt(&src, &|table| {
        force_body_forms(
            table,
            &["json_extract_get_string_size::p"],
            &[("json_extract_get_string_size::q", false)],
        );
    });
    assert!(
        attempt.receipt.lines().any(|line| {
            line.starts_with("body-blocked\t")
                && line.contains("json_extract_get_string_size")
                && line.contains("body-side-effecting-rhs")
        }),
        "the side-effect control must be typed, not silently absent:\n{}",
        attempt.receipt
    );
    assert!(
        attempt.emission.files.is_empty(),
        "the blocked body site holds the whole signature class"
    );
    let original = std::fs::read_to_string(attempt.fixture.root()).expect("fixture source");
    assert_eq!(
        original.matches("next(p, calls)").count(),
        1,
        "the unmodified input evaluates the side effect exactly once:\n{original}"
    );
}

/// The exact-eight allowlist is a production fact: an identical ninth function
/// must not acquire a body adapter.
#[test]
fn e2_body_scope_adapts_only_the_enumerated_function_identity() {
    let src = format!(
        "{E_ADAPT_PRE}\
         pub mod src {{ pub mod json {{\n\
         pub unsafe fn json_extract_get_array_size(p: *const i32) -> i32 {{ let q: *const i32 = p; *q }}\n\
         pub unsafe fn ninth_not_scoped(p: *const i32) -> i32 {{ let q: *const i32 = p; *q }}\n\
         }} }}\n"
    );
    let attempt = e2_attempt(&src, &|table| {
        force_body_forms(
            table,
            &["json_extract_get_array_size::p", "ninth_not_scoped::p"],
            &[
                ("json_extract_get_array_size::q", false),
                ("ninth_not_scoped::q", false),
            ],
        );
    });
    let body = attempt
        .receipt
        .lines()
        .filter(|line| line.starts_with("body-"))
        .collect::<Vec<_>>();
    assert!(
        body.iter()
            .any(|line| line.contains("json_extract_get_array_size")),
        "{body:?}"
    );
    assert!(
        body.iter().all(|line| !line.contains("ninth_not_scoped")),
        "{body:?}"
    );
}

/// E2-SCHEMA-W1 — a refusal retains the candidate and the peer pair that made
/// the pre-gate decision possible.
#[test]
fn e2_schema_w1_blocked_rows_retain_candidate_forms_and_peer_pairs() {
    let src = format!(
        "{E_ADAPT_PRE}\
         pub unsafe fn callee(a: *mut i32, b: *mut i32) {{ *a += *b; }}\n\
         pub unsafe fn caller(p: *mut i32) {{ callee(p, p); }}\n"
    );
    let attempt = e2_attempt(&src, &|table| {
        force_body_forms(
            table,
            &["caller::p"],
            &[("callee::a", true), ("callee::b", true)],
        );
    });
    let mut lines = attempt.receipt.lines();
    let header = lines
        .next()
        .expect("receipt header")
        .split('\t')
        .collect::<Vec<_>>();
    let column = |name: &str| {
        header
            .iter()
            .position(|value| *value == name)
            .unwrap_or_else(|| panic!("missing {name} in {header:?}"))
    };
    let expected = column("expected_form");
    let found = column("found_form");
    let candidate = column("candidate_template");
    let peers = column("peer_pairs");
    let root = column("root_identity");
    let blind = column("blind");
    let context = column("context");
    let blocked = lines
        .filter(|line| line.starts_with("blocked\t"))
        .map(|line| line.split('\t').collect::<Vec<_>>())
        .collect::<Vec<_>>();
    assert_eq!(blocked.len(), 2, "{}", attempt.receipt);
    for row in blocked {
        assert_eq!(row[expected], "ref-mut", "{row:?}");
        assert_eq!(row[found], "raw", "{row:?}");
        assert_eq!(row[candidate], "c-raw-reborrow-mut", "{row:?}");
        assert_eq!(
            row[peers], "0/1[same_root=1,left_blind=0,right_blind=0]",
            "{row:?}"
        );
        assert!(row[root].ends_with("caller::p"), "{row:?}");
        assert_eq!(row[blind], "0", "{row:?}");
        assert_eq!(row[context], "call-argument", "{row:?}");
    }

    let no_edit = e2_attempt(&src, &|table| {
        force_body_forms(
            table,
            &[],
            &[
                ("caller::p", true),
                ("callee::a", true),
                ("callee::b", true),
            ],
        );
    });
    let mut no_edit_lines = no_edit.receipt.lines();
    let no_edit_header = no_edit_lines
        .next()
        .expect("no-edit receipt header")
        .split('\t')
        .collect::<Vec<_>>();
    let no_edit_candidate = no_edit_header
        .iter()
        .position(|value| *value == "candidate_template")
        .expect("candidate column");
    let no_edit_rows = no_edit_lines
        .filter(|line| line.starts_with("blocked\t"))
        .map(|line| line.split('\t').collect::<Vec<_>>())
        .collect::<Vec<_>>();
    assert_eq!(no_edit_rows.len(), 2, "{}", no_edit.receipt);
    assert!(
        no_edit_rows
            .iter()
            .all(|row| row[no_edit_candidate] == "none"),
        "a computed no-edit candidate must not collapse back to missing: {no_edit_rows:?}"
    );
}

// ---------------------------------------------------------------------------
// Item E call-site adaptation wave 3 — RED-first production-path witnesses.
// ---------------------------------------------------------------------------

const E3_CLEAR_RAW: &str = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
    extern \"C\" { fn malloc(size: usize) -> *mut core::ffi::c_void; }\n\
    pub unsafe fn target(a: *mut i32, b: *mut i32) { *a += 1; *b += 1; }\n\
    pub unsafe fn caller() {\n\
        let left = malloc(8) as *mut i32;\n\
        let right = malloc(8) as *mut i32;\n\
        target(left.offset(0), right.offset(0));\n\
    }\n";

const E3_CLEAR_REFS: &str = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
    extern \"C\" { fn malloc(size: usize) -> *mut core::ffi::c_void; }\n\
    pub unsafe fn target(a: *mut i32, b: *mut i32) { *a += 1; *b += 1; }\n\
    pub unsafe fn caller() {\n\
        let left = malloc(8) as *mut i32;\n\
        let right = malloc(8) as *mut i32;\n\
        target(&mut *left, &mut *right);\n\
    }\n";

const E3_CLEAR_LICENSED: &str = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
    extern \"C\" { fn malloc(size: usize) -> *mut core::ffi::c_void; }\n\
    pub unsafe fn target(a: *mut i32, a_len: usize, b: *mut i32, b_len: usize) {\n\
        if a_len != 0 { *a += 1; } if b_len != 0 { *b += 1; }\n\
    }\n\
    pub unsafe fn caller() {\n\
        let left = malloc(8) as *mut i32;\n\
        let right = malloc(8) as *mut i32;\n\
        target(left.offset(0), 2, right.offset(0), 2);\n\
    }\n";

const E3_SCOPED_PAIR: &str = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
    extern \"C\" { fn malloc(size: usize) -> *mut core::ffi::c_void; }\n\
    pub unsafe fn target(a: *mut i32, b: *mut i32) { *a += 1; *b += 1; }\n\
    pub unsafe fn clear_caller() {\n\
        let left = malloc(8) as *mut i32;\n\
        let right = malloc(8) as *mut i32;\n\
        target(left.offset(0), right.offset(0));\n\
    }\n\
    pub unsafe fn overlap_caller(p: *mut i32) { target(p, p); }\n";

const E3_OVERLAP: &str = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
    pub unsafe fn target(a: *mut i32, b: *mut i32) { *a += 1; *b += 1; }\n\
    pub unsafe fn caller(p: *mut i32) { target(p, p); }\n";

fn force_wave3_target_forms(table: &mut super::decision::DecisionTable, slice: bool) {
    for (subject, decision) in &mut table.entries {
        if subject.label.ends_with("caller::left")
            || subject.label.ends_with("caller::right")
            || subject.label.ends_with("caller::p")
        {
            *decision = super::decision::Decision::Degraded(super::decision::Degradation {
                subject: subject.label.clone(),
                site: "<wave3-injected>".to_owned(),
                reason: super::decision::DegradeReason::CallSiteNotAdapted,
            });
        }
        if subject.label.ends_with("target::a") || subject.label.ends_with("target::b") {
            *decision = if slice {
                super::decision::Decision::Slice {
                    mutable: true,
                    uses: Vec::new(),
                }
            } else {
                super::decision::Decision::Ref { mutable: true }
            };
        }
    }
}

fn force_wave3_target_slices(table: &mut super::decision::DecisionTable) {
    for (subject, decision) in &mut table.entries {
        if subject.label.ends_with("target::a") || subject.label.ends_with("target::b") {
            *decision = super::decision::Decision::Slice {
                mutable: true,
                uses: Vec::new(),
            };
        }
        if subject.label.ends_with("caller::left")
            || subject.label.ends_with("caller::right")
            || subject.label.ends_with("clear_caller::left")
            || subject.label.ends_with("clear_caller::right")
            || subject.label.ends_with("overlap_caller::p")
        {
            *decision = super::decision::Decision::Degraded(super::decision::Degradation {
                subject: subject.label.clone(),
                site: "<wave3-injected>".to_owned(),
                reason: super::decision::DegradeReason::CallSiteNotAdapted,
            });
        }
    }
}

/// Drive an injected form decision through the production proof derivation and
/// the production seam synthesis. The only test seam is the form injection;
/// site facts, attestation, lookup, candidate construction, and emission are
/// the shipping path.
fn e3_attempt(src: &str, attested: bool, slice: bool) -> E2Attempt {
    e3_attempt_with(src, attested, &|table| {
        force_wave3_target_forms(table, slice);
    })
}

fn e3_attempt_with(
    src: &str,
    attested: bool,
    inject: &(dyn Fn(&mut super::decision::DecisionTable) + Sync),
) -> E2Attempt {
    let fixture = Fixture::new(&[("lib.rs", src)]);
    let (emission, receipt) = ::utils::compilation::run_compiler_on_path(&fixture.root(), |tcx| {
        let attestation = attested.then_some(
            crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph,
        );
        let (mut table, ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                crate::analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay,
                attestation,
            )),
        )
        .expect("wave-3 decision table");
        assert!(
            ctx.analysis.origins.is_some(),
            "the consumer-neutral E2-X1 carrier must retain full OriginSummaries"
        );
        assert_eq!(
            ctx.analysis.a5_mode,
            crate::analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay
        );
        assert_eq!(ctx.analysis.attestation, attestation);
        inject(&mut table);
        table.seams = super::decision::seam::synthesize(
            tcx,
            &ctx.facts,
            &ctx.subjects,
            &table,
            &ctx.retained_c9_plans,
            &ctx.a5_site_proofs,
            &ctx.retention,
            &ctx.lifetime_eligibility,
        );
        let receipt = super::seam_tsv_from_table(tcx, &table);
        let emission = emit_files(
            tcx,
            &table,
            &rustc_hash::FxHashSet::default(),
            &ctx.retained_c9_plans,
        )
        .expect("wave-3 attempted emission");
        (emission, receipt)
    })
    .expect("wave-3 fixture compiles before rewriting");
    E2Attempt {
        fixture,
        emission,
        receipt,
    }
}

const BR_W1_RAW_SCALARS: &str = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
     pub unsafe fn read_target(p: *const i32) -> i32 { *p }\n\
     pub unsafe fn write_target(p: *mut i32) { *p += 1; }\n\
     pub unsafe fn caller(read_p: *const i32, write_p: *mut i32) -> i32 {\n\
         let value = read_target(read_p);\n\
         write_target(write_p);\n\
         value\n\
     }\n";

fn force_br_w1_scalar_targets(table: &mut super::decision::DecisionTable) {
    for (subject, decision) in &mut table.entries {
        if subject.label.ends_with("caller::read_p") || subject.label.ends_with("caller::write_p") {
            *decision = super::decision::Decision::Degraded(super::decision::Degradation {
                subject: subject.label.clone(),
                site: "<br-w1-injected>".to_owned(),
                reason: super::decision::DegradeReason::CallSiteNotAdapted,
            });
        } else if subject.label.ends_with("read_target::p") {
            *decision = super::decision::Decision::Ref { mutable: false };
        } else if subject.label.ends_with("write_target::p") {
            *decision = super::decision::Decision::Ref { mutable: true };
        }
    }
}

/// BR-W1 RED: both raw-scalar inbound directions are explicit unsafe
/// reborrows, owned and receipted by the converted callee's signature class.
#[test]
fn br_w1_raw_scalar_inbound_reborrows_and_receipts_are_exact() {
    use super::bridge_receipt::{
        BridgeCalleeId, BridgeReceiptStage, BridgeReceiptState, BridgeRetentionTier,
    };

    let attempt = e3_attempt_with(BR_W1_RAW_SCALARS, true, &force_br_w1_scalar_targets);
    let source = e2_root_text(&attempt);
    assert!(
        source.contains("read_target(unsafe { &*read_p })"),
        "shared raw inbound bridge must be explicit and evaluate its operand once:\n{source}"
    );
    assert!(
        source.contains("write_target(unsafe { &mut *write_p })"),
        "mutable raw inbound bridge must be explicit and evaluate its operand once:\n{source}"
    );

    let events = attempt
        .emission
        .plan
        .bridge_events(&std::collections::BTreeSet::new());
    let scalar = events
        .iter()
        .filter(|event| {
            matches!(
                event.site.bridge_kind.as_str(),
                "c-raw-reborrow-shared" | "c-raw-reborrow-mut"
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        scalar.len(),
        4,
        "one plan and terminal event per scalar: {events:#?}"
    );
    for kind in ["c-raw-reborrow-shared", "c-raw-reborrow-mut"] {
        let pair = scalar
            .iter()
            .copied()
            .filter(|event| event.site.bridge_kind == kind)
            .collect::<Vec<_>>();
        assert_eq!(
            pair.len(),
            2,
            "exact plan/terminal pair for {kind}: {events:#?}"
        );
        assert!(pair.iter().all(|event| event.site.arm == "c"));
        assert!(
            pair.iter()
                .all(|event| event.retention == BridgeRetentionTier::T1)
        );
        assert!(pair.iter().all(|event| event.waiver_id.is_none()));
        assert!(pair.iter().all(|event| {
            event.expected_form
                == if kind == "c-raw-reborrow-mut" {
                    "ref-mut"
                } else {
                    "ref-shared"
                }
                && event.found_form == "raw"
                && event.argument_kind == "bare-local"
        }));
        assert!(pair.iter().all(|event| {
            matches!(event.site.callee, BridgeCalleeId::Local(callee) if event.site.owner_class.local_def_id() == callee)
        }));
        assert!(pair.iter().any(|event| {
            event.stage == BridgeReceiptStage::Plan && event.state == BridgeReceiptState::Planned
        }));
        assert!(pair.iter().any(|event| {
            event.stage == BridgeReceiptStage::Terminal
                && event.state == BridgeReceiptState::Applied
        }));
    }
    let rendered = super::bridge_receipt::render_bridge_events(&events);
    assert!(rendered.starts_with(
        "site_key\towner_class\tcaller\tcallee\tarm\tposition\tfile\tlo\thi\tbridge_kind\texpected_form\tfound_form\targument_kind\t"
    ));
    super::bridge_receipt::reconcile_bridge_events(&events).expect("BR-W1 bridge events reconcile");
}

const INV_W1_NON_SUBJECT_CALL: &str = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
     pub struct Holder { pub value: *mut i32 }\n\
     pub unsafe fn target(p: *mut i32) -> i32 { *p }\n\
     pub unsafe fn caller(holder: &mut Holder) -> i32 {\n\
         target(holder.value)\n\
     }\n";

fn force_inv_w1_target_ref(table: &mut super::decision::DecisionTable) {
    for (subject, decision) in &mut table.entries {
        if subject.label.ends_with("target::p") {
            *decision = super::decision::Decision::Ref { mutable: true };
        }
    }
}

/// INV-W1 — a non-subject field projection at a statically targeted MIR call
/// is still one required site in the converted callee's class.  It must either
/// receive an expression-level bridge or hold that whole class.
#[test]
fn inv_w1_non_subject_mir_call_is_bridged_or_holds_the_class() {
    use super::bridge_receipt::{BridgeReceiptStage, BridgeReceiptState};

    let fixture = Fixture::new(&[("lib.rs", INV_W1_NON_SUBJECT_CALL)]);
    let (emission, receipt) =
        ::utils::compilation::run_compiler_on_path(&fixture.root(), |tcx| {
            let (mut table, mut ctx) = super::decide_table_with_ctx_config(
                tcx,
                Some((
                    crate::analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay,
                    Some(
                        crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph,
                    ),
                )),
            )
            .expect("INV-W1 decision table");
            force_inv_w1_target_ref(&mut table);
            let target = ctx
                .subjects
                .iter()
                .find(|subject| subject.label.ends_with("target::p"))
                .expect("target parameter subject")
                .fn_did;
            assert!(
                ctx.facts.call_args.remove(&target).is_some(),
                "fixture must remove one legacy HIR call carrier"
            );
            table.seams = super::decision::seam::synthesize_with_raw_boundary(
                tcx,
                &ctx.facts,
                &ctx.subjects,
                &table,
                &ctx.retained_c9_plans,
                &ctx.a5_site_proofs,
                &ctx.raw_boundary,
                &ctx.coconv,
                &ctx.retention,
                &ctx.lifetime_eligibility,
            );
            assert_eq!(table.seams.interface_inventory.len(), 1);
            assert_eq!(table.seams.sites_from_non_subject_arguments(), 1);
            assert_eq!(table.seams.converted_callee_without_site_receipt(), 0);
            let inventory = table.seams.interface_inventory_tsv(tcx);
            assert!(
                inventory.contains("\ttarget\t")
                    && inventory.contains("\tmir-only\t1\theld"),
                "{inventory}"
            );
            table.arm_requirements = super::derive_arm_requirements(
                &ctx.subjects,
                &table,
                &ctx.coconv,
                &ctx.raw_boundary,
                &ctx.exposure,
            );
            let receipt = super::seam_tsv_from_table(tcx, &table);
            let emission = emit_files(
                tcx,
                &table,
                &rustc_hash::FxHashSet::default(),
                &ctx.retained_c9_plans,
            )
            .expect("INV-W1 attempted emission");
            (emission, receipt)
        })
        .expect("INV-W1 fixture compiles before rewriting");
    let attempt = E2Attempt {
        fixture,
        emission,
        receipt,
    };
    let source = text_for(&attempt.emission, "lib.rs")
        .cloned()
        .unwrap_or_else(|| fs::read_to_string(attempt.fixture.root()).expect("fixture source"));
    let events = attempt
        .emission
        .plan
        .bridge_events(&std::collections::BTreeSet::new());
    assert_eq!(attempt.emission.plan.class_finalization.classes.len(), 1);
    assert_eq!(
        attempt
            .emission
            .plan
            .class_finalization
            .classes
            .values()
            .filter(|class| !class.is_ready())
            .count(),
        1,
        "the unplaceable MIR-only argument must hold exactly its callee class"
    );
    let sites = events
        .iter()
        .filter(|event| {
            event.site.position == "arg0"
                && matches!(
                    event.site.bridge_kind.as_str(),
                    "c-raw-reborrow-mut" | "inventory-non-subject-held"
                )
        })
        .collect::<Vec<_>>();

    assert_eq!(
        sites.len(),
        2,
        "missing INV-W1 plan/terminal receipt:\n{source}"
    );
    assert!(sites.iter().any(|event| {
        event.stage == BridgeReceiptStage::Terminal
            && matches!(
                event.state,
                BridgeReceiptState::Applied | BridgeReceiptState::Dropped
            )
    }));
    assert!(
        source.contains("target(unsafe { &mut *holder.value })")
            || source.contains("fn target(p: *mut i32)"),
        "neither expression bridge nor atomic class hold was emitted:\n{source}"
    );
    assert!(
        e2_type_checks(&attempt),
        "INV-W1 emitted tree must type-check"
    );
    super::bridge_receipt::reconcile_bridge_events(&events).expect("INV-W1 receipts reconcile");
}

const D1_CALLEE_UNIVERSE: &str = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
     pub struct Holder { pub left: *mut i32, pub right: *mut i32 }\n\
     pub unsafe fn target(p: *mut i32) -> i32 { *p }\n\
     pub unsafe fn caller(holder: &mut Holder) -> i32 {\n\
         target(holder.left) + target(holder.right)\n\
     }\n";

/// D1-W1 — a placed base parameter decision defines the callee universe even
/// when one call is absent from the older HIR/subject-keyed carrier. Coverage
/// is per MIR call site, never merely per caller/callee/position triple.
#[test]
fn d1_w1_base_parameter_callee_requires_each_mir_call_site() {
    let fixture = Fixture::new(&[("lib.rs", D1_CALLEE_UNIVERSE)]);
    let (emission, receipt, omitted_control) =
        ::utils::compilation::run_compiler_on_path(&fixture.root(), |tcx| {
            let (mut table, mut ctx) = super::decide_table_with_ctx_config(
                tcx,
                Some((
                    crate::analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay,
                    Some(
                        crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph,
                    ),
                )),
            )
            .expect("D1-W1 decision table");
            force_inv_w1_target_ref(&mut table);
            let target = ctx
                .subjects
                .iter()
                .find(|subject| subject.label.ends_with("target::p"))
                .expect("target parameter subject")
                .fn_did;
            let calls = ctx
                .facts
                .call_args
                .get_mut(&target)
                .expect("two legacy HIR call sites");
            calls.sort_by_key(|site| site.span.lo().0);
            assert_eq!(calls.len(), 2);
            calls.truncate(1);
            table.seams = super::decision::seam::synthesize_with_raw_boundary(
                tcx,
                &ctx.facts,
                &ctx.subjects,
                &table,
                &ctx.retained_c9_plans,
                &ctx.a5_site_proofs,
                &ctx.raw_boundary,
                &ctx.coconv,
                &ctx.retention,
                &ctx.lifetime_eligibility,
            );
            let mut omitted = table.seams.clone();
            omitted.interface_inventory.clear();
            omitted.interface_required_sites.clear();
            let omitted_control = omitted.converted_callee_without_site_receipt();
            table.arm_requirements = super::derive_arm_requirements(
                &ctx.subjects,
                &table,
                &ctx.coconv,
                &ctx.raw_boundary,
                &ctx.exposure,
            );
            let receipt = super::seam_tsv_from_table(tcx, &table);
            let emission = emit_files(
                tcx,
                &table,
                &rustc_hash::FxHashSet::default(),
                &ctx.retained_c9_plans,
            )
            .expect("D1-W1 attempted emission");
            (emission, receipt, omitted_control)
        })
        .expect("D1-W1 fixture compiles before rewriting");
    let attempt = E2Attempt {
        fixture,
        emission,
        receipt,
    };
    let held = attempt
        .emission
        .plan
        .class_finalization
        .classes
        .values()
        .filter(|class| !class.is_ready())
        .count();
    assert_eq!(
        held, 1,
        "the uncovered second MIR call must hold the callee"
    );
    assert!(
        e2_type_checks(&attempt),
        "D1-W1 emitted tree must type-check after bridge-or-hold"
    );
    assert_eq!(
        omitted_control, 1,
        "the control must derive from the emitted-signature diff, not inventory rows"
    );
}

const BR_W2_RAW_OPTIONALS: &str = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
     pub unsafe fn maybe_shared(p: *const i32) { let _ = p; }\n\
     pub unsafe fn maybe_mut(p: *mut i32) { let _ = p; }\n\
     pub unsafe fn caller(read_p: *const i32, write_p: *mut i32) {\n\
         maybe_shared(read_p);\n\
         maybe_mut(write_p);\n\
     }\n";

fn force_br_w2_optional_targets(table: &mut super::decision::DecisionTable) {
    for (subject, decision) in &mut table.entries {
        if subject.label.ends_with("caller::read_p") || subject.label.ends_with("caller::write_p") {
            *decision = super::decision::Decision::Degraded(super::decision::Degradation {
                subject: subject.label.clone(),
                site: "<br-w2-injected>".to_owned(),
                reason: super::decision::DegradeReason::CallSiteNotAdapted,
            });
        } else if subject.label.ends_with("maybe_shared::p") {
            *decision = super::decision::Decision::Opt {
                mutable: false,
                slice: false,
                uses: Vec::new(),
            };
        } else if subject.label.ends_with("maybe_mut::p") {
            *decision = super::decision::Decision::Opt {
                mutable: true,
                slice: false,
                uses: Vec::new(),
            };
        }
    }
}

/// BR-W2 RED: nullable inbound raw pointers use the pointer APIs directly;
/// they neither dereference unconditionally nor construct an intermediate
/// borrow before the null check.
#[test]
fn br_w2_raw_optional_inbound_uses_as_ref_and_as_mut_once() {
    use super::bridge_receipt::{BridgeReceiptStage, BridgeRetentionTier};

    let attempt = e3_attempt_with(BR_W2_RAW_OPTIONALS, true, &force_br_w2_optional_targets);
    let source = e2_root_text(&attempt);
    assert!(
        source.contains("maybe_shared(unsafe { read_p.as_ref() })"),
        "shared optional bridge must use as_ref exactly once:\n{source}"
    );
    assert!(
        source.contains("maybe_mut(unsafe { write_p.as_mut() })"),
        "mutable optional bridge must use as_mut exactly once:\n{source}"
    );
    assert!(
        !source.contains("&*read_p"),
        "unchecked shared deref survived: {source}"
    );
    assert!(
        !source.contains("&mut *write_p"),
        "unchecked mutable deref survived: {source}"
    );
    assert_eq!(source.matches("read_p.as_ref()").count(), 1, "{source}");
    assert_eq!(source.matches("write_p.as_mut()").count(), 1, "{source}");
    let null_arm = receipt_column(&attempt.receipt, "null_arm");
    let option_rows = attempt
        .receipt
        .lines()
        .skip(1)
        .map(|line| line.split('\t').collect::<Vec<_>>())
        .filter(|row| {
            row.first() == Some(&"placed")
                && matches!(
                    row.get(receipt_column(&attempt.receipt, "template")),
                    Some(&"c-raw-option-shared") | Some(&"c-raw-option-mut")
                )
        })
        .collect::<Vec<_>>();
    assert_eq!(option_rows.len(), 2, "{}", attempt.receipt);
    assert!(
        option_rows
            .iter()
            .all(|row| row[null_arm] == "raw-pointer-option"),
        "{}",
        attempt.receipt
    );

    let events = attempt
        .emission
        .plan
        .bridge_events(&std::collections::BTreeSet::new());
    for kind in ["c-raw-option-shared", "c-raw-option-mut"] {
        let pair = events
            .iter()
            .filter(|event| event.site.bridge_kind == kind)
            .collect::<Vec<_>>();
        assert_eq!(
            pair.len(),
            2,
            "exact plan/terminal pair for {kind}: {events:#?}"
        );
        assert!(pair.iter().all(|event| event.site.arm == "c"));
        assert!(
            pair.iter()
                .all(|event| event.retention == BridgeRetentionTier::T1)
        );
        assert!(pair.iter().all(|event| event.waiver_id.is_none()));
        assert!(
            pair.iter()
                .any(|event| event.stage == BridgeReceiptStage::Plan)
        );
        assert!(
            pair.iter()
                .any(|event| event.stage == BridgeReceiptStage::Terminal)
        );
    }
    super::bridge_receipt::reconcile_bridge_events(&events).expect("BR-W2 bridge events reconcile");
}

const BR_W3_RAW_SLICES: &str = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
     pub unsafe fn licensed_shared(p: *const i32, n: usize) { let _ = (p, n); }\n\
     pub unsafe fn licensed_mut(p: *mut i32, n: usize) { let _ = (p, n); }\n\
     pub unsafe fn fallback_shared(p: *const i32) { let _ = p; }\n\
     pub unsafe fn optional_shared(p: *const i32) { let _ = p; }\n\
     pub unsafe fn optional_mut(p: *mut i32) { let _ = p; }\n\
     pub unsafe fn caller(read_p: *const i32, write_p: *mut i32, n: usize) {\n\
         licensed_shared(read_p, n);\n\
         licensed_mut(write_p, n);\n\
         fallback_shared(read_p);\n\
         optional_shared(read_p);\n\
         optional_mut(write_p);\n\
     }\n";

fn force_br_w3_slice_targets(table: &mut super::decision::DecisionTable) {
    for (subject, decision) in &mut table.entries {
        if subject.label.ends_with("caller::read_p") || subject.label.ends_with("caller::write_p") {
            *decision = super::decision::Decision::Degraded(super::decision::Degradation {
                subject: subject.label.clone(),
                site: "<br-w3-injected>".to_owned(),
                reason: super::decision::DegradeReason::CallSiteNotAdapted,
            });
        } else if subject.label.ends_with("licensed_shared::p")
            || subject.label.ends_with("fallback_shared::p")
        {
            *decision = super::decision::Decision::Slice {
                mutable: false,
                uses: Vec::new(),
            };
        } else if subject.label.ends_with("licensed_mut::p") {
            *decision = super::decision::Decision::Slice {
                mutable: true,
                uses: Vec::new(),
            };
        } else if subject.label.ends_with("optional_shared::p") {
            *decision = super::decision::Decision::Opt {
                mutable: false,
                slice: true,
                uses: Vec::new(),
            };
        } else if subject.label.ends_with("optional_mut::p") {
            *decision = super::decision::Decision::Opt {
                mutable: true,
                slice: true,
                uses: Vec::new(),
            };
        }
    }
}

/// BR-W3 RED: raw slice constructors are explicit unsafe bridges, prefer the
/// carried companion extent, and use only the named fallback otherwise.
#[test]
fn br_w3_raw_slice_inbound_extents_and_nullable_twins_are_exact() {
    use super::bridge_receipt::{BridgeExtentKind, BridgeRetentionTier};

    let attempt = e3_attempt_with(BR_W3_RAW_SLICES, true, &force_br_w3_slice_targets);
    let source = e2_root_text(&attempt);
    assert!(
        source.contains(
            "licensed_shared(unsafe { core::slice::from_raw_parts(read_p, (n) as usize) }, n)"
        ),
        "{source}"
    );
    assert!(
        source.contains(
            "licensed_mut(unsafe { core::slice::from_raw_parts_mut(write_p, (n) as usize) }, n)"
        ),
        "{source}"
    );
    assert!(
        source.contains(
            "fallback_shared(unsafe { core::slice::from_raw_parts(read_p, crate::FALLBACK_SLICE_EXTENT) })"
        ),
        "{source}"
    );
    assert_eq!(
        source
            .matches("const FALLBACK_SLICE_EXTENT: usize = 1024;")
            .count(),
        1,
        "{source}"
    );
    assert!(
        source.contains("optional_shared({ let __crat_call_adapter_ptr: *const i32 = read_p;"),
        "{source}"
    );
    assert!(
        source.contains("Some(unsafe { core::slice::from_raw_parts(__crat_call_adapter_ptr, crate::FALLBACK_SLICE_EXTENT) })"),
        "{source}"
    );
    assert!(
        source.contains("optional_mut({ let __crat_call_adapter_ptr: *mut i32 = write_p;"),
        "{source}"
    );
    assert!(
        source.contains("Some(unsafe { core::slice::from_raw_parts_mut(__crat_call_adapter_ptr, crate::FALLBACK_SLICE_EXTENT) })"),
        "{source}"
    );

    let events = attempt
        .emission
        .plan
        .bridge_events(&std::collections::BTreeSet::new());
    let applied = events
        .iter()
        .filter(|event| {
            event.stage == super::bridge_receipt::BridgeReceiptStage::Terminal
                && event.state == super::bridge_receipt::BridgeReceiptState::Applied
        })
        .collect::<Vec<_>>();
    assert!(applied.iter().any(|event| {
        event.site.bridge_kind == "c-raw-slice-shared"
            && matches!(&event.extent, BridgeExtentKind::Evidence(source) if source == "n")
    }));
    assert!(applied.iter().any(|event| {
        event.site.bridge_kind == "c-raw-slice-mut"
            && matches!(&event.extent, BridgeExtentKind::Evidence(source) if source == "n")
    }));
    assert!(applied.iter().any(|event| {
        event.site.bridge_kind == "c-raw-slice-shared" && event.extent == BridgeExtentKind::Fallback
    }));
    assert_eq!(
        applied
            .iter()
            .filter(|event| {
                event.site.bridge_kind == "c-raw-option-slice"
                    && event.extent == BridgeExtentKind::Fallback
            })
            .count(),
        2,
        "{events:#?}"
    );
    assert!(
        applied
            .iter()
            .filter(|event| event.site.bridge_kind.starts_with("c-raw-"))
            .all(|event| event.retention == BridgeRetentionTier::T1 && event.waiver_id.is_none())
    );
    super::bridge_receipt::reconcile_bridge_events(&events).expect("BR-W3 bridge events reconcile");
}

/// BR-W4 RED: a function item reified inside a static descriptor table must
/// keep the table's raw function-pointer type and route through the existing
/// raw-wrapper/safe-inner surface.
#[test]
fn br_w4_static_table_function_item_uses_atomic_raw_wrapper_surface() {
    let source = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
         pub type Callback = unsafe extern \"C\" fn(*mut i32) -> i32;\n\
         pub unsafe extern \"C\" fn target(p: *mut i32) -> i32 { *p }\n\
         pub static TABLE: [Option<Callback>; 1] = [Some(target as Callback)];\n";
    let fixture = Fixture::new(&[("lib.rs", source)]);
    let outcome = super::rewrite_m1_path_a5_injected(
        &fixture.root(),
        crate::analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay,
        Some(
            crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph,
        ),
        &|_| {},
    );
    let super::RewriteOutcome::Emitted {
        source,
        raw_boundary_artifacts,
        ..
    } = outcome
    else {
        panic!("BR-W4 static-table fixture must emit: {outcome:#?}");
    };
    assert!(
        source.contains("fn target(p: *mut i32) -> i32"),
        "the table-visible wrapper keeps the raw signature:\n{source}"
    );
    assert!(
        source.contains("fn __crat_safe_target(p: &i32) -> i32"),
        "the converted body must live behind the raw wrapper:\n{source}"
    );
    assert!(
        source.contains("Some(target as Callback)"),
        "the static table must continue to name the raw wrapper:\n{source}"
    );
    assert!(
        !source.contains("Some(__crat_safe_target as Callback)"),
        "the safe inner may never be cast back to the raw table type:\n{source}"
    );
    let wrapper_events = raw_boundary_artifacts
        .bridge_events
        .iter()
        .filter(|event| event.site.bridge_kind == "surface-static-fnptr-wrapper")
        .collect::<Vec<_>>();
    assert_eq!(
        wrapper_events.len(),
        2,
        "one plan and terminal static-site receipt: {:#?}",
        raw_boundary_artifacts.bridge_events
    );
    assert!(wrapper_events.iter().all(|event| {
        matches!(
            event.site.callee,
            super::bridge_receipt::BridgeCalleeId::Local(callee)
                if event.site.owner_class.local_def_id() == callee
        )
    }));
    super::bridge_receipt::reconcile_bridge_events(&raw_boundary_artifacts.bridge_events)
        .expect("BR-W4 bridge events reconcile");
}

#[test]
fn br_w4_const_mir_static_table_cardinality_is_exactly_207() {
    let mut source = String::from(
        "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
         pub type Callback = unsafe extern \"C\" fn(*mut i32) -> i32;\n",
    );
    for index in 0..207 {
        source.push_str(&format!(
            "pub unsafe extern \"C\" fn target_{index}(p: *mut i32) -> i32 {{ *p + {index} }}\n"
        ));
    }
    source.push_str("pub static TABLE: [Option<Callback>; 207] = [\n");
    for index in 0..207 {
        source.push_str(&format!("Some(target_{index} as Callback),\n"));
    }
    source.push_str("];\n");

    let (roots, members, seeds, unique_functions, unique_owners) =
        ::utils::compilation::run_compiler_on_str(&source, |tcx| {
            let program = super::collect_program(tcx);
            let web = super::decision::lifetime::derive_fn_ptr_web(
                &program,
                Some(
                    crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph,
                ),
            )
            .expect("attested fn-pointer web");
            let seeds = web.static_seeds();
            (
                web.root_count(),
                web.member_count(),
                seeds.len(),
                seeds
                    .iter()
                    .map(|seed| seed.function.local_def_index.as_u32())
                    .collect::<std::collections::BTreeSet<_>>()
                    .len(),
                seeds
                    .iter()
                    .map(|seed| seed.owner.local_def_index.as_u32())
                    .collect::<std::collections::BTreeSet<_>>()
                    .len(),
            )
        })
        .expect("207-entry static table compiles");
    assert_eq!((roots, members, seeds), (207, 207, 207));
    assert_eq!(
        unique_functions, 207,
        "one exact local function ID per entry"
    );
    assert_eq!(
        unique_owners, 1,
        "all entries belong to the one static initializer"
    );
}

#[test]
fn br_w4_generated_safe_inner_name_collision_is_typed_and_held() {
    let source = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
         pub type Callback = unsafe extern \"C\" fn(*mut i32) -> i32;\n\
         pub unsafe extern \"C\" fn target(p: *mut i32) -> i32 { *p }\n\
         pub fn __crat_safe_target() {}\n\
         pub static TABLE: [Option<Callback>; 1] = [Some(target as Callback)];\n";
    let fixture = Fixture::new(&[("lib.rs", source)]);
    let outcome = super::rewrite_m1_path_a5_injected(
        &fixture.root(),
        crate::analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay,
        Some(
            crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph,
        ),
        &|_| {},
    );
    let super::RewriteOutcome::Degraded {
        reason,
        source: unmodified,
        ..
    } = outcome
    else {
        panic!("a generated-name collision must hold/degrade: {outcome:#?}");
    };
    assert!(
        reason.contains("generated inner name collides: __crat_safe_target"),
        "{reason}"
    );
    assert_eq!(
        unmodified, source,
        "collision fallback must preserve input bytes"
    );
}

/// BR-W5b RED: thin depth-2 storage is presented as an NPO-compatible Option
/// and the out-parameter receives only a pointer to that Option storage.
#[test]
fn br_w5b_thin_const_and_mut_depth2_storage_use_npo_bridge() {
    let source = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
         unsafe extern \"C\" {\n\
             fn set_const(out: *mut *const i32, clear: bool);\n\
             fn set_mut(out: *mut *mut i32, clear: bool);\n\
         }\n\
         pub unsafe fn caller() {\n\
             let value = 7;\n\
             let mut mutable_value = 9;\n\
             let mut shared_slot: *const i32 = &value;\n\
             let mut mut_slot: *mut i32 = &mut mutable_value;\n\
             set_const(&mut shared_slot, false);\n\
             set_mut(&mut mut_slot, false);\n\
             set_const(&mut shared_slot, true);\n\
             set_mut(&mut mut_slot, true);\n\
         }\n";
    let fixture = Fixture::new(&[("lib.rs", source)]);
    let emission = ::utils::compilation::run_compiler_on_path(&fixture.root(), |tcx| {
        let (mut table, ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                crate::analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay,
                Some(
                    crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph,
                ),
            )),
        )
        .expect("BR-W5b decision table");
        for (subject, decision) in &mut table.entries {
            if subject.label.ends_with("caller::shared_slot") {
                *decision = super::decision::Decision::Opt {
                    mutable: false,
                    slice: false,
                    uses: Vec::new(),
                };
            } else if subject.label.ends_with("caller::mut_slot") {
                *decision = super::decision::Decision::Opt {
                    mutable: true,
                    slice: false,
                    uses: Vec::new(),
                };
            }
        }
        let raw_boundary = super::decision::raw_boundary::RawBoundaryDispositionIndex::derive(
            &ctx.raw_boundary_sites,
            &ctx.retention,
            &table,
            &ctx.facts,
            &ctx.mut_facts,
        );
        table.depth2_npo_storages = super::decision::plan_depth2_npo_storages(
            tcx,
            &table,
            &ctx.facts,
            &ctx.constructions,
        );
        table.seams = super::decision::seam::synthesize_with_raw_boundary(
            tcx,
            &ctx.facts,
            &ctx.subjects,
            &table,
            &ctx.retained_c9_plans,
            &ctx.a5_site_proofs,
            &raw_boundary,
            &ctx.coconv,
            &ctx.retention,
            &ctx.lifetime_eligibility,
        );
        let arm_requirements = super::derive_arm_requirements(
            &ctx.subjects,
            &table,
            &ctx.coconv,
            &raw_boundary,
            &ctx.exposure,
        );
        table.arm_requirements = arm_requirements;
        emit_files(
            tcx,
            &table,
            &rustc_hash::FxHashSet::default(),
            &ctx.retained_c9_plans,
        )
        .expect("BR-W5b emission")
    })
    .expect("BR-W5b source compiles");
    let source = text_for(&emission, "lib.rs").expect("BR-W5b emitted root");
    let materialized =
        verify::materialize(&fixture.root(), &emission.files).expect("materialize BR-W5b emission");
    assert!(
        verify::type_checks_crate(materialized.root()),
        "BR-W5b emitted tree must type-check:\n{source}"
    );
    assert!(
        source.contains("shared_slot: Option<&i32>"),
        "shared storage must use the NPO Option form:\n{source}"
    );
    assert!(
        source.contains("mut_slot: Option<&mut i32>"),
        "mutable storage must use the NPO Option form:\n{source}"
    );
    assert!(
        source.contains("core::ptr::from_mut(&mut shared_slot).cast::<*const i32>()"),
        "const-inner out-param bridge missing:\n{source}"
    );
    assert!(
        source.contains("core::ptr::from_mut(&mut mut_slot).cast::<*mut i32>()"),
        "mut-inner out-param bridge missing:\n{source}"
    );
    assert!(
        !source.contains("&mut &"),
        "live reference storage is forbidden: {source}"
    );
    let all_events = emission
        .plan
        .bridge_events(&std::collections::BTreeSet::new());
    let events = all_events
        .iter()
        .filter(|event| event.site.bridge_kind == "depth2-npo-bridge")
        .collect::<Vec<_>>();
    assert_eq!(
        events.len(),
        8,
        "four sites, each plan+terminal: {events:#?}"
    );
    assert!(events.iter().all(|event| {
        event.site.arm == "c" && event.state != super::bridge_receipt::BridgeReceiptState::Dropped
    }));
    assert!(events.iter().all(|event| {
        event.retention == super::bridge_receipt::BridgeRetentionTier::T2
            && event.waiver_id.as_deref() == Some(super::bridge_receipt::RAW_BOUNDARY_T2_WAIVER_ID)
    }));
    super::bridge_receipt::reconcile_bridge_events(&all_events)
        .expect("BR-W5b bridge events reconcile");

    let value = 1;
    let mut shared = Some(&value);
    let shared_raw = core::ptr::from_mut(&mut shared).cast::<*const i32>();
    // SAFETY: R-A admits exactly this thin NPO-compatible storage write; the
    // null representation of Option<&T> is guaranteed to be None.
    unsafe { *shared_raw = core::ptr::null() };
    assert!(shared.is_none());

    let mut value = 2;
    let mut mutable = Some(&mut value);
    let mutable_raw = core::ptr::from_mut(&mut mutable).cast::<*mut i32>();
    // SAFETY: the mutable twin has the same guaranteed thin NPO layout.
    unsafe { *mutable_raw = core::ptr::null_mut() };
    assert!(mutable.is_none());
}

#[test]
fn br_w5b_fat_and_non_variable_depth2_storage_are_typed_holds() {
    let source = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
         unsafe extern \"C\" {\n\
             fn set_fat(out: *mut *const [i32]);\n\
             fn set_thin(out: *mut *const i32);\n\
         }\n\
         pub struct Holder { slot: *const i32 }\n\
         pub unsafe fn caller(slice: &[i32], p: *const i32) {\n\
             let mut fat_slot: *const [i32] = slice as *const [i32];\n\
             let mut holder = Holder { slot: p };\n\
             set_fat(&mut fat_slot);\n\
             set_thin(&mut holder.slot);\n\
         }\n";
    let receipt = ::utils::compilation::run_compiler_on_str(source, |tcx| {
        let (mut table, ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                crate::analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay,
                Some(
                    crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph,
                ),
            )),
        )
        .expect("BR-W5b negative decision table");
        for (subject, decision) in &mut table.entries {
            if subject.label.ends_with("caller::fat_slot") {
                *decision = super::decision::Decision::Opt {
                    mutable: false,
                    slice: true,
                    uses: Vec::new(),
                };
            }
        }
        super::decision::raw_boundary::RawBoundaryDispositionIndex::derive(
            &ctx.raw_boundary_sites,
            &ctx.retention,
            &table,
            &ctx.facts,
            &ctx.mut_facts,
        )
        .receipts_tsv()
    })
    .expect("BR-W5b negative source compiles");
    assert!(
        receipt.contains("depth2-fat-layout-incompatible"),
        "fat Option<&[T]> storage must not enter the NPO cast:\n{receipt}"
    );
    assert!(
        receipt.contains("depth2-storage-shape-held"),
        "field/projection storage must be held with its own reason:\n{receipt}"
    );
    assert!(
        !receipt.contains("\tdepth2-npo-bridge\t"),
        "a negative branch must not receive the admitted template:\n{receipt}"
    );
}

/// BR-W6 RED: a generic void pointer keeps its raw signature and receives an
/// explicit pointee-erasing raw view from each safe source.
#[test]
fn br_w6_void_generic_boundary_uses_from_ref_mut_then_cast() {
    let source = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
         unsafe extern \"C\" {\n\
             fn consume(p: *mut core::ffi::c_void);\n\
             fn observe(p: *const core::ffi::c_void);\n\
         }\n\
         pub unsafe fn caller(write: *mut i32, read: *const i32) {\n\
             consume(write as *mut core::ffi::c_void);\n\
             observe(read as *const core::ffi::c_void);\n\
         }\n";
    let attempt = raw_boundary_attempt_with(source, &|table| {
        for (subject, decision) in &mut table.entries {
            if subject.label.ends_with("caller::write") {
                *decision = super::decision::Decision::Ref { mutable: true };
            } else if subject.label.ends_with("caller::read") {
                *decision = super::decision::Decision::Ref { mutable: false };
            }
        }
    });
    let source = e2_root_text(&attempt);
    assert!(
        source.contains("consume(core::ptr::from_mut(write).cast::<core::ffi::c_void>())"),
        "mutable void bridge missing:\n{source}"
    );
    assert!(
        source.contains("observe(core::ptr::from_ref(read).cast::<core::ffi::c_void>())"),
        "shared void bridge missing:\n{source}"
    );
    assert!(
        e2_type_checks(&attempt),
        "BR-W6 emitted tree must type-check"
    );
    let all_events = attempt
        .emission
        .plan
        .bridge_events(&std::collections::BTreeSet::new());
    let events = all_events
        .iter()
        .filter(|event| event.site.bridge_kind == "void-generic-raw")
        .collect::<Vec<_>>();
    assert_eq!(
        events.len(),
        4,
        "two sites, each plan+terminal: {events:#?}"
    );
    assert!(events.iter().all(|event| {
        event.state != super::bridge_receipt::BridgeReceiptState::Dropped
            && matches!(
                event.retention,
                super::bridge_receipt::BridgeRetentionTier::T1
                    | super::bridge_receipt::BridgeRetentionTier::T2
            )
    }));
    super::bridge_receipt::reconcile_bridge_events(&all_events)
        .expect("BR-W6 bridge events reconcile");
}

/// D4-W1 — bridge-only type paths must resolve in the emitted program. This
/// fixture has no `libc` crate: the local pointee must use `crate::`, while the
/// universal void spelling must use `core::ffi::c_void`.
#[test]
fn d4_w1_bridge_pointee_paths_resolve_without_libc_crate() {
    let source = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
         pub mod types { pub struct Widget(pub i32); }\n\
         pub mod api {\n\
             use crate::types::Widget;\n\
             unsafe extern \"C\" {\n\
                 fn take_widget(p: *const Widget);\n\
                 fn take_void(p: *const core::ffi::c_void);\n\
             }\n\
             pub unsafe fn caller(widget: *const Widget, opaque: *const core::ffi::c_void) {\n\
                 take_widget(widget);\n\
                 take_void(opaque);\n\
             }\n\
         }\n";
    let attempt = raw_boundary_attempt_with(source, &|table| {
        for (subject, decision) in &mut table.entries {
            if subject.label.ends_with("caller::widget") {
                *decision = super::decision::Decision::Opt {
                    mutable: false,
                    slice: false,
                    uses: Vec::new(),
                };
            } else if subject.label.ends_with("caller::opaque") {
                *decision = super::decision::Decision::Ref { mutable: false };
            }
        }
    });
    let source = e2_root_text(&attempt);
    assert!(
        source.contains("core::ptr::null::<crate::types::Widget>()"),
        "local pointee path is not crate-relative:\n{source}"
    );
    assert!(
        source.contains(".cast::<core::ffi::c_void>()"),
        "void pointee path is not dependency-free:\n{source}"
    );
    assert!(!source.contains("::<src::"), "{source}");
    assert!(!source.contains("::<libc::c_void>"), "{source}");
    assert!(
        e2_type_checks(&attempt),
        "D4-W1 emitted tree must type-check without a libc dependency"
    );
}

/// BR-W7 RED: explicit raw-pointer mutability changes use the direction-named
/// pointer methods and never reverse them.
#[test]
fn br_w7_raw_const_mut_casts_use_the_exact_direction() {
    let source = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
         unsafe extern \"C\" {\n\
             fn wants_mut(p: *mut i32);\n\
             fn wants_const(p: *const i32);\n\
         }\n\
         pub unsafe fn caller(mutable: *mut i32, shared: *const i32) {\n\
             wants_const(mutable as *const i32);\n\
             wants_mut(shared as *mut i32);\n\
         }\n";
    let attempt = raw_boundary_attempt_with(source, &|table| {
        for (subject, decision) in &mut table.entries {
            if subject.label.ends_with("caller::mutable")
                || subject.label.ends_with("caller::shared")
            {
                *decision = super::decision::Decision::Degraded(super::decision::Degradation {
                    subject: subject.label.clone(),
                    site: "<br-w7-injected>".to_owned(),
                    reason: super::decision::DegradeReason::KindRaw,
                });
            }
        }
    });
    let source = e2_root_text(&attempt);
    assert!(
        source.contains("wants_const(mutable.cast_const())"),
        "{source}"
    );
    assert!(source.contains("wants_mut(shared.cast_mut())"), "{source}");
    assert!(!source.contains("mutable.cast_mut()"), "{source}");
    assert!(!source.contains("shared.cast_const()"), "{source}");
    assert!(
        e2_type_checks(&attempt),
        "BR-W7 emitted tree must type-check"
    );
    let events = attempt
        .emission
        .plan
        .bridge_events(&std::collections::BTreeSet::new());
    for kind in ["raw-cast-const", "raw-cast-mut"] {
        let pair = events
            .iter()
            .filter(|event| event.site.bridge_kind == kind)
            .collect::<Vec<_>>();
        assert_eq!(
            pair.len(),
            2,
            "exact plan/terminal pair for {kind}: {events:#?}"
        );
        assert!(pair.iter().all(|event| {
            event.retention == super::bridge_receipt::BridgeRetentionTier::T1
                && event.waiver_id.is_none()
        }));
    }
}

/// BR-W8 RED: a nullable safe source may satisfy a required safe contract by
/// the ruled one-evaluation unwrap, while a raw target maps None to typed null.
#[test]
fn br_w8_nullable_required_and_raw_null_map_are_exact() {
    let required_source = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
         pub unsafe fn required_shared(p: *const i32) { let _ = p; }\n\
         pub unsafe fn required_mut(p: *mut i32) { let _ = p; }\n\
         pub unsafe fn caller(shared: *const i32, mut writable: *mut i32) {\n\
             required_shared(shared);\n\
             required_mut(writable);\n\
         }\n";
    let required = e3_attempt_with(required_source, true, &|table| {
        for (subject, decision) in &mut table.entries {
            if subject.label.ends_with("caller::shared") {
                *decision = super::decision::Decision::Opt {
                    mutable: false,
                    slice: false,
                    uses: Vec::new(),
                };
            } else if subject.label.ends_with("caller::writable") {
                *decision = super::decision::Decision::Opt {
                    mutable: true,
                    slice: false,
                    uses: Vec::new(),
                };
            } else if subject.label.ends_with("required_shared::p") {
                *decision = super::decision::Decision::Ref { mutable: false };
            } else if subject.label.ends_with("required_mut::p") {
                *decision = super::decision::Decision::Ref { mutable: true };
            }
        }
    });
    let emitted = e2_root_text(&required);
    assert!(
        emitted.contains("required_shared(shared.unwrap())"),
        "{emitted}"
    );
    assert!(
        emitted.contains("required_mut(writable.as_mut().unwrap())"),
        "{emitted}"
    );
    assert!(
        e2_type_checks(&required),
        "required unwrap twins must type-check"
    );
    let required_events = required
        .emission
        .plan
        .bridge_events(&std::collections::BTreeSet::new());
    assert_eq!(
        required_events
            .iter()
            .filter(|event| event.site.bridge_kind == "nullable-required-unwrap")
            .count(),
        4,
        "{required_events:#?}"
    );

    let raw_source = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
         unsafe extern \"C\" { fn observe(p: *const i32); }\n\
         pub unsafe fn caller(p: *const i32) { observe(p); }\n";
    let raw = raw_boundary_attempt_with(raw_source, &|table| {
        for (subject, decision) in &mut table.entries {
            if subject.label.ends_with("caller::p") {
                *decision = super::decision::Decision::Opt {
                    mutable: false,
                    slice: false,
                    uses: Vec::new(),
                };
            }
        }
    });
    let emitted = e2_root_text(&raw);
    assert!(
        emitted.contains("p.as_deref().map_or(core::ptr::null::<i32>(), core::ptr::from_ref)"),
        "Option-to-raw must map None to typed null:\n{emitted}"
    );
    assert!(e2_type_checks(&raw), "raw null-map twin must type-check");
    let raw_events = raw
        .emission
        .plan
        .bridge_events(&std::collections::BTreeSet::new());
    assert_eq!(
        raw_events
            .iter()
            .filter(|event| event.site.bridge_kind == "option-to-raw-null-map")
            .count(),
        2,
        "{raw_events:#?}"
    );
}

/// BR-W9 RED: thin-to-slice and licensed slice-to-thin conversions use the
/// explicit standard-library forms rather than indexing or implicit coercion.
#[test]
fn br_w9_thin_slice_glue_uses_from_ref_mut_and_first() {
    let source = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
         pub unsafe fn slice_target(p: *mut i32, n: usize) { let _ = (p, n); }\n\
         pub unsafe fn thin_target(p: *const i32) { let _ = p; }\n\
         pub unsafe fn caller(thin: *mut i32, slice: *const i32) {\n\
             slice_target(thin, 1);\n\
             thin_target(slice);\n\
         }\n";
    let attempt = e3_attempt_with(source, true, &|table| {
        for (subject, decision) in &mut table.entries {
            if subject.label.ends_with("caller::thin") {
                *decision = super::decision::Decision::Ref { mutable: true };
            } else if subject.label.ends_with("caller::slice") {
                *decision = super::decision::Decision::Slice {
                    mutable: false,
                    uses: Vec::new(),
                };
            } else if subject.label.ends_with("slice_target::p") {
                *decision = super::decision::Decision::Slice {
                    mutable: true,
                    uses: Vec::new(),
                };
            } else if subject.label.ends_with("thin_target::p") {
                *decision = super::decision::Decision::Ref { mutable: false };
            }
        }
    });
    let emitted = e2_root_text(&attempt);
    assert!(
        emitted.contains("slice_target(core::slice::from_mut(thin), 1)"),
        "{emitted}"
    );
    assert!(
        emitted.contains("thin_target(slice.first().unwrap())"),
        "{emitted}"
    );
    assert!(e2_type_checks(&attempt), "BR-W9 twins must type-check");
    let events = attempt
        .emission
        .plan
        .bridge_events(&std::collections::BTreeSet::new());
    assert!(events.iter().any(|event| {
        event.site.bridge_kind == "thin-to-slice-mut"
            && event.stage == super::bridge_receipt::BridgeReceiptStage::Terminal
    }));
    assert!(events.iter().any(|event| {
        event.site.bridge_kind == "slice-to-thin-shared"
            && event.stage == super::bridge_receipt::BridgeReceiptStage::Terminal
    }));
}

/// BR-W10: the shared-reference-to-mutable-raw form is selected only from an
/// exact Foster-immutable local parameter fact.
#[test]
fn br_w10_foster_immutable_local_allows_shared_to_mut_raw() {
    let source = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
         pub unsafe fn read_local(p: *mut i32) -> i32 { *p }\n\
         pub unsafe fn caller(shared: *const i32) -> i32 {\n\
             read_local(shared as *mut i32)\n\
         }\n";
    let attempt = raw_boundary_attempt_with(source, &|table| {
        for (subject, decision) in &mut table.entries {
            if subject.label.ends_with("caller::shared") {
                *decision = super::decision::Decision::Ref { mutable: false };
            } else if subject.label.ends_with("read_local::p") {
                *decision = super::decision::Decision::Degraded(super::decision::Degradation {
                    subject: subject.label.clone(),
                    site: "<br-w10-injected>".to_owned(),
                    reason: super::decision::DegradeReason::KindRaw,
                });
            }
        }
    });
    let emitted = e2_root_text(&attempt);
    assert!(
        emitted.contains("read_local(core::ptr::from_ref(shared).cast_mut())"),
        "{emitted}"
    );
    assert!(attempt.receipt.contains("negative-write=foster-immutable"));
    assert!(
        e2_type_checks(&attempt),
        "Foster-immutable twin must type-check"
    );
    let events = attempt
        .emission
        .plan
        .bridge_events(&std::collections::BTreeSet::new());
    let pair = events
        .iter()
        .filter(|event| event.site.bridge_kind == "shared-ref-to-mut-raw")
        .collect::<Vec<_>>();
    assert_eq!(pair.len(), 2, "{events:#?}");
}

/// BR-W10/R-B negative matrix. Retention tier and the T2 waiver are downstream
/// of this verdict and therefore cannot turn any non-negative write fact into
/// permission.
#[test]
fn br_w10_write_stream_lifecycle_and_missing_evidence_all_hold() {
    let source = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
         #[repr(C)] pub struct FILE { _private: [u8; 0] }\n\
         pub unsafe fn write_local(p: *mut i32) { *p = 1; }\n\
         unsafe extern \"C\" {\n\
             fn printf(fmt: *const i8, ...) -> i32;\n\
             fn scanf(fmt: *const i8, ...) -> i32;\n\
             fn fputs(s: *const i8, stream: *mut FILE) -> i32;\n\
             fn free(p: *mut core::ffi::c_void);\n\
             fn opaque(p: *mut i32);\n\
         }\n\
         pub unsafe fn caller(\n\
             local: *const i32, read: *const i32, write: *const i32,\n\
             stream: *const FILE, life: *const i32, missing: *const i32,\n\
         ) {\n\
             write_local(local as *mut i32);\n\
             printf(b\"%p\\0\".as_ptr() as *const i8, read as *mut core::ffi::c_void);\n\
             scanf(b\"%d\\0\".as_ptr() as *const i8, write as *mut i32);\n\
             fputs(b\"x\\0\".as_ptr() as *const i8, stream as *mut FILE);\n\
             free(life as *mut core::ffi::c_void);\n\
             opaque(missing as *mut i32);\n\
         }\n";
    let receipt = ::utils::compilation::run_compiler_on_str(source, |tcx| {
        let (mut table, ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                crate::analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay,
                Some(
                    crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph,
                ),
            )),
        )
        .expect("BR-W10 evidence matrix");
        for (subject, decision) in &mut table.entries {
            if subject.label.starts_with("caller::") {
                *decision = super::decision::Decision::Ref { mutable: false };
            } else if subject.label.ends_with("write_local::p") {
                *decision = super::decision::Decision::Degraded(super::decision::Degradation {
                    subject: subject.label.clone(),
                    site: "<br-w10-injected>".to_owned(),
                    reason: super::decision::DegradeReason::KindRaw,
                });
            }
        }
        super::decision::raw_boundary::RawBoundaryDispositionIndex::derive(
            &ctx.raw_boundary_sites,
            &ctx.retention,
            &table,
            &ctx.facts,
            &ctx.mut_facts,
        )
        .receipts_tsv()
    })
    .expect("BR-W10 matrix source compiles");
    assert!(
        receipt.lines().any(|line| {
            line.contains("\tprintf\t")
                && line.contains("\tshared-ref-to-mut-raw\t")
                && line.contains("negative-write=libc-read-only")
        }),
        "{receipt}"
    );
    for detail in [
        "negative-write-absent:foster-mutable",
        "negative-write-absent:libc-access=write",
        "negative-write-absent:libc-access=stream",
        "negative-write-absent:libc-access=lifecycle",
        "negative-write-absent:foreign-contract-missing",
    ] {
        assert!(receipt.contains(detail), "missing {detail}:\n{receipt}");
    }
    assert_eq!(
        receipt.matches("\tshared-ref-to-mut-raw\t").count(),
        1,
        "only the read-only libc arm may bridge:\n{receipt}"
    );
}

/// BR-W11 RED: a safe value reaching an `as` sink must first acquire an
/// explicit raw view, while the already-supported Option null observation must
/// be accounted as its own ADDR/GLUE bridge rather than a generic subject use.
#[test]
fn br_w11_cast_sink_and_is_null_are_explicit_receipted_raw_ops() {
    let source = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
         pub unsafe fn cast_sink(p: *const i32) -> *const u8 { p as *const u8 }\n\
         pub unsafe fn nullable(p: *mut i32) -> bool { p.is_null() }\n";
    let attempt = raw_boundary_attempt_with(source, &|table| {
        for (subject, decision) in &mut table.entries {
            if subject.label.ends_with("cast_sink::p") {
                *decision = super::decision::Decision::Ref { mutable: false };
            }
        }
    });
    let emitted = e2_root_text(&attempt);
    assert!(
        emitted.contains("core::ptr::from_ref(p) as *const u8"),
        "{emitted}"
    );
    assert!(emitted.contains("p.is_none()"), "{emitted}");
    assert!(
        e2_type_checks(&attempt),
        "BR-W11 scalar raw ops must type-check"
    );
    let events = attempt
        .emission
        .plan
        .bridge_events(&std::collections::BTreeSet::new());
    for kind in ["raw-op-cast-sink", "raw-op-is-none"] {
        let pair = events
            .iter()
            .filter(|event| event.site.bridge_kind == kind)
            .collect::<Vec<_>>();
        assert_eq!(pair.len(), 2, "missing plan/terminal {kind}: {events:#?}");
        assert!(pair.iter().all(|event| event.site.arm == "addr"));
    }
}

/// BR-W11 RED: pointer equality owns the whole expression so nested operand
/// edits cannot collide. Slice operands compare data pointers, and an optional
/// operand maps None to a null whose pointee type is explicit.
#[test]
fn br_w11_ptr_eq_uses_slice_data_and_typed_option_null_views() {
    let source = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
         pub unsafe fn eq(p: *const i32, q: *const i32) -> bool { core::ptr::eq(p, q) }\n";
    let attempt = raw_boundary_attempt_with(source, &|table| {
        for (subject, decision) in &mut table.entries {
            if subject.label.ends_with("eq::p") {
                *decision = super::decision::Decision::Slice {
                    mutable: false,
                    uses: Vec::new(),
                };
            } else if subject.label.ends_with("eq::q") {
                *decision = super::decision::Decision::Opt {
                    mutable: false,
                    slice: false,
                    uses: Vec::new(),
                };
            }
        }
    });
    let emitted = e2_root_text(&attempt);
    assert!(
        emitted.contains("core::ptr::eq(p.as_ptr(),"),
        "{emitted}\n{}",
        attempt.receipt
    );
    assert!(
        emitted.contains("core::ptr::null::<i32>()"),
        "{emitted}\n{}",
        attempt.receipt
    );
    assert!(e2_type_checks(&attempt), "BR-W11 ptr::eq must type-check");
    let events = attempt
        .emission
        .plan
        .bridge_events(&std::collections::BTreeSet::new());
    let pair = events
        .iter()
        .filter(|event| event.site.bridge_kind == "raw-op-ptr-eq")
        .collect::<Vec<_>>();
    assert_eq!(
        pair.len(),
        4,
        "one plan/terminal pair per operand: {events:#?}"
    );
    assert!(
        pair.iter()
            .any(|event| event.site.position.contains("lhs="))
    );
    assert!(
        pair.iter()
            .any(|event| event.site.position.contains("rhs="))
    );
    assert!(
        pair.iter()
            .all(|event| event.site.position.contains("target=*const i32"))
    );
}

/// BR-W12 RED: one class exercises every inference-sensitive declaration
/// family. The static/table and raw wrapper keep explicit raw types, while the
/// generated return temporary and caller local receive the carried safe type.
#[test]
fn br_w12_local_static_wrapper_and_return_temp_types_are_explicit() {
    let source = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
         pub type Callback = unsafe fn(*const i32) -> *const i32;\n\
         pub unsafe fn target(p: *const i32) -> *const i32 { p }\n\
         pub static TABLE: [Option<Callback>; 1] = [Some(target as Callback)];\n\
         pub unsafe fn id(p: *const i32) -> *const i32 { p }\n\
         pub unsafe fn caller(p: *const i32) -> i32 { let q = id(p); *q }\n";
    let fixture = Fixture::new(&[("lib.rs", source)]);
    let outcome = super::rewrite_m1_path_a5_injected(
        &fixture.root(),
        crate::analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay,
        Some(
            crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph,
        ),
        &|_| {},
    );
    let super::RewriteOutcome::Emitted {
        source,
        raw_boundary_artifacts,
        ..
    } = outcome
    else {
        panic!("BR-W12 declaration fixture must emit: {outcome:#?}");
    };
    assert!(
        source.contains("static TABLE: [Option<Callback>; 1]"),
        "{source}"
    );
    assert!(
        source.contains("fn target(p: *const i32) -> *const i32"),
        "{source}"
    );
    assert!(source.contains("let __crat_result: &i32 ="), "{source}");
    assert!(source.contains("let q: &i32 = id(p)"), "{source}");
    let declarations = raw_boundary_artifacts
        .bridge_events
        .iter()
        .filter(|event| event.site.bridge_kind == "declaration-explicit-type")
        .collect::<Vec<_>>();
    for category in ["local", "static", "wrapper", "return-temp"] {
        assert!(
            declarations
                .iter()
                .any(|event| event.site.position.starts_with(category)),
            "missing {category} declaration receipt: {declarations:#?}"
        );
    }
    assert_eq!(
        declarations.len(),
        8,
        "four plan/terminal declaration pairs: {declarations:#?}"
    );
}

/// BR-W13 RED: a raw tail entering a lifetime-permitted safe return reuses the
/// inbound bridge algebra and belongs to the returning function's class.
#[test]
fn br_w13_raw_tail_to_safe_return_reuses_reborrow_and_lifetime_permit() {
    let source = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
         pub unsafe fn choose(p: *const i32) -> *const i32 { p }\n";
    let fixture = Fixture::new(&[("lib.rs", source)]);
    let outcome = super::rewrite_m1_path_a5_injected(
        &fixture.root(),
        crate::analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay,
        Some(
            crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph,
        ),
        &|_| {},
    );
    let super::RewriteOutcome::Emitted {
        source: emitted,
        raw_boundary_artifacts,
        ..
    } = outcome
    else {
        panic!("BR-W13 inbound return must emit: {outcome:#?}");
    };
    assert!(emitted.contains("unsafe { &*p }"), "{emitted}");
    let pair = raw_boundary_artifacts
        .bridge_events
        .iter()
        .filter(|event| event.site.bridge_kind == "return-raw-to-ref")
        .collect::<Vec<_>>();
    assert_eq!(pair.len(), 2, "{:#?}", raw_boundary_artifacts.bridge_events);
    assert!(pair.iter().all(|event| {
        event.site.owner_class.local_def_id() == event.site.caller
            && event.retention == super::bridge_receipt::BridgeRetentionTier::T1
            && event.waiver_id.is_none()
    }));
}

/// BR-W13 RED: a real raw exposure wrapper converts the safe inner return back
/// to its raw ABI and carries a return-specific class receipt.
#[test]
fn br_w13_surface_safe_return_to_raw_has_class_receipt() {
    let fixture = Fixture::new(&[(
        "lib.rs",
        "#![allow(dead_code, unused_unsafe)]\n\
         pub unsafe extern \"C\" fn api(p: *const i32) -> *const i32 { p }\n",
    )]);
    let outcome = super::rewrite_m1_path_with_emission_config(
        &fixture.root(),
        crate::analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay,
        Some(
            crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph,
        ),
        &super::EmissionRunConfig {
            configured_exposure: configured_exposure_input("api"),
        },
    );
    let super::RewriteOutcome::Emitted {
        source,
        raw_boundary_artifacts,
        ..
    } = outcome
    else {
        panic!("BR-W13 exposed return must emit: {outcome:#?}");
    };
    assert!(
        source.contains("core::ptr::from_ref(__crat_result)"),
        "{source}"
    );
    let pair = raw_boundary_artifacts
        .bridge_events
        .iter()
        .filter(|event| event.site.bridge_kind == "return-ref-to-raw")
        .collect::<Vec<_>>();
    assert_eq!(pair.len(), 2, "{:#?}", raw_boundary_artifacts.bridge_events);
    assert!(pair.iter().all(|event| {
        event.retention == super::bridge_receipt::BridgeRetentionTier::T1
            && event.waiver_id.is_none()
            && event.site.arm == "surface"
    }));
}

/// BR-W13 RED: an inferred receive declaration is still a seam owned by the
/// returned callee class; the caller's lack of a signature edit cannot orphan
/// its receipt.
#[test]
fn br_w13_caller_receive_is_owned_by_the_returned_callee_class() {
    let fixture = Fixture::new(&[(
        "lib.rs",
        "#![allow(dead_code, unused_unsafe)]\n\
         pub unsafe fn id(p: *const i32) -> *const i32 { p }\n\
         pub unsafe fn caller(p: *const i32) -> i32 { let q = id(p); *q }\n",
    )]);
    let outcome = super::rewrite_m1_path_a5_injected(
        &fixture.root(),
        crate::analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay,
        Some(
            crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph,
        ),
        &|_| {},
    );
    let super::RewriteOutcome::Emitted {
        source,
        raw_boundary_artifacts,
        ..
    } = outcome
    else {
        panic!("BR-W13 caller receive must emit: {outcome:#?}");
    };
    assert!(source.contains("let q: &i32 = id(p)"), "{source}");
    let pair = raw_boundary_artifacts
        .bridge_events
        .iter()
        .filter(|event| event.site.bridge_kind == "return-caller-receive-ref")
        .collect::<Vec<_>>();
    assert_eq!(pair.len(), 2, "{:#?}", raw_boundary_artifacts.bridge_events);
    assert!(pair.iter().all(|event| {
        matches!(event.site.callee, super::bridge_receipt::BridgeCalleeId::Local(callee)
            if callee == event.site.owner_class.local_def_id())
            && event.site.caller != event.site.owner_class.local_def_id()
            && event.site.position.contains("lifetime_plan=")
    }));
}

/// BR-W13/F98 negative: removing the exact subject permit while preserving the
/// already-finalized safe return plan must drop the return site and hold the
/// entire class. No downstream retention tier or waiver may recreate it.
#[test]
fn br_w13_raw_to_safe_return_without_exact_permit_holds_class() {
    let fixture = Fixture::new(&[(
        "lib.rs",
        "#![allow(dead_code, unused_unsafe)]\n\
         pub unsafe fn id(p: *const i32) -> *const i32 { p }\n",
    )]);
    let emission = ::utils::compilation::run_compiler_on_path(&fixture.root(), |tcx| {
        let (mut table, ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                crate::analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay,
                Some(
                    crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph,
                ),
            )),
        )
        .expect("BR-W13 negative decision table");
        let subject = table
            .entries
            .iter()
            .find(|(subject, _)| subject.label.ends_with("id::p"))
            .map(|(subject, _)| (subject.fn_did, subject.hir_id))
            .expect("id::p subject");
        let mut eligibility = ctx.lifetime_eligibility.clone();
        assert!(eligibility.remove_return_permit_for_test(subject));
        table.seams = super::decision::seam::synthesize_with_raw_boundary(
            tcx,
            &ctx.facts,
            &ctx.subjects,
            &table,
            &ctx.retained_c9_plans,
            &ctx.a5_site_proofs,
            &ctx.raw_boundary,
            &ctx.coconv,
            &ctx.retention,
            &eligibility,
        );
        let arm_requirements = super::derive_arm_requirements(
            &ctx.subjects,
            &table,
            &ctx.coconv,
            &ctx.raw_boundary,
            &ctx.exposure,
        );
        table.arm_requirements = arm_requirements;
        emit_files(
            tcx,
            &table,
            &rustc_hash::FxHashSet::default(),
            &ctx.retained_c9_plans,
        )
        .expect("BR-W13 negative emission")
    })
    .expect("BR-W13 negative fixture compiles");
    let events = emission
        .plan
        .bridge_events(&std::collections::BTreeSet::new());
    assert!(events.iter().any(|event| {
        event.site.bridge_kind == "return-lifetime-permit-absent"
            && event.stage == super::bridge_receipt::BridgeReceiptStage::Terminal
            && event.state == super::bridge_receipt::BridgeReceiptState::Dropped
    }));
    assert!(
        emission
            .plan
            .class_finalization
            .classes
            .values()
            .any(|class| matches!(
                class.disposition,
                super::plan::SignatureClassDisposition::Held(_)
            ))
    );
    if let Some(emitted) = text_for(&emission, "lib.rs") {
        assert!(emitted.contains("p: *const i32"), "{emitted}");
        assert!(!emitted.contains("unsafe { &*p }"), "{emitted}");
    }
}

/// LIFE-W1 RED: the returned mutable parameter and return slot are one emitted
/// lifetime group. A fresh return-only name (the former `'b`) is forbidden.
#[test]
fn life_w1_kazmath_return_reuses_the_origin_parameter_lifetime() {
    let fixture = Fixture::new(&[(
        "lib.rs",
        "#![allow(dead_code, unused_unsafe)]\n\
         pub unsafe fn kazmath(p_out: *mut i32, add: *const i32) -> *mut i32 {\n\
             *p_out += *add;\n\
             p_out\n\
         }\n",
    )]);
    let outcome = super::rewrite_m1_path_a5_injected(
        &fixture.root(),
        crate::analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay,
        Some(
            crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph,
        ),
        &|_| {},
    );
    let super::RewriteOutcome::Emitted { source, .. } = outcome else {
        panic!("LIFE-W1 kazmath shape must emit: {outcome:#?}");
    };
    assert!(
        source.contains("fn kazmath<'a>(p_out: &'a mut i32"),
        "{source}"
    );
    assert!(source.contains(") -> &'a mut i32"), "{source}");
    assert!(!source.contains("'b"), "{source}");
    assert!(source.contains("unsafe { &mut *p_out }"), "{source}");
}

/// LIFE-W2 RED: every permitted source of a multi-branch return joins the
/// return target before name allocation, so all three signature positions use
/// one lifetime and the receipt says it was reused.
#[test]
fn life_w2_multi_source_return_uses_one_common_lifetime_and_receipt() {
    let fixture = Fixture::new(&[(
        "lib.rs",
        "#![allow(dead_code, unused_unsafe)]\n\
         pub unsafe fn choose(a: *const i32, b: *const i32, pick: bool) -> *const i32 {\n\
             if pick { return a; }\n\
             b\n\
         }\n",
    )]);
    let outcome = super::rewrite_m1_path_a5_injected(
        &fixture.root(),
        crate::analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay,
        Some(
            crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph,
        ),
        &|_| {},
    );
    let super::RewriteOutcome::Emitted { source, .. } = outcome else {
        panic!("LIFE-W2 multi-source shape must emit: {outcome:#?}");
    };
    let receipt = ::utils::compilation::run_compiler_on_path(&fixture.root(), |tcx| {
        let (table, _) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                crate::analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay,
                Some(
                    crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph,
                ),
            )),
        )
        .expect("LIFE-W2 decision table");
        table.lifetime_plan.canonical_receipt(tcx)
    })
    .expect("LIFE-W2 fixture compiles");
    assert!(
        source.contains("fn choose<'a>(a: &'a i32, b: &'a i32, pick: bool) -> &'a i32"),
        "{source}"
    );
    assert!(!source.contains("'b") && !source.contains("'c"), "{source}");
    assert!(receipt.contains("return_lifetime_reused=true"), "{receipt}");
    assert!(receipt.contains("common_name=a"), "{receipt}");
}

fn pair_w1_outcome(source: &str) -> super::RewriteOutcome {
    let fixture = Fixture::new(&[("lib.rs", source)]);
    super::rewrite_m1_path_a5_injected(
        &fixture.root(),
        crate::analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay,
        Some(
            crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph,
        ),
        &|_| {},
    )
}

/// PAIR-W1 RED, A5-clear branch: disjoint fields sharing one aggregate root
/// stay safe on both positions and carry the existing site-audit proof.
#[test]
fn pair_w1_a5_clear_keeps_both_same_root_fields_safe() {
    let source = "#![allow(dead_code, unused_unsafe)]\n\
         pub struct Pair { pub left: i32, pub right: i32 }\n\
         pub unsafe fn update(a: *mut i32, b: *mut i32) { *a += 1; *b += 1; }\n\
         pub unsafe fn caller() {\n\
             let mut pair = Pair { left: 1, right: 2 };\n\
             update(&mut pair.left, &mut pair.right);\n\
         }\n";
    let outcome = pair_w1_outcome(source);
    let super::RewriteOutcome::Emitted {
        source,
        raw_boundary_artifacts,
        degradations,
        ..
    } = outcome
    else {
        panic!("PAIR-W1 clear branch must emit: {outcome:#?}");
    };
    assert!(
        source.contains("update(a: &mut i32, b: &mut i32)"),
        "degradations={degradations:#?}\n{source}"
    );
    assert!(
        source.contains("update(&mut pair.left, &mut pair.right)"),
        "{source}"
    );
    let clear = raw_boundary_artifacts
        .bridge_events
        .iter()
        .filter(|event| event.site.bridge_kind == "pair-a5-clear")
        .collect::<Vec<_>>();
    assert_eq!(
        clear.len(),
        4,
        "one pair per position: {:#?}",
        raw_boundary_artifacts.bridge_events
    );
}

/// PAIR-W1 RED, Copy branch: the read-only side may be snapshotted only through
/// the pre-existing C9 mark, which already carries Copy pointee and effect
/// ordering proof. No in-wave proof is synthesized.
#[test]
fn pair_w1_copy_read_uses_the_existing_c9_effect_carrier() {
    let source = "#![allow(dead_code, unused_unsafe)]\n\
         pub struct H { pub symbol: i32, pub previous: i32 }\n\
         pub unsafe fn update(write: *mut i32, read: *const i32) { *write = *read + 1; }\n\
         pub unsafe fn caller(h: *mut H) {\n\
             let q: *const i32 = &(*h).symbol;\n\
             update(&mut (*h).symbol, q);\n\
         }\n";
    let outcome = pair_w1_outcome(source);
    let super::RewriteOutcome::Emitted {
        source,
        raw_boundary_artifacts,
        degradations,
        ..
    } = outcome
    else {
        panic!("PAIR-W1 Copy branch must emit: {outcome:#?}");
    };
    assert!(
        source.contains("let __crat_c9_"),
        "degradations={degradations:#?}\npairs={}\n{source}",
        raw_boundary_artifacts.pairs,
    );
    assert!(source.contains(": i32 = *(q)"), "{source}");
    let snapshot = source.find("let __crat_c9_").expect("snapshot temp");
    let mutable_borrow = source
        .find("update(&mut (*h).symbol,")
        .expect("mutable call argument");
    assert!(snapshot < mutable_borrow, "{source}");
    assert!(
        source.contains("update(&mut (*h).symbol, &__crat_c9_"),
        "{source}"
    );
    let copy = raw_boundary_artifacts
        .bridge_events
        .iter()
        .filter(|event| event.site.bridge_kind == "pair-copy-snapshot")
        .collect::<Vec<_>>();
    assert_eq!(copy.len(), 2, "{:#?}", raw_boundary_artifacts.bridge_events);
    assert!(
        copy.iter()
            .all(|event| event.site.position.contains("carrier=c9"))
    );
}

/// PAIR-W1/A-2 RED: this source has a Copy read side but no existing C9
/// site/effect carrier. The Copy arm is `held-no-proof`; the site falls through
/// to the separately receipted T2 raw view.
#[test]
fn pair_w1_copy_shape_without_existing_carrier_is_held_then_t2() {
    let source = "#![allow(dead_code, unused_unsafe)]\n\
         pub unsafe fn update(write: *mut i32, read: *const i32) { *write = *read + 1; }\n\
         pub unsafe fn caller() {\n\
             let mut x = 1;\n\
             update(&mut x, &mut x);\n\
         }\n";
    let outcome = pair_w1_outcome(source);
    let super::RewriteOutcome::Emitted {
        source,
        raw_boundary_artifacts,
        ..
    } = outcome
    else {
        panic!("PAIR-W1 no-carrier fallback must emit: {outcome:#?}");
    };
    assert!(!source.contains("__crat_c9_"), "{source}");
    assert!(source.contains("let __crat_pair_raw_"), "{source}");
    assert!(
        raw_boundary_artifacts
            .pairs
            .contains("held-no-proof:c9-effect-carrier-absent;pair-t2"),
        "{}",
        raw_boundary_artifacts.pairs
    );
    assert!(raw_boundary_artifacts.bridge_events.iter().any(|event| {
        event.site.bridge_kind == "pair-t2-raw-view"
            && event.retention == super::bridge_receipt::BridgeRetentionTier::T2
            && event.waiver_id.as_deref() == Some(super::bridge_receipt::RAW_BOUNDARY_T2_WAIVER_ID)
    }));
}

/// PAIR-W1 RED, T2 branch: without a licensed Copy snapshot, the selected raw
/// view is materialized before the surviving mutable borrow and carries the
/// exact unsafe-bridge waiver.
#[test]
fn pair_w1_t2_raw_view_is_materialized_before_the_safe_borrow() {
    let source = "#![allow(dead_code, unused_unsafe)]\n\
         pub unsafe fn update(a: *mut i32, b: *mut i32) { *a += 1; *b += 1; }\n\
         pub unsafe fn caller() {\n\
             let mut x = 0;\n\
             update(&mut x, &mut x);\n\
         }\n";
    let outcome = pair_w1_outcome(source);
    let super::RewriteOutcome::Emitted {
        source,
        raw_boundary_artifacts,
        degradations,
        ..
    } = outcome
    else {
        panic!("PAIR-W1 T2 branch must emit: {outcome:#?}");
    };
    let temp = source
        .find("let __crat_pair_raw_")
        .unwrap_or_else(|| panic!("degradations={degradations:#?}\n{source}"));
    let borrow = source.find("update(&mut").expect("safe borrow");
    assert!(temp < borrow, "{source}");
    assert!(source.contains("core::ptr::from_mut(&mut x)"), "{source}");
    let raw = raw_boundary_artifacts
        .bridge_events
        .iter()
        .filter(|event| event.site.bridge_kind == "pair-t2-raw-view")
        .collect::<Vec<_>>();
    assert_eq!(raw.len(), 2, "{:#?}", raw_boundary_artifacts.bridge_events);
    assert!(raw.iter().all(|event| {
        event.retention == super::bridge_receipt::BridgeRetentionTier::T2
            && event.waiver_id.as_deref() == Some(super::bridge_receipt::RAW_BOUNDARY_T2_WAIVER_ID)
    }));
}

/// PAIR-W1/G18: when both same-object positions may retain the pointer there is
/// no lawful raw-view side. T2 is not spent and the class is held with the
/// positive-retention reason.
#[test]
fn pair_w1_positive_retention_holds_instead_of_spending_t2() {
    let source = "#![allow(dead_code, unused_unsafe)]\n\
         pub unsafe fn retain(a: *mut i32, b: *mut i32, pick: bool) -> *mut i32 {\n\
             *a += 1; *b += 1;\n\
             if pick { a } else { b }\n\
         }\n\
         pub unsafe fn caller() {\n\
             let mut x = 0;\n\
             let _ = retain(&mut x, &mut x, false);\n\
         }\n";
    let fixture = Fixture::new(&[("lib.rs", source)]);
    let pairs = ::utils::compilation::run_compiler_on_path(&fixture.root(), |tcx| {
        let (_, ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                crate::analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay,
                Some(
                    crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph,
                ),
            )),
        )
        .expect("PAIR-W1 positive-retention table");
        ctx.raw_boundary_artifacts.pairs
    })
    .expect("PAIR-W1 positive-retention fixture compiles");
    assert!(
        pairs.contains("\tblocked\tblocked\tpair-positive-retention\t"),
        "{pairs}"
    );
    let outcome = pair_w1_outcome(source);
    let (emitted, artifacts) = match &outcome {
        super::RewriteOutcome::Emitted {
            source,
            raw_boundary_artifacts,
            ..
        }
        | super::RewriteOutcome::Degraded {
            source,
            raw_boundary_artifacts,
            ..
        } => (source, raw_boundary_artifacts),
    };
    assert!(!emitted.contains("__crat_pair_raw_"), "{outcome:#?}");
    assert!(!artifacts.bridge_events.iter().any(|event| {
        event.site.bridge_kind == "pair-t2-raw-view"
            && event.state == super::bridge_receipt::BridgeReceiptState::Applied
    }));
}

/// E2-X1 RED — the consumer-neutral carrier already reaches `finish_decide`,
/// but E2-FN has no consumer yet. The lifetime producer must receive the intact
/// summary object rather than an A5-shaped projection of it.
#[test]
fn e2_x1_carrier_reaches_the_lifetime_producer_intact() {
    let fixture = Fixture::new(&[(
        "lib.rs",
        "#![allow(dead_code, unused_unsafe)]\n\
         pub unsafe fn id(p: *const i32) -> *const i32 { p }\n",
    )]);
    let receipt = ::utils::compilation::run_compiler_on_path(&fixture.root(), |tcx| {
        let (_, ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                crate::analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay,
                Some(
                    crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph,
                ),
            )),
        )
        .expect("E2-X1 decision table");
        super::decision::lifetime::carrier_receipt(ctx.analysis.origins.as_ref())
    })
    .expect("E2-X1 fixture compiles before rewriting");

    assert!(receipt.summary_count > 0, "{receipt:?}");
    assert!(receipt.native_flows, "{receipt:?}");
}

/// E2-W1 RED — a modeled argument-to-return origin must create the private
/// permit and let the existing decision ladder pass the return-escape gate.
#[test]
fn e2_w1_return_decision_uses_the_typed_permit() {
    let fixture = Fixture::new(&[(
        "lib.rs",
        "#![allow(dead_code, unused_unsafe)]\n\
         pub unsafe fn id(p: *mut i32) -> *mut i32 { p }\n",
    )]);
    let (decision, permits) =
        ::utils::compilation::run_compiler_on_path(&fixture.root(), |tcx| {
            let (table, ctx) = super::decide_table_with_ctx_config(
                tcx,
                Some((
                    crate::analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay,
                    Some(
                        crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph,
                    ),
                )),
            )
            .expect("E2-W1 decision table");
            let decision = table
                .entries
                .iter()
                .find(|(subject, _)| subject.label.ends_with("id::p"))
                .map(|(_, decision)| decision.clone())
                .expect("id::p subject");
            (decision, ctx.lifetime_eligibility.return_permit_count())
        })
        .expect("E2-W1 fixture compiles before rewriting");

    assert!(
        matches!(decision, super::decision::Decision::Ref { mutable: false }),
        "{decision:#?}"
    );
    assert_eq!(permits, 1);
}

/// Addendum-117 RED — an origin-backed return permit removes only the
/// return-escape blocker. If a later ordinary raw-flow blocker then wins, the
/// E2 ledger must name that secondary degradation and retain its typed payload;
/// it must neither call the row planned nor drop the later reason.
#[test]
fn e2_w8_return_permit_reports_secondary_degradation_payload() {
    let fixture = Fixture::new(&[(
        "lib.rs",
        "#![allow(dead_code, unused_unsafe)]\n\
         static mut HOLD: *mut i32 = core::ptr::null_mut();\n\
         type P = *mut i32;\n\
         pub unsafe fn raw_sink(p: P) -> usize { HOLD = p; 0 }\n\
         pub unsafe fn returns_after_raw_flow(p: *mut i32) -> *mut i32 {\n\
             *p = 1;\n\
             let _ = raw_sink(p);\n\
             p\n\
         }\n",
    )]);
    let (permits, subjects) =
        ::utils::compilation::run_compiler_on_path(&fixture.root(), |tcx| {
            let (_, ctx) = super::decide_table_with_ctx_config(
                tcx,
                Some((
                    crate::analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay,
                    Some(
                        crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph,
                    ),
                )),
            )
            .expect("E2-W8 decision table");
            (
                ctx.lifetime_eligibility.return_permit_count(),
                ctx.e2_artifacts.subjects,
            )
        })
        .expect("E2-W8 fixture compiles before rewriting");

    assert_eq!(permits, 1, "{subjects}");
    let row = subjects
        .lines()
        .skip(1)
        .find(|row| row.contains("returns_after_raw_flow::p#"))
        .unwrap_or_else(|| panic!("E2-W8 subject missing:\n{subjects}"));
    let fields = row.split('\t').collect::<Vec<_>>();
    assert_eq!(
        fields[receipt_column(&subjects, "final_decision")],
        "flows-into-raw-param",
        "{row}",
    );
    assert_eq!(
        fields[receipt_column(&subjects, "e2_disposition")],
        "lifetime-secondary-degradation",
        "{row}",
    );
    assert_eq!(
        fields[receipt_column(&subjects, "secondary_reason")],
        "flows-into-raw-param",
        "{row}",
    );
    assert_eq!(
        fields[receipt_column(&subjects, "secondary_reason_detail")],
        "flows-into-raw-param",
        "{row}",
    );
}

/// Addendum-120 collateral RED — `ClassBlocked { via }` means the blocker is
/// owned by a classmate. Even when `via` names return escape, the permitted row
/// receives the secondary class and keeps `(class-blocked, via)` as payload.
#[test]
fn e2_w9_classmate_primary_is_secondary_class_coupling() {
    let decision = super::decision::Decision::Degraded(super::decision::Degradation {
        subject: "permitted-row".to_owned(),
        site: "fixture".to_owned(),
        reason: super::decision::DegradeReason::ClassBlocked {
            via: super::decision::co_conversion::BlockReason::EscapesViaReturn,
        },
    });
    let disposition = super::e2_terminal_disposition(false, true, None, &decision)
        .expect("class coupling is a secondary disposition");

    assert_eq!(
        disposition.key(),
        "lifetime-secondary-degradation",
        "{disposition:?}",
    );
    assert_eq!(
        disposition.secondary_payload(),
        ("class-blocked".to_owned(), "escapes-via-return".to_owned()),
    );
}

/// Addendum-121 RED — the collateral row itself need not carry a permit. The
/// `ClassBlocked` variant already says a classmate owns `via`, so this row must
/// retain the secondary class and payload even with no direct permit.
#[test]
fn e2_w9b_permitless_classmate_coupling_is_secondary() {
    let decision = super::decision::Decision::Degraded(super::decision::Degradation {
        subject: "permitless-collateral-row".to_owned(),
        site: "fixture".to_owned(),
        reason: super::decision::DegradeReason::ClassBlocked {
            via: super::decision::co_conversion::BlockReason::EscapesViaReturn,
        },
    });
    let disposition = super::e2_terminal_disposition(false, false, None, &decision)
        .expect("permit-less class coupling is a secondary disposition");

    assert_eq!(
        disposition.key(),
        "lifetime-secondary-degradation",
        "{disposition:?}",
    );
    assert_eq!(
        disposition.secondary_payload(),
        ("class-blocked".to_owned(), "escapes-via-return".to_owned()),
    );
}

/// Addendum-120 invariant RED — a permitted row cannot retain its own direct
/// return-escape blocker. That state is a typed construction failure, not a
/// secondary disposition and not `not-e2`.
#[test]
fn e2_n8_permitted_own_primary_is_loud_invariant_violation() {
    let decision = super::decision::Decision::Degraded(super::decision::Degradation {
        subject: "permitted-row".to_owned(),
        site: "fixture".to_owned(),
        reason: super::decision::DegradeReason::SilentCoercion {
            via: super::decision::co_conversion::BlockReason::EscapesViaReturn,
        },
    });
    let error = super::e2_terminal_disposition(false, true, None, &decision)
        .expect_err("an own-primary blocker must stop artifact construction");

    assert_eq!(error.key(), "lifetime-invariant-permitted-own-primary");
    assert_eq!(
        error.payload(),
        (
            "escapes-via-return".to_owned(),
            "escapes-via-return".to_owned()
        ),
    );
}

/// E2-W7 RED — an unannotated local fed by a direct local call may use the
/// callee's modeled lifetime plan without inventing a local declaration
/// splice.  The explicit decision arm is load-bearing: treating this as an
/// ordinary `Ref` would let the no-`ty_span` residual gate erase the evidence.
#[test]
fn e2_w7_direct_call_result_local_is_inferred_safe() {
    let fixture = Fixture::new(&[(
        "lib.rs",
        "#![allow(dead_code, unused_unsafe)]\n\
         pub unsafe fn id(p: *const i32) -> *const i32 { p }\n\
         pub unsafe fn caller(p: *const i32) -> i32 {\n\
             let q = id(p);\n\
             *q\n\
         }\n",
    )]);
    let (decision, return_permits, inferred_permits, failure) =
        ::utils::compilation::run_compiler_on_path(&fixture.root(), |tcx| {
        let (table, ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                crate::analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay,
                Some(
                    crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph,
                ),
            )),
        )
        .expect("E2-W7 decision table");
        let (subject, decision) = table
            .entries
            .iter()
            .find(|(subject, _)| subject.label.ends_with("caller::q"))
            .expect("caller::q subject");
        (
            decision.clone(),
            ctx.lifetime_eligibility.return_permit_count(),
            ctx.lifetime_eligibility.inferred_permit_count(),
            ctx.lifetime_eligibility
                .failure((subject.fn_did, subject.hir_id)),
        )
    })
    .expect("E2-W7 fixture compiles before rewriting");

    assert!(
        matches!(
            decision,
            super::decision::Decision::InferredRef { mutable: false, .. }
        ),
        "decision={decision:#?}; return_permits={return_permits}; \
         inferred_permits={inferred_permits}; failure={failure:?}"
    );
}

/// E2-W7 conservative controls — allocator, foreign, and indirect results may
/// not acquire an inferred local lifetime merely because their accepted model
/// happens to contain a reference-shaped slot.
#[test]
fn e2_w7_only_a_direct_local_call_result_may_be_inferred_safe() {
    fn observed(
        source: &str,
        suffix: &str,
    ) -> (
        super::decision::Decision,
        Option<super::decision::lifetime::LifetimeFailure>,
    ) {
        let fixture = Fixture::new(&[("lib.rs", source)]);
        ::utils::compilation::run_compiler_on_path(&fixture.root(), |tcx| {
            let (table, ctx) = super::decide_table_with_ctx_config(
                tcx,
                Some((
                    crate::analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay,
                    Some(
                        crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph,
                    ),
                )),
            )
            .expect("E2-W7 negative decision table");
            let (subject, decision) = table
                .entries
                .iter()
                .find(|(subject, _)| subject.label.ends_with(suffix))
                .expect("negative-control subject");
            (
                decision.clone(),
                ctx.lifetime_eligibility
                    .failure((subject.fn_did, subject.hir_id)),
            )
        })
        .expect("E2-W7 negative fixture compiles before rewriting")
    }

    let (allocator, _) = observed(
        "#![allow(dead_code, unused_unsafe)]\n\
         unsafe extern \"C\" { fn malloc(n: usize) -> *mut core::ffi::c_void; }\n\
         pub unsafe fn caller() -> *mut i32 {\n\
             let q = malloc(4) as *mut i32;\n\
             q\n\
         }\n",
        "caller::q",
    );
    assert!(
        !matches!(allocator, super::decision::Decision::InferredRef { .. }),
        "allocator result gained an inferred lifetime: {allocator:#?}"
    );

    let (foreign, foreign_failure) = observed(
        "#![allow(dead_code, unused_unsafe)]\n\
         unsafe extern \"C\" { fn foreign(p: *const i32) -> *const i32; }\n\
         pub unsafe fn caller(p: *const i32) -> i32 {\n\
             let q = foreign(p);\n\
             *q\n\
         }\n",
        "caller::q",
    );
    assert!(
        !matches!(foreign, super::decision::Decision::InferredRef { .. }),
        "foreign result gained an inferred lifetime: {foreign:#?}"
    );
    assert_eq!(
        foreign_failure,
        Some(super::decision::lifetime::LifetimeFailure::ExternalContractAbsent)
    );

    let (indirect, indirect_failure) = observed(
        "#![allow(dead_code, unused_unsafe)]\n\
         unsafe fn id(p: *const i32) -> *const i32 { p }\n\
         pub unsafe fn caller(p: *const i32) -> i32 {\n\
             let f: unsafe fn(*const i32) -> *const i32 = id;\n\
             let q = f(p);\n\
             *q\n\
         }\n",
        "caller::q",
    );
    assert!(
        !matches!(indirect, super::decision::Decision::InferredRef { .. }),
        "indirect result gained an inferred lifetime: {indirect:#?}"
    );
    assert_eq!(
        indirect_failure,
        Some(super::decision::lifetime::LifetimeFailure::FnPtrWebHeld)
    );
}

/// E2-W3 RED — output storage receives the modeled source lifetime, not the
/// temporary local used to carry the call argument.  The permit is keyed to
/// the field-free signature-depth slot (`*out`), so a later AST pass has no
/// opportunity to substitute an implementation temporary.
#[test]
fn e2_w3_output_storage_uses_source_not_temp_lifetime() {
    let fixture = Fixture::new(&[(
        "lib.rs",
        "#![allow(dead_code, unused_unsafe)]\n\
         pub unsafe fn store(out: *mut *const i32, p: *const i32) {\n\
             *out = p;\n\
         }\n",
    )]);
    let (receipt, diagnostic) =
        ::utils::compilation::run_compiler_on_path(&fixture.root(), |tcx| {
        let (_, ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                crate::analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay,
                Some(
                    crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph,
                ),
            )),
        )
        .expect("E2-W3 decision table");
        let mut diagnostic = Vec::new();
        if let Some(origins) = ctx.analysis.origins.as_ref() {
            for (&did, summary) in origins.iter() {
                if !tcx.def_path_str(did.to_def_id()).ends_with("store") {
                    continue;
                }
                for (origin, slot) in summary.slots.iter_enumerated() {
                    let local = match slot.place.root {
                        crate::analyses::borrow_ownership::origin_summary::SignatureRoot::Arg(local) => local,
                        crate::analyses::borrow_ownership::origin_summary::SignatureRoot::Return => rustc_middle::mir::RETURN_PLACE,
                    };
                    let depth = slot.place.deref_depth.saturating_add(slot.depth);
                    let kind = ctx
                        .slots
                        .fn_local_slots
                        .get(&did)
                        .and_then(|universe| universe.slot_for_local_depth(local, depth))
                        .and_then(|slot| ctx.model.get(&crate::analyses::borrow_ownership::solver::SlotRef::Local(did, slot)))
                        .copied();
                    let incoming = summary
                        .slots
                        .indices()
                        .filter(|source| summary.subset.contains(*source, origin))
                        .map(|source| format!("{source:?}"))
                        .collect::<Vec<_>>();
                    diagnostic.push(format!(
                        "{origin:?}={:?}/deref{}/depth{} model={kind:?} unknown={} incoming={incoming:?}",
                        slot.place.root,
                        slot.place.deref_depth,
                        slot.depth,
                        summary.unknown.contains(origin),
                    ));
                }
            }
        }
        (
            ctx.lifetime_eligibility.output_storage_receipts(),
            diagnostic,
        )
    })
    .expect("E2-W3 fixture compiles before rewriting");

    assert_eq!(
        receipt.len(),
        1,
        "receipt={receipt:#?}; summary={diagnostic:#?}"
    );
    assert_eq!(receipt[0].source, "arg2/deref0/depth0");
    // NB5-O represents this raw-pointer layer as signature `depth=1`; the
    // separate `deref_depth` component is reserved for a projected place.
    assert_eq!(receipt[0].target, "arg1/deref0/depth1");
}

/// E2-W1/BR-W13 structural witness — the production AST path materializes the
/// lifetime plan and the return-site reborrow. Separate SCC names make the
/// accepted source-to-return direction visible as one reused `'a`.
#[test]
fn e2_w1_production_emits_named_signature_lifetimes() {
    let fixture = Fixture::new(&[(
        "lib.rs",
        "#![allow(dead_code, unused_unsafe)]\n\
         pub unsafe fn id(p: *const i32) -> *const i32 { p }\n",
    )]);
    let outcome = super::rewrite_m1_path_a5_injected(
        &fixture.root(),
        crate::analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay,
        Some(
            crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph,
        ),
        &|_| {},
    );
    let super::RewriteOutcome::Emitted { files, .. } = outcome else {
        panic!("E2-W1 production rewrite must survive: {outcome:#?}");
    };
    let emitted = files
        .values()
        .find(|source| source.contains("fn id"))
        .expect("emitted E2-W1 function");
    assert!(emitted.contains("fn id<'a>"), "{emitted}");
    assert!(emitted.contains("p: &'a i32"), "{emitted}");
    assert!(emitted.contains("-> &'a i32"), "{emitted}");
    let signature = emitted
        .lines()
        .find(|line| line.contains("fn id"))
        .expect("E2-W1 emitted signature line");
    assert_eq!(
        signature, "pub unsafe fn id<'a>(p: &'a i32) -> &'a i32 { unsafe { &*p } }",
        "the lifetime and return bridge must move this exact structural line",
    );
}

/// E2-W2/W3/W5 production-path coverage: multiple source bounds, nested
/// output storage, and collision-free insertion beside user generics all pass
/// through the same structural visitor as E2-W1.
#[test]
fn e2_structural_plan_covers_bounds_output_storage_and_existing_generics() {
    let fixture = Fixture::new(&[(
        "lib.rs",
        "#![allow(dead_code, unused_unsafe, unused_lifetimes)]\n\
         pub unsafe fn choose(a: *const i32, b: *const i32, pick: bool) -> *const i32 {\n\
             if pick { return a; }\n\
             b\n\
         }\n\
         pub unsafe fn store(out: *mut *const i32, p: *const i32) { *out = p; }\n\
         pub unsafe fn existing<'a, T>(p: *const T) -> *const T { p }\n",
    )]);
    let outcome = super::rewrite_m1_path_a5_injected(
        &fixture.root(),
        crate::analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay,
        Some(
            crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph,
        ),
        &|_| {},
    );
    let super::RewriteOutcome::Emitted { files, .. } = outcome else {
        panic!("E2 structural fixture must survive: {outcome:#?}");
    };
    let emitted = files
        .values()
        .find(|source| source.contains("fn choose"))
        .expect("emitted E2 structural fixture");
    assert!(emitted.contains("fn choose<'a>"), "{emitted}");
    assert!(
        emitted.contains("fn store<'a, 'b: 'a>(out: &mut &'a i32, p: &'b i32)"),
        "{emitted}"
    );
    assert!(emitted.contains("fn existing<'a, 'b, T>"), "{emitted}");
}

/// E2-W2/R165-2 — body-local reassignment does not create an analysis relation,
/// but the typed multi-source return permit intentionally joins both source
/// groups with the return before emitted-name allocation.
#[test]
fn e2_w2_local_reassignment_reuses_the_common_return_lifetime() {
    let source = "#![allow(dead_code, unused_unsafe, unused_assignments)]\n\
         pub unsafe fn cross(\n\
             mut a: *const i32,\n\
             mut b: *const i32,\n\
             choose_a: bool,\n\
         ) -> *const i32 {\n\
             if choose_a { a = b; } else { b = a; }\n\
             if choose_a { return a; }\n\
             b\n\
         }\n";
    let fixture = Fixture::new(&[("lib.rs", source)]);
    let plan_dump = ::utils::compilation::run_compiler_on_path(&fixture.root(), |tcx| {
        let (table, _) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                crate::analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay,
                Some(
                    crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph,
                ),
            )),
        )
        .expect("E2-W2 local-reassignment decision table");
        let (did, plan) = table
            .lifetime_plan
            .functions()
            .find(|(did, _)| tcx.def_path_str(did.to_def_id()).ends_with("cross"))
            .expect("E2-W2 local-reassignment plan");
        let arg1 = super::decision::lifetime::FnSignatureSlot::arg(1, 0, 0);
        let arg2 = super::decision::lifetime::FnSignatureSlot::arg(2, 0, 0);
        let mutual = plan
            .sccs
            .iter()
            .filter(|scc| scc.contains(&arg1) || scc.contains(&arg2))
            .collect::<Vec<_>>();
        assert_eq!(mutual.len(), 1, "{}: {}", tcx.def_path_str(did.to_def_id()), plan.receipt());
        assert_eq!(plan.lifetime_for(arg1), plan.lifetime_for(arg2));
        assert!(plan.outlives.iter().all(|(longer, shorter)| longer != shorter));
        assert!(plan.receipt().contains("return_lifetime_reused=true"));
        plan.receipt()
    })
    .expect("E2-W2 local-reassignment fixture compiles before rewriting");

    let outcome = super::rewrite_m1_path_a5_injected(
        &fixture.root(),
        crate::analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay,
        Some(
            crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph,
        ),
        &|_| {},
    );
    let super::RewriteOutcome::Emitted { files, .. } = outcome else {
        panic!("E2-W2 common lifetime must emit: plan={plan_dump}; outcome={outcome:#?}");
    };
    let emitted = files
        .values()
        .find(|text| text.contains("fn cross"))
        .expect("E2-W2 emitted function");
    assert!(
        emitted.contains("fn cross<'a>(")
            && emitted.contains("mut a: &'a i32")
            && emitted.contains("mut b: &'a i32")
            && emitted.contains("-> &'a i32"),
        "plan={plan_dump}; source={emitted}",
    );
}

/// E2-W2b — caller-visible cross-storage makes the two output signature slots
/// mutually reachable. The structural plan assertion, not compilation alone,
/// is what kills omission of SCC collapse.
#[test]
fn e2_w2b_mutual_output_storage_collapses_and_emits() {
    let source = "#![allow(dead_code, unused_unsafe)]\n\
         pub unsafe fn cross_store(x: *mut *const i32, y: *mut *const i32) {\n\
             let tmp = *x;\n\
             *x = *y;\n\
             *y = tmp;\n\
         }\n";
    let fixture = Fixture::new(&[("lib.rs", source)]);
    let plan_dump = ::utils::compilation::run_compiler_on_path(&fixture.root(), |tcx| {
        let (table, _) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                crate::analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay,
                Some(
                    crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph,
                ),
            )),
        )
        .expect("E2-W2b decision table");
        let (did, plan) = table
            .lifetime_plan
            .functions()
            .find(|(did, _)| tcx.def_path_str(did.to_def_id()).ends_with("cross_store"))
            .expect("E2-W2b cross-storage plan");
        let x = super::decision::lifetime::FnSignatureSlot::arg(1, 0, 1);
        let y = super::decision::lifetime::FnSignatureSlot::arg(2, 0, 1);
        let mutual = plan
            .sccs
            .iter()
            .filter(|scc| scc.contains(&x) || scc.contains(&y))
            .collect::<Vec<_>>();
        assert_eq!(mutual.len(), 1, "{}: {}", tcx.def_path_str(did.to_def_id()), plan.receipt());
        assert_eq!(mutual[0], &vec![x, y], "{}", plan.receipt());
        assert_eq!(plan.lifetime_for(x), plan.lifetime_for(y));
        assert!(
            plan.outlives.iter().all(|(longer, shorter)| longer != shorter),
            "{}",
            plan.receipt(),
        );
        plan.receipt()
    })
    .expect("E2-W2b fixture compiles before rewriting");

    let outcome = super::rewrite_m1_path_a5_injected(
        &fixture.root(),
        crate::analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay,
        Some(
            crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph,
        ),
        &|_| {},
    );
    let super::RewriteOutcome::Emitted { files, .. } = outcome else {
        panic!("E2-W2b emitted signature failed: plan={plan_dump}; outcome={outcome:#?}");
    };
    let emitted = files
        .values()
        .find(|text| text.contains("fn cross_store"))
        .expect("E2-W2b emitted function");
    assert!(
        emitted.contains("x: &mut &'a i32") && emitted.contains("y: &mut &'a i32"),
        "plan={plan_dump}; emitted={emitted}",
    );
}

/// E2-W6 RED — a call adapter owned by a lifetime-bearing callee carries that
/// exact plan identity, evaluates the source expression once, and survives the
/// ordinary production verifier as one atomic function-owned rewrite.
#[test]
fn e2_w6_lifetime_callee_keeps_adapter_one_evaluation() {
    let source = "#![allow(dead_code, unused_unsafe)]\n\
         unsafe extern \"C\" { fn source() -> *const i32; }\n\
         pub unsafe fn first(p: *const i32) -> *const i32 { p }\n\
         pub unsafe fn caller() -> i32 { *first(source()) }\n";
    let fixture = Fixture::new(&[("lib.rs", source)]);
    let receipt = ::utils::compilation::run_compiler_on_path(&fixture.root(), |tcx| {
        let (table, _) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                crate::analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay,
                Some(
                    crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph,
                ),
            )),
        )
        .expect("E2-W6 decision table");
        super::seam_tsv_from_table(tcx, &table)
    })
    .expect("E2-W6 fixture compiles before rewriting");
    let digest_column = receipt_column(&receipt, "lifetime_plan_digest");
    let placed = receipt
        .lines()
        .skip(1)
        .map(|line| line.split('\t').collect::<Vec<_>>())
        .find(|columns| columns.first() == Some(&"placed"))
        .expect("E2-W6 placed adapter row");
    assert_ne!(placed[digest_column], "-", "{receipt}");

    let outcome = super::rewrite_m1_path_a5_injected(
        &fixture.root(),
        crate::analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay,
        Some(
            crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph,
        ),
        &|_| {},
    );
    let super::RewriteOutcome::Emitted { files, .. } = outcome else {
        panic!("E2-W6 production rewrite must survive: {outcome:#?}");
    };
    let emitted = files
        .values()
        .find(|text| text.contains("fn first"))
        .expect("E2-W6 emitted source");
    assert!(emitted.contains("fn first<'a>"), "{emitted}");
    assert_eq!(emitted.matches("source()").count(), 2, "{emitted}");
}

/// E2-N3/N4 RED — boundary and field tranches stay closed, but their refusal
/// is typed by E2 rather than disappearing behind the ordinary degradation.
#[test]
fn e2_n3_n4_external_and_field_rows_are_loudly_held() {
    fn inspect(
        source: &str,
        suffix: &str,
    ) -> (
        &'static str,
        super::decision::lifetime::LifetimeFailure,
        String,
    ) {
        let fixture = Fixture::new(&[("lib.rs", source)]);
        ::utils::compilation::run_compiler_on_path(&fixture.root(), |tcx| {
            let (table, ctx) = super::decide_table_with_ctx_config(
                tcx,
                Some((
                    crate::analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay,
                    Some(
                        crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph,
                    ),
                )),
            )
            .expect("E2-N3/N4 decision table");
            let (subject, decision) = table
                .entries
                .iter()
                .find(|(subject, _)| subject.label.ends_with(suffix))
                .expect("held subject");
            let disposition = match decision {
                super::decision::Decision::Ref { .. } => "ref",
                super::decision::Decision::InferredRef { .. } => "inferred-ref",
                super::decision::Decision::Slice { .. } => "slice",
                super::decision::Decision::Opt { .. } => "optional",
                super::decision::Decision::Box(_) => "box",
                super::decision::Decision::Degraded(_) => "degraded",
            };
            let failure = ctx
                .lifetime_eligibility
                .failure((subject.fn_did, subject.hir_id))
                .expect("row must retain its E2 analysis fact");
            (
                disposition,
                failure,
                ctx.raw_boundary_artifacts.dispositions.clone(),
            )
        })
        .expect("E2-N3/N4 fixture compiles before rewriting")
    }

    let (external_disposition, external_failure, external_receipts) = inspect(
        "#![allow(dead_code, unused_unsafe)]\n\
         unsafe extern \"C\" { fn retain(p: *const i32); }\n\
         pub unsafe fn f(p: *const i32) { retain(p); }\n",
        "f::p",
    );
    assert_eq!(external_disposition, "ref");
    assert_eq!(
        external_failure,
        super::decision::lifetime::LifetimeFailure::ExternalContractAbsent,
        "E2 analysis facts are frozen; only the final disposition moves"
    );
    assert!(
        external_receipts.lines().skip(1).any(|line| {
            let fields = line.split('\t').collect::<Vec<_>>();
            fields.get(6) == Some(&"f::p#1")
                && fields.get(10) == Some(&"T2")
                && fields.get(11) == Some(&"ref-shared-to-raw-const")
                && fields.get(12) == Some(&super::decision::raw_boundary::RAW_BOUNDARY_WAIVER_ID)
        }),
        "external disposition lacks its exact confirmed-T2 receipt: {external_receipts}"
    );

    let (field_disposition, field_failure, _) = inspect(
        "#![allow(dead_code, unused_unsafe)]\n\
         pub struct Holder { pub p: *const i32 }\n\
         pub unsafe fn f(h: *mut Holder, p: *const i32) { (*h).p = p; }\n",
        "f::p",
    );
    assert_eq!(field_disposition, "degraded");
    assert_eq!(
        field_failure,
        super::decision::lifetime::LifetimeFailure::FieldHeld,
    );
}

/// C-W4 / deliberate E2-N7 transition. The address-taken root gets a positive
/// seed shim and its forward web member gets a raw wrapper, so both safe inner
/// signatures may now consume E2 lifetime plans without changing the web type.
#[test]
fn c_w4_fnptr_web_members_open_only_behind_ruled_surfaces() {
    let fixture = Fixture::new(&[(
        "lib.rs",
        "#![allow(dead_code, unused_unsafe)]\n\
         pub unsafe fn leaf(p: *const i32) -> *const i32 { p }\n\
         pub unsafe fn root(p: *const i32) -> *const i32 { let _ = leaf(p); p }\n\
         pub unsafe fn install() {\n\
             let _callback: unsafe fn(*const i32) -> *const i32 = root;\n\
         }\n",
    )]);
    ::utils::compilation::run_compiler_on_path(&fixture.root(), |tcx| {
        let (table, ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                crate::analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay,
                Some(
                    crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph,
                ),
            )),
        )
        .expect("E2-N7 eligibility decision table");
        for suffix in ["leaf::p", "root::p"] {
            let (subject, decision) = table
                .entries
                .iter()
                .find(|(subject, _)| subject.label.ends_with(suffix))
                .unwrap_or_else(|| panic!("missing {suffix}"));
            assert!(
                matches!(decision, super::decision::Decision::Ref { .. }),
                "{suffix} did not reach its safe inner: {decision:#?}",
            );
            let failure = ctx
                .lifetime_eligibility
                .failure((subject.fn_did, subject.hir_id));
            assert_eq!(failure, None, "{suffix}: {decision:#?}");
            assert!(table.lifetime_plan.function(subject.fn_did).is_some());
            let expected = if suffix == "root::p" {
                super::decision::exposure::ExposureSurfacePlan::PositiveSeedShim
            } else {
                super::decision::exposure::ExposureSurfacePlan::FnPtrRawWrapper
            };
            assert_eq!(ctx.exposure.plan(subject.fn_did), expected);
        }
    })
    .expect("E2-N7 eligibility fixture compiles");
}

/// E2-N5 RED — an on-disk cache hit must reproduce the consumed model, A5
/// receipt, finalized lifetime plan, and structurally emitted source bytes.
#[test]
fn e2_n5_cache_and_fresh_paths_share_plan_model_a5_and_source_bytes() {
    let fixture = Fixture::new(&[(
        "lib.rs",
        "#![allow(dead_code, unused_unsafe)]\n\
         pub unsafe fn id(p: *const i32) -> *const i32 { p }\n",
    )]);
    let cache_dir = fixture.0.join("cache");
    std::fs::create_dir_all(&cache_dir).expect("E2-N5 cache directory");

    let run = |read: bool| {
        ::utils::compilation::run_compiler_on_path(&fixture.root(), |tcx| {
            crate::analyses::borrow_ownership::model_cache::reset_for_test();
            crate::analyses::borrow_ownership::model_cache::with_test_config(
                read,
                &cache_dir,
                || {
                let capture = super::ast_transform::capture_ast(tcx)?;
                let (table, ctx) = super::decide_table_with_ctx_config(
                    tcx,
                    Some((
                        crate::analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay,
                        Some(
                            crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph,
                        ),
                    )),
                )?;
                let model = crate::analyses::borrow_ownership::model_cache::model_bytes_sha256(
                    tcx,
                    &ctx.slots,
                    &ctx.model,
                )
                .ok_or_else(|| "E2-N5 model key did not render".to_owned())?;
                let (files, _, _) = super::ast_transform::ast_emitted_files_from(
                    tcx,
                    &capture,
                    &super::ast_transform::RevertSet::default(),
                    None,
                    &table,
                )?;
                let provenance =
                    crate::analyses::borrow_ownership::model_cache::last_solve()
                        .ok_or_else(|| "E2-N5 solve provenance missing".to_owned())?;
                Ok::<_, String>((
                    format!(
                        "model={model}\na5={}\nplan={}\nsource={files:?}",
                        ctx.a5_receipt,
                        table.lifetime_plan.canonical_receipt(tcx),
                    ),
                    provenance.source,
                    provenance.solve_secs,
                ))
                },
            )
        })
        .expect("E2-N5 fixture compiles")
    };

    let (fresh, fresh_source, _) = run(false).expect("E2-N5 fresh path");
    assert_eq!(fresh_source, "real");

    let (cached, cached_source, cached_solve_secs) = run(true).expect("E2-N5 cached path");
    assert_eq!(cached_source, "cache");
    assert_eq!(cached_solve_secs, 0.0);
    assert_eq!(cached, fresh);
    crate::analyses::borrow_ownership::model_cache::reset_for_test();
}

/// Task 29 — path-independent lifetime plans/receipts and off-tranche source
/// identity across two distinct source roots.
#[test]
fn e2_n5_two_roots_share_plan_receipts_and_unowned_source_bytes() {
    let source = "#![allow(dead_code, unused_unsafe)]\n\
         pub unsafe fn id(p: *const i32) -> *const i32 { p }\n\
         pub fn untouched(x: i32) -> i32 { x + 1 }\n";
    let left = Fixture::new(&[("lib.rs", source)]);
    let right = Fixture::new(&[("lib.rs", source)]);
    assert_ne!(left.0, right.0);

    let run = |fixture: &Fixture| {
        ::utils::compilation::run_compiler_on_path(&fixture.root(), |tcx| {
            let capture = super::ast_transform::capture_ast(tcx)?;
            let (table, ctx) = super::decide_table_with_ctx_config(
                tcx,
                Some((
                    crate::analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay,
                    Some(
                        crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph,
                    ),
                )),
            )?;
            let (files, _, _) = super::ast_transform::ast_emitted_files_from(
                tcx,
                &capture,
                &super::ast_transform::RevertSet::default(),
                None,
                &table,
            )?;
            let emitted = files
                .values()
                .find(|text| text.contains("fn id"))
                .cloned()
                .ok_or_else(|| "E2 two-root source missing".to_owned())?;
            Ok::<_, String>((
                table.lifetime_plan.canonical_receipt(tcx),
                ctx.e2_artifacts.subjects,
                ctx.e2_artifacts.functions,
                ctx.e2_artifacts.failures,
                emitted,
            ))
        })
        .expect("E2 two-root fixture compiles")
        .expect("E2 two-root derivation")
    };

    let left = run(&left);
    let right = run(&right);
    assert_eq!(left, right);
    assert!(
        left.4.contains("pub fn untouched(x: i32) -> i32 { x + 1 }"),
        "off-tranche function moved:\n{}",
        left.4,
    );
}

/// E2-N6 — lifetime diagnostics are one-iteration row data, not a false
/// success. Both missing lifetime selection and an omitted input constraint
/// must reach the repaired full-analysis observer with their rustc codes.
#[test]
fn e2_n6_compile_errors_surface_as_iteration_data() {
    let missing = Fixture::new(&[(
        "lib.rs",
        "pub fn choose(a: &i32, b: &i32, pick: bool) -> &i32 {\n\
             if pick { a } else { b }\n\
         }\n",
    )]);
    let missing_diagnosis = super::verify::diagnose_crate(&missing.root());
    assert!(missing_diagnosis.errors > 0);
    assert!(
        missing_diagnosis
            .diags
            .iter()
            .any(|diag| matches!(diag.code.as_deref(), Some("E0106" | "ErrCode(106)"))),
        "{missing_diagnosis:#?}"
    );

    let constraint = Fixture::new(&[(
        "lib.rs",
        "pub fn choose<'a>(a: &i32, b: &'a i32, pick: bool) -> &'a i32 {\n\
             if pick { a } else { b }\n\
         }\n",
    )]);
    let constraint_diagnosis = super::verify::diagnose_crate(&constraint.root());
    assert!(constraint_diagnosis.errors > 0);
    assert!(
        constraint_diagnosis.diags.iter().any(|diag| matches!(
            diag.code.as_deref(),
            Some("E0621" | "E0623" | "ErrCode(621)" | "ErrCode(623)")
        )),
        "{constraint_diagnosis:#?}"
    );
}

/// E2 task-22 exact-once receipt control: one table drives subject, function,
/// failure, and seam artifacts, and the typed lifetime justification carries
/// the same digest as the function row.
#[test]
fn e2_receipts_reconcile_subject_function_and_plan_identity_once() {
    let fixture = Fixture::new(&[(
        "lib.rs",
        "#![allow(dead_code, unused_unsafe)]\n\
         pub unsafe fn id(p: *const i32) -> *const i32 { p }\n",
    )]);
    let (entries, artifacts) =
        ::utils::compilation::run_compiler_on_path(&fixture.root(), |tcx| {
            let (table, ctx) = super::decide_table_with_ctx_config(
                tcx,
                Some((
                    crate::analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay,
                    Some(
                        crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph,
                    ),
                )),
            )
            .expect("E2 receipt decision table");
            (table.entries.len(), ctx.e2_artifacts)
        })
        .expect("E2 receipt fixture compiles");

    let subjects = artifacts.subjects.lines().skip(1).collect::<Vec<_>>();
    assert_eq!(subjects.len(), entries, "{}", artifacts.subjects);
    assert_eq!(
        subjects
            .iter()
            .map(|row| row.split('\t').next().unwrap())
            .collect::<std::collections::BTreeSet<_>>()
            .len(),
        entries,
        "{}",
        artifacts.subjects,
    );
    let functions = artifacts.functions.lines().skip(1).collect::<Vec<_>>();
    assert_eq!(functions.len(), 1, "{}", artifacts.functions);
    let function_digest = functions[0].split('\t').nth(1).expect("function digest");
    let subject_digest = subjects[0].split('\t').nth(9).expect("subject digest");
    assert_eq!(subject_digest, function_digest);
    assert!(subjects[0].contains("\tplanned\tlifetime-plan\t"));
    assert_eq!(
        artifacts.failures.lines().count(),
        1,
        "{}",
        artifacts.failures
    );
    assert!(artifacts.seams.starts_with("kind\towner_fn\t"));
}

fn receipt_column(receipt: &str, name: &str) -> usize {
    receipt
        .lines()
        .next()
        .expect("receipt header")
        .split('\t')
        .position(|column| column == name)
        .unwrap_or_else(|| panic!("missing receipt column {name}: {receipt}"))
}

/// E-ADAPT-W3-W1 — a same-root field pair that the frozen A5 site producer
/// proves disjoint discharges SiteOverlap and reaches the existing slice seam.
#[test]
fn e_adapt_w3_w1_proven_disjoint_site_emits_its_slice_adapter() {
    let attempt = e3_attempt(E3_CLEAR_RAW, true, true);
    let header = attempt
        .receipt
        .lines()
        .next()
        .expect("receipt header")
        .split('\t')
        .collect::<Vec<_>>();
    assert_eq!(
        header
            .iter()
            .copied()
            .collect::<std::collections::BTreeSet<_>>()
            .len(),
        header.len(),
        "every receipt column name must be unique: {header:?}"
    );
    let verdict = receipt_column(&attempt.receipt, "overlap_verdict");
    let guard = receipt_column(&attempt.receipt, "overlap_a5_abi_guard");
    let placed = attempt
        .receipt
        .lines()
        .skip(1)
        .map(|line| line.split('\t').collect::<Vec<_>>())
        .filter(|row| row.first() == Some(&"placed"))
        .collect::<Vec<_>>();
    assert_eq!(placed.len(), 2, "{}", attempt.receipt);
    assert!(placed.iter().all(|row| row[verdict] == "clear"));
    assert!(
        placed
            .iter()
            .all(|row| { row[guard] == "permitted:measurement-frozen-graph-attested" })
    );
    assert!(
        e2_root_text(&attempt).contains("core::slice::from_raw_parts_mut"),
        "{}",
        e2_root_text(&attempt)
    );
}

/// E-ADAPT-W3-N1 — a genuine overlap remains closed even under attestation.
#[test]
fn e_adapt_w3_n1_overlapping_site_stays_closed() {
    let attempt = e3_attempt(E3_OVERLAP, true, true);
    assert!(
        attempt.receipt.lines().any(|line| {
            line.starts_with("blocked\t")
                && line.contains("\toverlapping\t")
                && line.contains("a5-not-proven-disjoint")
        }),
        "{}",
        attempt.receipt
    );
    assert!(attempt.emission.files.is_empty());
    assert!(
        attempt
            .emission
            .plan
            .class_finalization
            .classes
            .values()
            .all(|class| !class.is_ready())
    );
}

/// E-ADAPT-W3-N2 — a clear site with no required glue is recorded but never
/// changed. Clear is evidence for one gate, not an edit command.
#[test]
fn e_adapt_w3_n2_clear_template_none_is_untouched() {
    let attempt = e3_attempt(E3_CLEAR_REFS, true, false);
    assert!(
        attempt.receipt.lines().any(|line| {
            line.starts_with("overlap-proof\t")
                && line.contains("\tnone\t")
                && line.contains("\tclear\t")
        }),
        "{}",
        attempt.receipt
    );
    assert!(
        e2_root_text(&attempt).contains("target(&mut *left, &mut *right);"),
        "the call argument must remain byte-shaped as written:\n{}",
        e2_root_text(&attempt)
    );
    assert!(!e2_root_text(&attempt).contains("core::slice::"));
}

/// E-ADAPT-W3-N3 — the identical closed-world-dependent site fails closed when
/// the attestation is absent. Product default remains refusal.
#[test]
fn e_adapt_w3_n3_unattested_site_fails_closed_with_typed_reason() {
    let attempt = e3_attempt(E3_CLEAR_RAW, false, true);
    assert!(
        attempt.receipt.lines().any(|line| {
            line.starts_with("blocked\t")
                && line.contains("\tundeterminable\t")
                && line.contains("seam-a5-attestation-absent")
        }),
        "{}",
        attempt.receipt
    );
    assert!(attempt.emission.files.is_empty());
}

/// E-ADAPT-W3-N6 — evidence-backed extents remain preferred after the overlap
/// gate opens. Both raw slice arguments have their own following count.
#[test]
fn e_adapt_w3_n6_clear_site_prefers_licensed_extent() {
    let attempt = e3_attempt_with(E3_CLEAR_LICENSED, true, &force_wave3_target_slices);
    let len_arm = receipt_column(&attempt.receipt, "len_arm");
    let placed = attempt
        .receipt
        .lines()
        .skip(1)
        .map(|line| line.split('\t').collect::<Vec<_>>())
        .filter(|row| row.first() == Some(&"placed"))
        .collect::<Vec<_>>();
    assert_eq!(placed.len(), 2, "{}", attempt.receipt);
    assert!(placed.iter().all(|row| row[len_arm] == "len-following"));
    assert!(!e2_root_text(&attempt).contains("FALLBACK_SLICE_EXTENT"));
}

/// E-ADAPT-W3-N7 — absent sound extent evidence uses only the named fallback,
/// and the receipt carries the fabricated arm.
#[test]
fn e_adapt_w3_n7_clear_site_receipts_named_fallback_extent() {
    let attempt = e3_attempt(E3_CLEAR_RAW, true, true);
    let len_arm = receipt_column(&attempt.receipt, "len_arm");
    let placed = attempt
        .receipt
        .lines()
        .skip(1)
        .map(|line| line.split('\t').collect::<Vec<_>>())
        .filter(|row| row.first() == Some(&"placed"))
        .collect::<Vec<_>>();
    assert_eq!(placed.len(), 2, "{}", attempt.receipt);
    assert!(placed.iter().all(|row| row[len_arm] == "len-fabricated"));
    assert_eq!(
        e2_root_text(&attempt)
            .matches("const FALLBACK_SLICE_EXTENT: usize = 1024;")
            .count(),
        1
    );
}

/// E-ADAPT-W3-N8 — two calls to the same target receive independent site
/// verdicts: the clear site opens and the overlapping neighbor stays closed.
#[test]
fn e_adapt_w3_n8_site_key_does_not_license_an_overlapping_neighbor() {
    let attempt = e3_attempt_with(E3_SCOPED_PAIR, true, &force_wave3_target_slices);
    let proof_rows = attempt
        .receipt
        .lines()
        .filter(|line| line.starts_with("overlap-proof\t"))
        .collect::<Vec<_>>();
    assert_eq!(proof_rows.len(), 4, "{}", attempt.receipt);
    assert_eq!(
        proof_rows
            .iter()
            .filter(|row| row.contains("\tclear\tall-peers-clear\t"))
            .count(),
        2
    );
    assert_eq!(
        proof_rows
            .iter()
            .filter(|row| row.contains("\toverlapping\tat-least-one-peer-overlapping\t"))
            .count(),
        2
    );
    assert!(
        attempt.emission.files.is_empty(),
        "one blocked site holds the callee signature and both call-site adapters"
    );
}

/// **A BLOCKED seam row names the CALLEE in `owner_fn`, and the caller in its
/// own column.**
///
/// `owner_fn` is the REVERT KEY. On a `placed` row it has always been the
/// callee — `a_reverted_callee_takes_its_seams_with_it` is the property — but a
/// `blocked` row carried the CALLER there, so one column meant two things by
/// row kind. The consequence was not cosmetic: a refused seam costs the
/// **callee's** conversion, so *"which functions would gain if this refusal
/// went away"* could only be answered on the axis that does not revert. That is
/// how the fabricated-length slice's own upside was nearly priced wrong.
///
/// The caller is real information and moves to its own column rather than being
/// dropped.
///
/// *Mutation-tested:* swapping the two back — `owner_fn` = caller, trailing
/// column = callee — fails both assertions, and each on its own.
#[test]
fn a_null_literal_seam_row_names_both_call_parties_and_the_literal_arm() {
    let src = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
               pub unsafe fn callee(p: *mut i32) -> i32 {\n\
               \x20   if p.is_null() { 0 } else { *p }\n\
               }\n\
               pub fn caller() {\n\
               \x20   unsafe { callee(0 as *mut i32); }\n\
               }\n";
    let fixture = Fixture::new(&[("lib.rs", src)]);
    let tsv = ::utils::compilation::run_compiler_on_path(&fixture.0.join("lib.rs"), |tcx| {
        super::seam_tsv(tcx).expect("seam census")
    })
    .expect("fixture compiles");

    let hdr: Vec<&str> = tsv.lines().next().expect("header").split('\t').collect();
    let col = |n: &str| hdr.iter().position(|h| *h == n).expect("column present");
    let (c_owner, c_caller, c_null) = (col("owner_fn"), col("caller"), col("null_arm"));
    let placed: Vec<Vec<&str>> = tsv
        .lines()
        .skip(1)
        .map(|l| l.split('\t').collect::<Vec<_>>())
        .filter(|f| f.first() == Some(&"placed"))
        .collect();
    assert_eq!(
        placed.len(),
        1,
        "one literal-None position expected:\n{tsv}"
    );
    assert!(
        placed[0][c_owner].ends_with("callee"),
        "`owner_fn` must be the CALLEE — it is the revert key on every row \
         kind:\n{tsv}"
    );
    assert!(
        placed[0][c_caller].ends_with("caller"),
        "the caller must be recorded, not dropped:\n{tsv}"
    );
    assert_eq!(placed[0][c_null], "literal-none", "{tsv}");
}

/// **`render` RUNS OUTSIDE THE COMPILER SESSION, AND THE CONST STILL LANDS.**
///
/// The reproduction of the defect the first fabrication emit sweep found: four
/// of twenty programs panicked at
/// `scoped-tls: cannot access a scoped thread local variable without calling
/// set first`, and they were exactly the four in which a fabricated adapter
/// SURVIVED into a verify/revert round.
///
/// `rewrite_core`'s `TyCtxt` closure ends before the verify loop, so the loop's
/// three `render` calls have **no session globals**. Building the const there
/// parsed and pretty-printed — both of which need them.
///
/// **Why the existing witness could not catch it:**
/// `the_fabricated_const_follows_the_surviving_adapters` calls `render` INSIDE
/// `run_compiler_on_path`. It exercised the function in a context production
/// does not have, so it was green while production panicked. *A witness has to
/// run where the code runs* — M-F7's lesson one layer down, and this one cost a
/// 625 s sweep.
///
/// *Mutation-tested:* move the `fabricated_len_item()` call back into `render`
/// and this test panics rather than failing an assertion — which is the defect,
/// reproduced.
#[test]
fn render_outside_a_compiler_session_omits_an_unused_const() {
    const SRC: &str = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
                       pub unsafe fn fab_total(buf: *mut i32) -> i32 {\n\
                       \x20   let mut s: i32 = 0;\n\
                       \x20   let mut i: usize = 0;\n\
                       \x20   while i < 4 { s += *buf.offset(i as isize); i += 1; }\n\
                       \x20   s\n\
                       }\n\
                       pub unsafe fn fab_one(d: *mut i32) -> i32 { fab_total(d) }\n";
    let fixture = Fixture::new(&[("lib.rs", SRC)]);
    // Everything that needs a session happens INSIDE it, and only data escapes.
    let (plan, texts) =
        ::utils::compilation::run_compiler_on_path(&fixture.0.join("lib.rs"), |tcx| {
            let table = decide_table(tcx).expect("decides");
            let e = emit_files(tcx, &table, &rustc_hash::FxHashSet::default(), &[]).expect("emits");
            (e.plan, e.texts)
        })
        .expect("fixture compiles");

    assert!(
        plan.len_const_item.is_some(),
        "the const's text must be produced while a session exists, or the          insertion fail-closes outside one"
    );

    // ---- and NOW, with no session anywhere on this thread ----
    let (files, rollbacks, _) = super::validate_plan(&plan, &texts);
    assert!(rollbacks.is_empty());
    let n: usize = files
        .values()
        .map(|t| {
            t.matches("const FALLBACK_SLICE_EXTENT: usize = 1024;")
                .count()
        })
        .sum();
    assert_eq!(n, 0, "safe-to-safe glue needs no fabricated extent");
}

/// **BOTH LAYERS EMIT THE CONST, AND AGREE ON IT.**
///
/// Found by mutation **M-F7**: disabling the AST layer's const arm entirely left
/// the suite at 1247/6/28 — byte-identical to baseline. The arm was live
/// production code in the **layer of record** with no witness at all, because
/// the only thing exercising the AST emitter is the golden set and **no golden
/// carries a fabricated position** (measured: 0 across all 21).
///
/// The obvious answer — "g26 will witness it" — is the answer this milestone has
/// learned to refuse. g26 is a ratification event that has not happened yet, and
/// an arm whose only witness is a fixture someone still has to approve is an arm
/// shipping unwitnessed in the meantime.
///
/// *Mutation-tested:* the M-F7 mutation that survived the whole suite fails
/// here.
/// **W1 — the AST layer HONOURS a non-empty revert set.**
///
/// The standing gap, registered at the fabrication close: *"every existing
/// cross-layer witness runs with an empty revert set."* The verify/revert loop
/// reverts on every round but the first, so an emitter that ignored its revert
/// set would re-convert exactly the functions the previous round took back —
/// silently, and the loop would never converge.
///
/// **Reading could not settle this.** The comment in `ast_emitted_source` said
/// `transform_inner` "builds its visitors with an explicitly EMPTY revert set";
/// it had been false since M-2/A task 1 threaded `reverts` through. This test is
/// the empirical answer.
///
/// *Mutation-tested* (M-W1-a): drop `reverted_fns` from the decl visitor's
/// construction, or pass `&RevertSet::default()` to `transform_with`, and the
/// `revert_me` half fails — the reverted function converts.
#[test]
fn a_reverted_fn_keeps_its_raw_declaration() {
    const SRC: &str = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
                       pub unsafe fn keep_me(p: *mut i32) -> i32 { *p }\n\
                       pub unsafe fn revert_me(q: *mut i32) -> i32 { *q }\n";

    // Both convert with an EMPTY revert set — the control that makes the
    // reverted half non-vacuous. Without it, "revert_me stayed raw" would be
    // satisfied by a fixture that never converted at all.
    let none = ast_emitted_source_of(SRC).expect("the AST layer emits");
    assert!(
        !none.contains("p: *mut i32") && !none.contains("q: *mut i32"),
        "CONTROL: both params must convert under an empty revert set, or the \
         reverted half below proves nothing:\n{none}"
    );

    // Now revert exactly one of them.
    let one = super::ast_emitted_source_of_reverting(SRC, "revert_me::q#1")
        .expect("the AST layer emits under a revert set");
    assert!(
        one.contains("q: *mut i32"),
        "REVERTED: `revert_me` must keep its raw declaration — an emitter that \
         ignores its revert set re-converts what the previous round took \
         back:\n{one}"
    );
    assert!(
        !one.contains("p: *mut i32"),
        "KEPT: `keep_me` must still convert — reverting one function may not \
         revert the crate:\n{one}"
    );
}

/// **The one-capture-per-session fact, measured rather than cited.**
///
/// `ast_emitted_source` captures on every call, so a loop calling it per round
/// would fail on round 2. That is why the loop uses
/// `ast_emitted_source_from` against a single round-0 capture — a design
/// constraint, not a performance choice.
///
/// *Mutation-tested* (M-W1-b): make `capture_ast` memoize and return the same
/// capture twice and this fails, which is the point — a memoizing capture would
/// make the split look unnecessary while quietly handing out a krate whose
/// resolver is already consumed.
#[test]
fn a_second_capture_in_one_session_fails() {
    const SRC: &str = "#![allow(dead_code)]\npub unsafe fn f(p: *mut i32) -> i32 { *p }\n";
    let (first, second) = super::two_captures_in_one_session(SRC).expect("session runs");
    assert!(
        first,
        "the FIRST capture must succeed, or the second proves nothing"
    );
    assert!(
        !second,
        "a SECOND capture in one session must fail — the loop's one-capture \
         design rests on this, and if it ever starts succeeding the split in \
         `ast_emitted_source_from` needs re-justifying, not deleting"
    );
}

#[test]
fn both_layers_omit_the_const_when_safe_glue_needs_no_extent() {
    const SRC: &str = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
                       pub unsafe fn fab_total(buf: *mut i32) -> i32 {\n\
                       \x20   let mut s: i32 = 0;\n\
                       \x20   let mut i: usize = 0;\n\
                       \x20   while i < 4 { s += *buf.offset(i as isize); i += 1; }\n\
                       \x20   s\n\
                       }\n\
                       pub unsafe fn fab_one(d: *mut i32) -> i32 { fab_total(d) }\n";
    let decl = "const FALLBACK_SLICE_EXTENT: usize = 1024;";

    let ast = ast_emitted_source_of(SRC).expect("the AST layer emits");
    assert_eq!(ast.matches(decl).count(), 0, "{ast}");
    assert!(ast.contains("core::slice::from_ref(d)"), "{ast}");

    // The span layer, on the SAME input, through the production entry point.
    let span = match super::rewrite_m1(SRC) {
        super::RewriteOutcome::Emitted { source, .. } => source,
        other => panic!("the span layer must emit: {other:?}"),
    };
    assert_eq!(span.matches(decl).count(), 0, "{span}");
    assert!(span.contains("core::slice::from_ref(d)"), "{span}");
}

/// **CROSS-ARM PARITY — one function carrying BOTH a declaration edit and a
/// fabricated seam.** The REARM obligation, discharged at fixture level.
///
/// The fabrication sweep made `multi_arm` nonzero for the first time:
/// `rgba_from_hex_string` holds two subjects decided `ref` **and** both of
/// rgba's fabricated seams, with zero reverts in that program — one function,
/// two arms. The parked cross-arm parity obligation therefore REARMED.
///
/// **The p3 gate cannot see this.** It runs against a frozen oracle whose revert
/// set predates fabrication and reverted exactly the functions fabrication
/// unblocks, so its `multi_arm` is 0 by construction, not by measurement. A pin
/// that cannot move is not a discharge.
///
/// Measured on rgba itself: the two layers are **byte-identical after canonical
/// formatting** (86,458 bytes each, one const each). This fixture is the
/// corpus-independent half of the same claim, so the obligation stays discharged
/// when the corpus moves.
#[test]
fn a_function_carrying_declaration_and_safe_glue_renders_identically_in_both_layers() {
    const SRC: &str = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
                       pub unsafe fn cx_sum(buf: *mut i32) -> i32 {\n\
                       \x20   let mut s: i32 = 0;\n\
                       \x20   let mut i: usize = 0;\n\
                       \x20   while i < 4 { s += *buf.offset(i as isize); i += 1; }\n\
                       \x20   s\n\
                       }\n\
                       pub unsafe fn cx_caller(p: *mut i32, out: *mut i32) -> i32 {\n\
                       \x20   let t = cx_sum(p);\n\
                       \x20   *out = t;\n\
                       \x20   t\n\
                       }\n";
    let span = match super::rewrite_m1(SRC) {
        super::RewriteOutcome::Emitted { source, .. } => source,
        other => panic!("the span layer must emit: {other:?}"),
    };
    // ---- NON-VACUITY: the fixture must actually carry BOTH arms ----
    //
    // Without this the test would pass on a fixture where fabrication never
    // fired, or where the caller kept every raw parameter — which is exactly
    // the shape it exists to cover.
    assert!(span.contains("core::slice::from_ref(p)"), "{span}");
    assert!(
        span.contains("out: &mut i32"),
        "arm 2 (a declaration edit) must be present IN THE CALLER, or this is \
         not a cross-arm function:\n{span}"
    );

    let ast = ast_emitted_source_of(SRC).expect("the AST layer emits");
    assert_eq!(
        crate::bo_rewriter::goldens::canonicalize("span", &span),
        crate::bo_rewriter::goldens::canonicalize("ast", &ast),
        "the two layers must agree on a function that carries both arms"
    );
}

/// **DIAGNOSIS (M-2/A, 2026-08-18) — does a revert restore BYTES or a reprint?**
///
/// The bar the acceptance gate sets is verdicts and counters, not text. But
/// byte preservation for untransformed code is the migration's founding
/// principle, so a reverted function coming back as a `pprust` reprint is a
/// defect against that principle regardless of whether it moves a verdict.
///
/// Reverting EVERY function is the sharpest form of the question: the emitted
/// text should then be the substrate, byte for byte.
#[test]
fn reverting_every_function_reproduces_the_substrate() {
    // ⚠ **DELIBERATELY NON-CANONICAL.** The first draft of this fixture was
    // written in `pprust`'s own style, so it would have passed whether reverts
    // restore bytes or reprint them — a witness passing for the wrong reason.
    // The odd spacing, the multi-line body and the interior comment are the
    // discriminator: a reprint normalizes all three.
    const SRC: &str = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
                       pub unsafe fn one(p:   *mut i32) -> i32 {\n\
                       \x20   // a comment a reprint would drop\n\
                       \x20   *p\n\
                       }\n\
                       pub unsafe fn two(q: *mut i32)   ->   i32 { *q }\n";

    let all = "one::p#1\ntwo::q#1";
    let out = super::ast_emitted_source_of_reverting(SRC, all).expect("emits");

    // **FIXED (2026-08-18).** This was a status-quo pin of a confirmed defect:
    // `collect_fn_prints` reprinted every function unconditionally, so a fully
    // reverted function came back as a `pprust` reprint with its spacing
    // normalized and its interior comment dropped. The splicer now reprints
    // only functions the transform actually CLAIMED, so an untouched function
    // keeps its original bytes.
    //
    // ⚠ The fixture is DELIBERATELY non-canonical — see above. Written in
    // `pprust` style it would pass either way, which is how the defect stayed
    // invisible to 21 goldens.
    assert_eq!(
        out, SRC,
        "reverting every function must reproduce the substrate byte for byte.\n\
         --- emitted ---\n{out}\n--- substrate ---\n{SRC}"
    );
}

/// RB-W4 — an exact foreign boundary with unknown retention is admitted only
/// by the user-confirmed T2 waiver. The source needs no syntax edit because
/// Rust already coerces `&mut T` to `*mut T`; the decision and tier receipt are
/// the missing mechanism.
#[test]
fn rb_w4_confirmed_t2_unknown_foreign_boundary_emits_zero_syntax() {
    let src = "#![allow(dead_code, unused_unsafe)]\n\
               extern \"C\" { fn opaque(p: *mut i32); }\n\
               pub unsafe fn f(p: *mut i32) { opaque(p); }\n";
    assert_eq!(
        reason_of(&decisions_of(src), "p", true),
        "<emitted>",
        "confirmed T2 must lift the exact foreign-argument escape"
    );
    let super::RewriteOutcome::Emitted { source, .. } = super::rewrite_m1(src) else {
        panic!("T2 fixture must emit");
    };
    assert!(source.contains("p: &mut i32"), "{source}");
    assert!(
        source.contains("opaque(p)"),
        "zero-syntax coercion must stay exact: {source}"
    );
}

/// RB-W5 — the explicit optional bridge borrows the Option at each call. Two
/// calls make move-on-first-use visible; the emitted source must contain no
/// unchecked unwrap.
#[test]
fn rb_w5_optional_foreign_boundary_bridge_is_repeatable_and_compiles() {
    let src = "#![allow(dead_code, unused_unsafe)]\n\
               extern \"C\" { fn opaque(p: *mut i32); }\n\
               pub unsafe fn f(mut p: *mut i32) {\n\
                   if !p.is_null() { opaque(p); opaque(p); }\n\
               }\n";
    let decisions = decisions_of(src);
    assert_eq!(
        reason_of(&decisions, "p", true),
        "<emitted>",
        "decision did not reach the optional bridge: {decisions:#?}"
    );
    let super::RewriteOutcome::Emitted {
        source,
        degradations,
        ..
    } = super::rewrite_m1(src)
    else {
        panic!("optional T2 fixture must emit");
    };
    assert!(
        source.contains("p: Option<&mut i32>"),
        "degradations={degradations:#?}\n{source}"
    );
    assert_eq!(
        source.matches("p.as_deref_mut().map_or").count(),
        2,
        "{source}"
    );
    assert!(!source.contains("unwrap"), "{source}");
}

/// RB-W9 — value observation is rewritten to raw views derived from the safe
/// subjects; the observed addresses are sinks and never become provenance.
#[test]
fn rb_w9_value_observing_comparison_uses_safe_address_views() {
    let src = "#![allow(dead_code, unused_unsafe)]\n\
               extern \"C\" { fn observe(p: *const i32); }\n\
               pub unsafe fn f(p: *const i32, q: *const i32) -> bool {\n\
                   observe(p); observe(q); p == q\n\
               }\n";
    let super::RewriteOutcome::Emitted { source, .. } = super::rewrite_m1(src) else {
        panic!("address-observation fixture must emit");
    };
    assert!(source.contains("p: &i32"), "{source}");
    assert!(source.contains("q: &i32"), "{source}");
    assert_eq!(source.matches("core::ptr::from_ref").count(), 2, "{source}");
    assert!(
        !source.contains(" as *const _ as usize as *const"),
        "{source}"
    );
}

/// ADDR-W1 — a terminal pointer-to-integer observation is a sink. It receives
/// an explicit address view without requiring an unrelated foreign boundary.
#[test]
fn addr_w1_pointer_to_integer_is_a_terminal_safe_view() {
    let src = "#![allow(dead_code, unused_unsafe)]\n\
               pub unsafe fn f(p: *const i32) -> usize { p as usize }\n";
    let super::RewriteOutcome::Emitted { source, .. } = super::rewrite_m1(src) else {
        panic!("terminal address observation must emit");
    };
    assert!(source.contains("p: &i32"), "{source}");
    assert!(
        source.contains("core::ptr::from_ref(p) as usize"),
        "{source}"
    );
}

/// ADDR-W1 — same-allocation difference is observation-only and converts both
/// operands to explicit address views.
#[test]
fn addr_w1_offset_from_is_a_terminal_safe_view() {
    let src = "#![allow(dead_code, unused_unsafe)]\n\
               pub unsafe fn f(p: *const i32, q: *const i32) -> isize { p.offset_from(q) }\n";
    let super::RewriteOutcome::Emitted { source, .. } = super::rewrite_m1(src) else {
        panic!("terminal pointer difference must emit");
    };
    assert!(source.contains("p: &i32"), "{source}");
    assert!(source.contains("q: &i32"), "{source}");
    assert_eq!(source.matches("core::ptr::from_ref").count(), 2, "{source}");
}

/// ADDR-N1 — a pointer-producing arithmetic use remains access-producing and
/// cannot be licensed by an address observation elsewhere in the function.
#[test]
fn addr_n1_access_producing_use_keeps_the_subject_raw() {
    let src = "#![allow(dead_code, unused_unsafe)]\n\
               pub unsafe fn f(p: *const i32) -> (usize, i32) { (p as usize, *p.offset(1)) }\n";
    let super::RewriteOutcome::Emitted { source, .. } = super::rewrite_m1(src) else {
        panic!("mixed address/access fixture must remain emittable");
    };
    assert!(source.contains("p: *const i32"), "{source}");
    assert!(!source.contains("core::ptr::from_ref(p)"), "{source}");
}

/// Addendum-142 edit-region witness: a depth-two pointer's element access is
/// already rewritten by the subject-use arm.  The foreign call consumes that
/// RAW element, not the surrounding safe slice, so the existing use edit owns
/// the exact argument region and the raw-boundary arm must not plan a second
/// edit over it.
///
/// Mutation: deleting the exact-region ownership check recreates two edits at
/// one span.  The structural plan gate then degrades with an overlap instead of
/// emitting this fixture, so the outcome assertion kills the mutation before a
/// corpus launch.
#[test]
fn raw_boundary_exact_slice_use_region_has_one_owner() {
    let src = "#![allow(dead_code, unused_unsafe, unused_variables)]\n\
               extern \"C\" { fn strlen(s: *const i8) -> usize; }\n\
               pub unsafe fn f(argc: i32, argv: *mut *mut i8) -> usize {\n\
                   let _ = argc; strlen(*argv.offset(0))\n\
               }\n";
    let super::RewriteOutcome::Emitted { source, .. } = super::rewrite_m1(src) else {
        panic!("an exact subject-use/raw-boundary region must have one owner");
    };
    assert!(
        source.contains("argv: &[*mut i8]"),
        "the fixture must actually produce the depth-two slice subject: {source}"
    );
    assert!(
        source.contains("strlen(argv["),
        "the subject-use carrier must survive at the call: {source}"
    );
    assert!(
        !source.contains(".as_ptr()"),
        "the raw element must not be mistaken for the surrounding slice: {source}"
    );
    let artifacts = ::utils::compilation::run_compiler_on_str(src, |tcx| {
        super::raw_boundary_trace_artifacts(tcx).expect("raw-boundary trace")
    })
    .expect("trace fixture compiles");
    assert!(
        artifacts
            .atom_outcomes
            .contains("edit-region-owned\traw-boundary-edit-region-owned\t"),
        "the sole-owner disposition must be receipted: {}",
        artifacts.atom_outcomes
    );
}

/// Addendum-169 R-B production witness for the two RB-X3 family shapes. The
/// variadic subject crosses a libc position whose contract marks the argument
/// read-only, so it may use the explicit address view. The FILE stream contract
/// is not read-only and therefore must remain raw even when the Rust body only
/// reads through the pointer.
///
/// A mutation that treats the stream shape itself as negative-write evidence
/// incorrectly promotes `stream` and emits a second `cast_mut` bridge.
#[test]
fn rb_x3_family_contracts_reach_the_shared_emission_path() {
    let src = "#![allow(dead_code, unused_unsafe, unused_variables)]\n\
               #[repr(C)] pub struct File { x: i32 }\n\
               static FMT: [i8; 3] = [37, 115, 0];\n\
               extern \"C\" {\n\
                   fn printf(fmt: *const i8, ...) -> i32;\n\
                   fn fprintf(stream: *mut File, fmt: *const i8, ...) -> i32;\n\
               }\n\
               pub unsafe fn print_arg(p: *mut i8) -> i32 {\n\
                   let _ = *p; printf(FMT.as_ptr(), p)\n\
               }\n\
               pub unsafe fn print_stream(stream: *mut File) -> i32 {\n\
                   let _ = (*stream).x; fprintf(stream, FMT.as_ptr())\n\
               }\n";
    let super::RewriteOutcome::Emitted { source, .. } = super::rewrite_m1(src) else {
        panic!("both exact family contracts must emit");
    };
    assert!(source.contains("print_arg(p: &i8)"), "{source}");
    assert!(
        source.contains("print_stream(stream: *mut File)"),
        "{source}"
    );
    assert_eq!(
        source.matches("core::ptr::from_ref(").count(),
        1,
        "only the libc-read-only subject may use an explicit bridge: {source}"
    );
    assert_eq!(
        source.matches(".cast_mut()").count(),
        1,
        "a stream contract must not license a shared-to-mut raw bridge: {source}"
    );
}

fn configured_exposure_input(name: &str) -> super::decision::exposure::ConfiguredExposureInput {
    let digest = match name {
        "api" => "14c2529eb4498c5d1ffd6915d05bf58a91bdda796af59f41d480d11c099d0479",
        other => panic!("fixture has no pinned digest for {other}"),
    };
    super::decision::exposure::ConfiguredExposureInput::checked(
        "fixture-config",
        [name.to_owned()],
        digest,
    )
    .expect("configured exposure fixture input")
}

/// C-W5a/C-W5c — a positive seed gets one raw outer plus a safe inner, while
/// an unseeded function in the same crate converts directly under R4.
#[test]
fn c_w5_surface_emission_separates_seed_shim_from_closed_world_direct() {
    let fixture = Fixture::new(&[(
        "lib.rs",
        "#![allow(dead_code, unused_unsafe)]\n\
         #[no_mangle]\n\
         pub unsafe extern \"C\" fn api(p: *const i32) -> *const i32 { p }\n\
         pub unsafe extern \"C\" fn helper(p: *const i32) -> *const i32 { p }\n",
    )]);
    let run_config = super::EmissionRunConfig {
        configured_exposure: configured_exposure_input("api"),
    };
    let outcome = super::rewrite_m1_path_with_emission_config(
        &fixture.root(),
        crate::analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay,
        Some(
            crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph,
        ),
        &run_config,
    );
    let super::RewriteOutcome::Emitted { files, .. } = outcome else {
        panic!("C-W5 surface fixture must emit: {outcome:#?}")
    };
    let source = files
        .values()
        .find(|source| source.contains("fn api"))
        .expect("emitted root");
    assert!(
        source.contains("fn api(p: *const i32) -> *const i32"),
        "{source}"
    );
    assert!(source.contains("fn __crat_safe_api<'"), "{source}");
    assert!(
        source.contains("core::ptr::from_ref(__crat_result)"),
        "{source}"
    );
    assert!(!source.contains("__crat_safe_helper"), "{source}");
    assert!(source.contains("fn helper<'"), "{source}");
}

/// C-W5d — an explicit empty configured input does not mean internal, but the
/// closed-world rule still performs the direct conversion and emits no shim.
#[test]
fn c_w5_empty_seed_direct_conversion_has_no_surface_wrapper() {
    let fixture = Fixture::new(&[(
        "lib.rs",
        "#![allow(dead_code, unused_unsafe)]\n\
         pub unsafe extern \"C\" fn api(p: *const i32) -> *const i32 { p }\n",
    )]);
    let run_config = super::EmissionRunConfig::default();
    let outcome = super::rewrite_m1_path_with_emission_config(
        &fixture.root(),
        crate::analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay,
        Some(
            crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph,
        ),
        &run_config,
    );
    let super::RewriteOutcome::Emitted { files, .. } = outcome else {
        panic!("C-W5d surface fixture must emit: {outcome:#?}")
    };
    let source = files.values().next().expect("emitted root");
    assert!(!source.contains("__crat_safe_api"), "{source}");
    assert!(source.contains("fn api<'"), "{source}");
}

/// C-N2 — seed membership is audit evidence, not permission to manufacture a
/// wrapper when every signature subject is blocked by a later arm.
#[test]
fn c_n2_seed_without_settled_signature_subject_has_no_pointless_wrapper() {
    let fixture = Fixture::new(&[(
        "lib.rs",
        "#![allow(dead_code, unused_unsafe)]\n\
         pub unsafe extern \"C\" fn api(p: *const i32) -> *const i32 { p.offset(1) }\n",
    )]);
    let run_config = super::EmissionRunConfig {
        configured_exposure: configured_exposure_input("api"),
    };
    let outcome = super::rewrite_m1_path_with_emission_config(
        &fixture.root(),
        crate::analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay,
        Some(
            crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph,
        ),
        &run_config,
    );
    let super::RewriteOutcome::Emitted { files, .. } = outcome else {
        panic!("C-N2 blocked seed fixture must remain emittable: {outcome:#?}")
    };
    let source = files.values().next().expect("emitted root");
    assert!(!source.contains("__crat_safe_api"), "{source}");
    assert!(source.contains("fn api(p: *const i32)"), "{source}");
}

/// C-W4 — an address-taken root gets the positive-seed shim and its forward
/// web member gets a raw-signature wrapper. Calls inside the safe root target
/// the member's safe inner; the web/table binding remains raw.
#[test]
fn c_w4_fnptr_web_uses_raw_surfaces_and_safe_inner_calls() {
    let fixture = Fixture::new(&[(
        "lib.rs",
        "#![allow(dead_code, unused_unsafe)]\n\
         pub unsafe fn leaf(p: *const i32) -> *const i32 { p }\n\
         pub unsafe fn root(p: *const i32) -> *const i32 { leaf(p) }\n\
         pub unsafe fn install() {\n\
             let _callback: unsafe fn(*const i32) -> *const i32 = root;\n\
         }\n",
    )]);
    let outcome = super::rewrite_m1_path_with_emission_config(
        &fixture.root(),
        crate::analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay,
        Some(
            crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph,
        ),
        &super::EmissionRunConfig::default(),
    );
    let super::RewriteOutcome::Emitted { files, .. } = outcome else {
        panic!("C-W4 web fixture must emit: {outcome:#?}")
    };
    let source = files.values().next().expect("emitted root");
    assert!(source.contains("fn root(p: *const i32)"), "{source}");
    assert!(source.contains("fn __crat_safe_root(p: &i32)"), "{source}");
    assert!(source.contains("fn leaf(p: *const i32)"), "{source}");
    assert!(source.contains("fn __crat_safe_leaf<'"), "{source}");
    assert!(source.contains("__crat_safe_leaf(p)"), "{source}");
    assert!(
        source.contains("let _callback: unsafe fn(*const i32) -> *const i32 = root"),
        "{source}"
    );
}

/// D3-W1 — lil's missing-generated-item shape. A surfaced caller names the
/// callee's generated safe inner, so holding the defining callee class must
/// hold the caller class before either surface is emitted.
#[test]
fn d3_w1_generated_inner_use_depends_on_ready_defining_class() {
    let source = "#![allow(dead_code, unused_unsafe)]\n\
         pub unsafe fn leaf(p: *const i32) -> *const i32 { p }\n\
         pub unsafe fn root(p: *const i32) -> *const i32 { leaf(p) }\n\
         pub unsafe fn install() {\n\
             let _callback: unsafe fn(*const i32) -> *const i32 = root;\n\
         }\n";
    let fixture = Fixture::new(&[("lib.rs", source)]);
    let (emitted, leaf_held, root_held) =
        ::utils::compilation::run_compiler_on_path(&fixture.root(), |tcx| {
            let capture = super::ast_transform::capture_ast(tcx)?;
            let (mut table, ctx) = super::decide_table_with_ctx_config(
                tcx,
                Some((
                    crate::analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay,
                    Some(
                        crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph,
                    ),
                )),
            )?;
            let leaf = table
                .entries
                .iter()
                .find(|(subject, _)| subject.label.ends_with("leaf::p"))
                .map(|(subject, _)| (subject.fn_did, subject.hir_id))
                .expect("leaf parameter subject");
            let root = table
                .entries
                .iter()
                .find(|(subject, _)| subject.label.ends_with("root::p"))
                .map(|(subject, _)| subject.fn_did)
                .expect("root parameter subject");
            assert!(table.seams.generated_item_dependencies.contains(&(
                super::bridge_receipt::SignatureClassId::of(root),
                super::bridge_receipt::SignatureClassId::of(leaf.0),
            )));
            table
                .arm_requirements
                .entry(leaf)
                .or_default()
                .insert(super::decision::Arm::C);
            let emission = emit_files(
                tcx,
                &table,
                &rustc_hash::FxHashSet::default(),
                &ctx.retained_c9_plans,
            )?;
            let held = emission.plan.held_classes();
            let leaf_held = held.contains(&super::bridge_receipt::SignatureClassId::of(leaf.0));
            let root_held = held.contains(&super::bridge_receipt::SignatureClassId::of(root));
            let reverts = super::ast_transform::revert_set_from_classes_and_atoms(
                &held,
                &std::collections::BTreeSet::new(),
                &table,
            )?;
            let (files, _, _) = super::ast_transform::ast_emitted_files_from(
                tcx, &capture, &reverts, None, &table,
            )?;
            let emitted = files
                .values()
                .find(|text| text.contains("fn leaf"))
                .cloned()
                .ok_or_else(|| "D3-W1 emitted root missing".to_owned())?;
            Ok::<_, String>((emitted, leaf_held, root_held))
        })
        .expect("D3-W1 input compiles")
        .expect("D3-W1 emission");

    assert!(leaf_held, "the defining class was not held:\n{emitted}");
    assert!(
        root_held,
        "the generated-item use stayed Ready after its definition was held:\n{emitted}"
    );
    assert!(!emitted.contains("__crat_safe_leaf"), "{emitted}");
    assert!(!emitted.contains("__crat_safe_root"), "{emitted}");
    let emitted_fixture = Fixture::new(&[("lib.rs", &emitted)]);
    assert!(
        ::utils::compilation::run_compiler_on_path(&emitted_fixture.root(), |_| ()).is_ok(),
        "D3-W1 emitted tree must not name a missing generated item:\n{emitted}"
    );
}

/// D8-W1 — an ordinary local caller of a surfaced function must target the
/// generated safe inner when its C adapter was planned against that inner's
/// interface.  The tulip L86 failure instead rendered `target(&[T])`, where
/// `target` was the terminal raw wrapper and therefore still expected `*const
/// T`.
#[test]
fn d8_w1_ordinary_caller_uses_terminal_safe_inner_interface() {
    let fixture = Fixture::new(&[(
        "lib.rs",
        "#![allow(dead_code, unused_unsafe)]\n\
         pub unsafe fn target(p: *const i32) -> i32 { *p }\n\
         pub unsafe fn caller(p: *const i32) -> i32 { target(p) }\n\
         pub unsafe fn install() {\n\
             let _callback: unsafe fn(*const i32) -> i32 = target;\n\
         }\n",
    )]);
    let outcome = super::rewrite_m1_path_with_emission_config(
        &fixture.root(),
        crate::analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay,
        Some(
            crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph,
        ),
        &super::EmissionRunConfig::default(),
    );
    let super::RewriteOutcome::Emitted { files, .. } = outcome else {
        panic!("D8-W1 fixture must emit: {outcome:#?}")
    };
    let emitted = files.values().next().expect("emitted root");
    assert!(emitted.contains("fn target(p: *const i32)"), "{emitted}");
    assert!(emitted.contains("fn __crat_safe_target"), "{emitted}");
    assert!(emitted.contains("__crat_safe_target(p)"), "{emitted}");
    let emitted_fixture = Fixture::new(&[("lib.rs", emitted)]);
    assert!(
        ::utils::compilation::run_compiler_on_path(&emitted_fixture.root(), |_| ()).is_ok(),
        "D8-W1 terminal wrapper/inner pairing must type-check:\n{emitted}"
    );
}
