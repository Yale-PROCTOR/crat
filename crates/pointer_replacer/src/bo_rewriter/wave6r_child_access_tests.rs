//! Reduced from brotli PrepareDistanceCacheH65 at checkpoint 2: the shared
//! root's field address reaches a raw formal whose pointee carries pointer
//! fields, so the callee "may yield a pointer" by output storage and the
//! write-through-shared-view hold fires although the callee never lets a
//! descendant of the argument escape.
const INPUT: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut)]
pub struct H6 { num: i32, extra: *mut u8 }
pub struct HROLLING { tag: i32, extra: *mut u8 }
pub struct H65 { ha: H6, hb: HROLLING }
#[unsafe(no_mangle)]
pub unsafe extern "C" fn prepare_h6(s: *mut H6, cache: *mut i32) {
    *cache = (*s).num;
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn prepare_hrolling(s: *mut HROLLING, cache: *mut i32) {
    *cache += (*s).tag;
}
pub unsafe fn prepare_h65(s: *mut H65, cache: *mut i32) {
    prepare_h6(&mut (*s).ha, cache);
    prepare_hrolling(&mut (*s).hb, cache);
}
"#;

#[test]
fn wave6r_h65_descendant_free_callee_discharges_write_through_shared_view() {
    let source = super::emitted(INPUT);
    assert!(source.contains("s: &H65"), "{source}");
    // The callee's formal is raw on this branch (the bridge); a class split
    // that applies its shared formal makes the plain shared borrow the right
    // text instead. Either way the shared root is never borrowed mutably.
    assert!(
        source.contains("prepare_h6(core::ptr::from_ref(&(*s).ha).cast_mut()")
            || source.contains("prepare_h6(&(*s).ha"),
        "{source}"
    );
    assert!(
        source.contains("prepare_hrolling(core::ptr::from_ref(&(*s).hb).cast_mut()")
            || source.contains("prepare_hrolling(&(*s).hb"),
        "{source}"
    );
    assert!(!source.contains("&mut (*s)"), "{source}");
}

/// The raw-boundary disposition rows of `prepare_h65`'s first argument to
/// `prepare_h6`, as the census exports them.
fn h6_arg0_disposition(input: &str) -> String {
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let (_, ctx) = super::super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::super::A5Mode::PreciseReplay,
                Some(super::super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .expect("native decisions");
        let rows = ctx.raw_boundary.receipts_tsv();
        println!("DISPOSITIONS\n{rows}");
        rows.lines()
            .find(|line| line.starts_with("prepare_h65\t") && line.contains("\tprepare_h6\t0\t"))
            .expect("the H6 arg0 site is inventoried")
            .to_owned()
    })
    .expect("input type-checks")
}

/// The site must stay blocked. Which arm names the hold depends on arm order
/// — `write-through-shared-view` here, `positive-retention` once a retention
/// check runs first (the batch-8 composition) — and both are the same
/// soundness fact for these shapes: the callee retains or hands back the alias.
fn held(input: &str) {
    let row = h6_arg0_disposition(input);
    assert!(
        row.contains("\tblocked\t")
            && (row.contains("ordinary-argument-permission:write-through-shared-view")
                || row.contains("raw-boundary-positive-retention")),
        "the hold must stand: {row}"
    );
}

#[test]
fn wave6r_child_access_discharge_is_receipted() {
    let row = h6_arg0_disposition(INPUT);
    assert!(row.contains("\tshared-ref-to-mut-raw\t"), "{row}");
    assert!(!row.contains("write-through-shared-view"), "{row}");
}
/// The callee stores the argument itself: the retention row is not NoRetain.
#[test]
fn wave6r_child_access_global_store_keeps_hold() {
    held(
        &INPUT
            .replace(
                "    *cache = (*s).num;\n",
                "    *cache = (*s).num;\n    KEEP = s;\n",
            )
            .replace(
                "pub struct H65",
                "pub static mut KEEP: *mut H6 = core::ptr::null_mut();\npub struct H65",
            ),
    );
}

/// A derivation the retention summary does not track — the raw address of a
/// place under the argument — escapes through a global: the body scan refuses.
#[test]
fn wave6r_child_access_raw_address_derivation_keeps_hold() {
    held(
        &INPUT
            .replace(
                "    *cache = (*s).num;\n",
                "    *cache = (*s).num;\n    let q = &raw mut (*s).extra;\n    KEEP2 = q;\n",
            )
            .replace(
                "pub struct H65",
                "pub static mut KEEP2: *mut *mut u8 = core::ptr::null_mut();\npub struct H65",
            ),
    );
}

/// A local callee that retains the argument transitively: the retention row
/// depends on it and is not NoRetain.
#[test]
fn wave6r_child_access_transitive_retaining_callee_keeps_hold() {
    held(&INPUT.replace(
        "    *cache = (*s).num;\n",
        "    *cache = (*s).num;\n    keep(s);\n",
    ).replace("pub struct H65", "pub static mut KEEP3: *mut H6 = core::ptr::null_mut();\npub unsafe fn keep(p: *mut H6) { KEEP3 = p; }\npub struct H65"));
}

/// Reduced from binn `binn_object_get_value`: the callee null-tests its
/// parameter before reading it. `is_null` is a `Rust`-ABI core method, which
/// the retention collector filed as an unknown call, so the position never
/// earned NoRetain and the shared source stayed held.
#[test]
fn wave6r_child_access_null_test_in_callee_is_no_retain() {
    let row = h6_arg0_disposition(&INPUT.replace(
        "    *cache = (*s).num;\n",
        "    if s.is_null() { return; }\n    *cache = (*s).num;\n",
    ));
    assert!(row.contains("\tshared-ref-to-mut-raw\t"), "{row}");
    assert!(!row.contains("write-through-shared-view"), "{row}");
}

/// Reduced from brotli `StoreH3`: the callee advances its parameter with a
/// core `offset` and reads through the result. `offset` is a `Rust`-ABI
/// method, filed as an unknown call by the retention collector, so the
/// position never earned NoRetain and every shared caller stayed held.
#[test]
fn wave6r_child_access_core_offset_read_in_callee_is_no_retain() {
    let row = h6_arg0_disposition(&INPUT.replace(
        "    *cache = (*s).num;\n",
        "    let next = s.offset(1);\n    *cache = (*next).num;\n",
    ));
    assert!(row.contains("\tshared-ref-to-mut-raw\t"), "{row}");
    assert!(!row.contains("write-through-shared-view"), "{row}");
}

/// The `offset` result is an alias: storing it in a global retains it.
#[test]
fn wave6r_child_access_core_offset_result_stored_keeps_hold() {
    held(
        &INPUT
            .replace(
                "    *cache = (*s).num;\n",
                "    KEEP4 = s.offset(1);\n    *cache = (*s).num;\n",
            )
            .replace(
                "pub struct H65",
                "pub static mut KEEP4: *mut H6 = core::ptr::null_mut();\npub struct H65",
            ),
    );
}

/// The `offset` result reaches a foreign callee with no contract row: only
/// the retention collector sees that sink (the scan defers foreign callees
/// to the certificate). The unknown foreign call also makes the root mutable
/// upstream, so the site is a T2 bridge; what the alias edge decides is its
/// retention reason — an open boundary reached through the `offset` result,
/// never a no-retain certificate.
#[test]
fn wave6r_child_access_core_offset_result_into_unmodeled_foreign_is_retention_unknown() {
    let row = h6_arg0_disposition(
        &INPUT
            .replace(
                "    *cache = (*s).num;\n",
                "    sink(s.offset(1));\n    *cache = (*s).num;\n",
            )
            .replace(
                "pub struct H65",
                "unsafe extern \"C\" { fn sink(p: *mut H6); }\npub struct H65",
            ),
    );
    assert!(
        row.contains("\tT2\t") && row.contains("retention-open-boundary"),
        "{row}"
    );
}
