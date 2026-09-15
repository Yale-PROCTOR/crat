//! Reduced from heman kmVec2Reflect → kmVec2Subtract: the callee returns its
//! `pOut` parameter (a Return-only retention) and the caller DISCARDS the
//! result, so nothing retains the alias beyond the call.
const INPUT: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut)]
pub struct V { x: f32, y: f32 }
#[unsafe(no_mangle)]
pub unsafe extern "C" fn sub(pOut: *mut V, a: *const V, b: *const V) -> *mut V {
    (*pOut).x = (*a).x - (*b).x;
    (*pOut).y = (*a).y - (*b).y;
    pOut
}
pub unsafe fn reflect(pOut: *mut V, pIn: *const V, normal: *const V) {
    let mut tmp = V { x: 0., y: 0. };
    tmp.x = (*normal).x;
    sub(pOut, pIn, &mut tmp);
}
"#;

fn sub_arg0_disposition(input: &str) -> String {
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let (table, ctx) = super::super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::super::A5Mode::PreciseReplay,
                Some(super::super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .expect("native decisions");
        for (subject, decision) in &table.entries {
            println!("DECISION {} {decision:?}", subject.label);
        }
        let rows = ctx.raw_boundary.receipts_tsv();
        println!("DISPOSITIONS\n{rows}");
        rows.lines()
            .find(|line| line.starts_with("reflect\t") && line.contains("\tsub\t0\t"))
            .expect("the sub arg0 site is inventoried")
            .to_owned()
    })
    .expect("input type-checks")
}

#[test]
fn wave6r_returned_alias_discarded_by_caller_is_no_retain() {
    let row = sub_arg0_disposition(INPUT);
    assert!(row.contains("\tT1\t"), "{row}");
    assert!(!row.contains("positive-retention"), "{row}");
}

/// The caller keeps the returned alias (writes through it): the retention stands.
#[test]
fn wave6r_returned_alias_kept_by_caller_keeps_hold() {
    let row = sub_arg0_disposition(&INPUT.replace(
        "    sub(pOut, pIn, &mut tmp);\n",
        "    let r = sub(pOut, pIn, &mut tmp);\n    (*r).x = 1.0;\n",
    ));
    assert!(
        row.contains("\tblocked\t") && row.contains("positive-retention"),
        "{row}"
    );
}

/// The callee retains through a store as well as the return: the retention stands.
#[test]
fn wave6r_returned_alias_with_store_keeps_hold() {
    let row = sub_arg0_disposition(
        &INPUT
            .replace(
                "    (*pOut).y = (*a).y - (*b).y;\n    pOut\n",
                "    (*pOut).y = (*a).y - (*b).y;\n    KEEP = pOut;\n    pOut\n",
            )
            .replace(
                "pub struct V",
                "pub static mut KEEP: *mut V = core::ptr::null_mut();\npub struct V",
            ),
    );
    assert!(
        row.contains("\tblocked\t") && row.contains("positive-retention"),
        "{row}"
    );
}

/// The emitted caller: the site is a plain mutable bridge (zero syntax) and
/// the discarded result still compiles.
#[test]
fn wave6r_returned_alias_discarded_caller_emits() {
    let source = super::emitted(INPUT);
    assert!(source.contains("reflect(pOut: &mut V"), "{source}");
    assert!(source.contains("sub(pOut, "), "{source}");
}
