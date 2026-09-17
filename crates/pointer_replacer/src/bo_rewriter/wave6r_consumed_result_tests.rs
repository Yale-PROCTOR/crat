//! Reduced from heman `kmVec2Length(kmVec2Subtract(&mut tmp, &mut intersect,
//! &mut p1))` (relay wave-6r/019, wave-5d2 014): the callee returns its own
//! out-parameter (`retains / positive-retention`, `Return: return _1`) and the
//! caller consumes that alias in the statement that produced it. Nothing keeps
//! it, so the site takes a no-retain certificate instead of the hold.
const VEC2: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, static_mut_refs)]
#[derive(Copy, Clone)]
pub struct Vec2 { x: f32, y: f32 }
pub static mut KEEP: *mut Vec2 = core::ptr::null_mut();
unsafe fn vec2_subtract(pOut: *mut Vec2, pV1: *const Vec2, pV2: *const Vec2) -> *mut Vec2 {
    (*pOut).x = (*pV1).x - (*pV2).x;
    (*pOut).y = (*pV1).y - (*pV2).y;
    pOut
}
unsafe fn vec2_length(pIn: *const Vec2) -> f32 {
    ((*pIn).x * (*pIn).x + (*pIn).y * (*pIn).y).sqrt()
}
pub unsafe fn consumed(out: *mut Vec2, a: *const Vec2, b: *const Vec2) -> f32 {
    vec2_length(vec2_subtract(out, a, b))
}
pub unsafe fn kept(out: *mut Vec2, a: *const Vec2, b: *const Vec2) -> f32 {
    let p = vec2_subtract(out, a, b);
    KEEP = p;
    vec2_length(p)
}
pub unsafe fn stashed(out: *mut Vec2, a: *const Vec2, b: *const Vec2, slot: *mut *mut Vec2) -> f32 {
    let p = vec2_subtract(out, a, b);
    *slot = p;
    vec2_length(p)
}
"#;

fn site_rows(caller: &str, callee: &str) -> Vec<String> {
    ::utils::compilation::run_compiler_on_str(VEC2, |tcx| {
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
        println!("RETENTION\n{}", ctx.retention.to_tsv());
        rows.lines()
            .filter(|line| {
                line.starts_with(&format!("{caller}\t"))
                    && line.contains(&format!("\t{callee}\t0\t"))
            })
            .map(str::to_owned)
            .collect::<Vec<_>>()
    })
    .expect("input type-checks")
}

#[test]
fn wave6r_consumed_returned_alias_delivers() {
    let rows = site_rows("consumed", "vec2_subtract");
    assert!(!rows.is_empty(), "the subtract site is inventoried");
    // The certificate is the site's retention verdict, not a receipt column:
    // without it the row reads `blocked / raw-boundary-positive-retention`.
    assert!(
        rows.iter().any(|row| row.contains("\tT1\t")),
        "the consumed alias delivers: {rows:?}"
    );
}

#[test]
fn wave6r_kept_returned_alias_keeps_the_hold() {
    let rows = site_rows("kept", "vec2_subtract");
    assert!(!rows.is_empty(), "the subtract site is inventoried");
    assert!(
        !rows.iter().any(|row| row.contains("\tT1\t")),
        "a stored returned alias keeps the hold: {rows:?}"
    );
}

#[test]
fn wave6r_stashed_returned_alias_keeps_the_hold() {
    let rows = site_rows("stashed", "vec2_subtract");
    assert!(!rows.is_empty(), "the subtract site is inventoried");
    assert!(
        !rows.iter().any(|row| row.contains("\tT1\t")),
        "a returned alias stored through a pointer keeps the hold: {rows:?}"
    );
}
