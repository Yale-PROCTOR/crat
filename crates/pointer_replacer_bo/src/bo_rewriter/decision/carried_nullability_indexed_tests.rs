//! Wave-6o relay 139 (R785-10, batch 54's main 159 §2b): a nullability carried
//! from elsewhere (a raw field the program writes null into, R619-2 finding 12;
//! a caller's nullable actual, R744-1) made an INDEXED slot optional, and no
//! optional-slice arm renders its `.offset` or its index: lodepng
//! `lodepng_convert::palette#51` (E0608), brotli
//! `ZopfliCostModelSetFromLiteralCosts::literal_costs#5` / `cost_dist#7` (E0599).
//! A slot used as an array keeps the form its own evidence gives it.

fn fixture(body: &str) -> String {
    format!(
        "#![allow(dead_code,unused_unsafe,unused_mut,unused_assignments,unused_variables,non_snake_case,non_camel_case_types)]\n{body}"
    )
}

/// lodepng's shape, reduced from the corpus row: `mode_clear` writes null into
/// the field; `convert` reads it into a local and indexes it.
const PALETTE: &str = r###"
pub struct LodePNGColorMode {
    pub palette: *mut u8,
    pub palettesize: usize,
}
pub unsafe fn lodepng_color_mode_clear(mut info: *mut LodePNGColorMode) {
    (*info).palette = 0 as *mut u8;
    (*info).palettesize = 0;
}
pub unsafe fn lodepng_convert(mut out: *mut u8, mut mode_in: *const LodePNGColorMode, mut n: usize) -> u32 {
    let mut palette = (*mode_in).palette;
    let mut i: usize = 0;
    while i < n {
        *out.offset(i as isize) = *palette.offset((4 * i) as isize);
        i = i.wrapping_add(1);
    }
    0
}
"###;

/// brotli's shape: `ZopfliCostModelSetFromLiteralCosts` reads `literal_costs_`
/// into a local and walks it by `.offset`; the cleanup writes null into it.
const COSTS: &str = r###"
pub struct ZopfliCostModel {
    pub literal_costs_: *mut f32,
    pub num_bytes_: usize,
}
pub unsafe fn CleanupZopfliCostModel(mut self_0: *mut ZopfliCostModel) {
    (*self_0).literal_costs_ = 0 as *mut f32;
}
pub unsafe fn ZopfliCostModelSetFromLiteralCosts(mut self_0: *mut ZopfliCostModel) {
    let mut literal_costs = (*self_0).literal_costs_;
    let mut literal_carry = 0.0f32;
    let mut i: usize = 0;
    *literal_costs.offset(0 as isize) = 0.0f32;
    while i < (*self_0).num_bytes_ {
        literal_carry += *literal_costs.offset(i.wrapping_add(1) as isize);
        *literal_costs.offset(i.wrapping_add(1) as isize) = *literal_costs.offset(i as isize) + literal_carry;
        i = i.wrapping_add(1);
    }
}
"###;

fn check(src: &str, local: &str) {
    let source = crate::bo_rewriter::emit_tests::ast_emitted_source_of(&fixture(src))
        .unwrap_or_else(|e| panic!("emission failed: {e}"));
    assert!(
        crate::bo_rewriter::verify::type_checks_str(&source),
        "the emitted program must type-check (the {local} slot indexed through an optional): {source}"
    );
    let compact: String = source.split_whitespace().collect();
    assert!(
        !compact.contains(&format!("mut{local}:Option<"))
            && !compact.contains(&format!("let{local}:Option<")),
        "an indexed slot is not made optional by carried nullability: {source}"
    );
}

/// W1 — lodepng `palette`: the field's null does not make the indexed local optional.
#[test]
fn w6o_r785_w1_a_field_null_does_not_make_an_indexed_local_optional() {
    check(PALETTE, "palette");
}

/// W2 — brotli `literal_costs`: the same at an `.offset` walk with stores.
#[test]
fn w6o_r785_w2_a_field_null_does_not_make_an_offset_walked_local_optional() {
    check(COSTS, "literal_costs");
}
