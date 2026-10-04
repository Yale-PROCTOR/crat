//! R805-7 (relay 272): the census-world test entry. A reduced A5 shape that the
//! open world (`rewrite_m1`) cannot emit — `unowned A5 proof-site receipt
//! identities` — emits in the world every census runs in.

const ALLOW: &str = "#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments, unused_variables, non_snake_case, non_camel_case_types)]\n";

/// brotli `BrotliClusterHistogramsCommand → BrotliHistogramCombineCommand`'s
/// call, reduced (main 164 §4): three pointer arguments of one element type,
/// two of them element addresses.
const CLUSTER: &str = r#"
extern "C" {
    fn malloc(n: usize) -> *mut core::ffi::c_void;
    fn free(p: *mut core::ffi::c_void);
}
pub unsafe fn combine(cluster_size: *mut u32, symbols: *mut u32, clusters: *mut u32, n: usize) -> usize {
    let mut i = 0usize;
    while i < n {
        *symbols.offset(i as isize) = *clusters.offset(i as isize);
        *cluster_size.offset(i as isize) = 1;
        i = i.wrapping_add(1);
    }
    n
}
pub unsafe fn cluster(in_size: usize, histogram_symbols: *mut u32) -> usize {
    let mut cluster_size = malloc(in_size.wrapping_mul(4)) as *mut u32;
    let mut clusters = malloc(in_size.wrapping_mul(4)) as *mut u32;
    let mut i = 0usize;
    while i < in_size {
        *histogram_symbols.offset(i as isize) = i as u32;
        *clusters.offset(i as isize) = i as u32;
        i = i.wrapping_add(1);
    }
    let mut total = 0usize;
    i = 0;
    while i < in_size {
        total = total.wrapping_add(combine(
            cluster_size,
            &mut *histogram_symbols.offset(i as isize),
            &mut *clusters.offset(i as isize),
            64,
        ));
        i = i.wrapping_add(64);
    }
    free(cluster_size as *mut core::ffi::c_void);
    free(clusters as *mut core::ffi::c_void);
    total
}
"#;

#[test]
fn r805_7_an_a5_shape_emits_in_the_census_world() {
    let input = format!("{ALLOW}{CLUSTER}");
    match super::rewrite_m1_census_world(&input) {
        super::RewriteOutcome::Emitted { source, .. } => {
            assert!(source.contains("pub unsafe fn combine("), "{source}");
        }
        other => panic!("the census world emits: {other:#?}"),
    }
}
