//! Reduced from brotli SearchInStaticDictionary → TestStaticDictionaryItem →
//! FindMatchLengthWithLimit (relay 011 §2): the shared `data` reaches a raw
//! `*const u8` formal whose only derivations are core `offset`s read through
//! (`BrotliUnalignedRead64`); the callee's out-param carries a pointer field
//! so it "may yield a pointer" and the write-through arm is exercised.
pub(crate) const STATIC_DICT: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]
use core::ffi::c_void;
pub struct Words { offsets: [u32; 4], data: *const u8 }
pub struct Dict { words: *const Words, cutoff: u32 }
pub struct Out { len: usize, score: usize, extra: *mut u8 }
unsafe fn read64(p: *const c_void) -> u64 { *(p as *const u64) }
unsafe fn match_len(s1: *const u8, mut s2: *const u8, limit: usize) -> usize {
    let mut matched = 0usize;
    while matched + 8 <= limit {
        if read64(s2 as *const c_void) != read64(s1.offset(matched as isize) as *const c_void) {
            return matched;
        }
        s2 = s2.offset(8);
        matched += 8;
    }
    while matched < limit && *s1.offset(matched as isize) == *s2 {
        s2 = s2.offset(1);
        matched += 1;
    }
    matched
}
unsafe fn test_item(dictionary: *const Dict, len: usize, idx: usize, data: *const u8, max_length: usize, out: *mut Out) -> i32 {
    let offset = (*(*dictionary).words).offsets[len] as usize + len * idx;
    let matchlen = match_len(data, &*((*(*dictionary).words).data).offset(offset as isize), max_length);
    if matchlen < len { return 0; }
    (*out).len = matchlen;
    (*out).score = len + (*dictionary).cutoff as usize;
    1
}
pub unsafe fn search(dictionary: *const Dict, data: *const u8, max_length: usize, out: *mut Out) {
    let key = (*data as usize) & 3;
    if (*(*dictionary).words).offsets[key] != 0 {
        test_item(dictionary, key, 1, data, max_length, out);
    }
}
"#;

fn search_row(input: &str, index: &str) -> String {
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
        println!("RETENTION\n{}", ctx.retention.to_tsv());
        rows.lines()
            .find(|line| {
                line.starts_with("search\t") && line.contains(&format!("\ttest_item\t{index}\t"))
            })
            .expect("the test_item site is inventoried")
            .to_owned()
    })
    .expect("input type-checks")
}

#[test]
fn wave6r_static_dictionary_data_position_is_descendant_free() {
    let row = search_row(STATIC_DICT, "3");
    assert!(row.contains("\tT1\t"), "{row}");
    assert!(!row.contains("write-through-shared-view"), "{row}");
}

#[test]
fn wave6r_static_dictionary_dictionary_position_is_descendant_free() {
    let row = search_row(STATIC_DICT, "0");
    assert!(row.contains("\tT1\t"), "{row}");
    assert!(!row.contains("write-through-shared-view"), "{row}");
}
