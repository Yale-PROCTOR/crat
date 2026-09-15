//! wave-6p witnesses: pair-disjointness certificates lift `pair-raw-view`
//! exactly where disjointness is proven (charter wave-6p/001, R400-4).
//!
//! Every fixture is reduced from a real corpus function named in the test.
//! The RED state of each `..._delivers` witness was recorded with the
//! `with_pair_certificates` hook detached (report 001, artifact
//! `2026-09-15-wave-6p-certificate-market/red-*.log`).

use crate::{
    analyses::borrow_ownership::a5_overlap::{A5Mode, WholeProgramAttestation},
    bo_rewriter::{
        self,
        decision::{
            Decision, DegradeReason,
            a5_site_proof::A5SiteProofVerdict,
            pair_disjointness::{CERTIFICATE_FAMILY, CertificateKind, Unproved},
        },
    },
};

fn precise() -> Option<(A5Mode, Option<WholeProgramAttestation>)> {
    Some((
        A5Mode::PreciseReplay,
        Some(WholeProgramAttestation::FrozenBenchmarkGraph),
    ))
}

/// The decision of `callee`'s parameter `index`, by identity.
fn param_decision<'a>(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    table: &'a bo_rewriter::decision::DecisionTable,
    callee: &str,
    index: usize,
) -> &'a Decision {
    table
        .entries
        .iter()
        .find_map(|(subject, decision)| {
            (tcx.item_name(subject.fn_did.to_def_id()).as_str() == callee
                && matches!(subject.kind, bo_rewriter::decision::SubjectKind::Param { hir_index } if hir_index == index))
            .then_some(decision)
        })
        .unwrap_or_else(|| panic!("no parameter subject {callee}#{index}"))
}

fn is_pair_raw_view(decision: &Decision) -> bool {
    match decision {
        Decision::Degraded(degraded) => degraded.reason == DegradeReason::PairRawView,
        Decision::Ref { .. }
        | Decision::InferredRef { .. }
        | Decision::Slice { .. }
        | Decision::NestedSlice { .. }
        | Decision::Opt { .. }
        | Decision::Box(_)
        | Decision::Cursor { .. } => false,
    }
}

fn is_safe_reference(decision: &Decision) -> bool {
    match decision {
        Decision::Ref { .. }
        | Decision::InferredRef { .. }
        | Decision::Opt { slice: false, .. } => true,
        Decision::Slice { .. }
        | Decision::NestedSlice { .. }
        | Decision::Opt { slice: true, .. }
        | Decision::Box(_)
        | Decision::Cursor { .. }
        | Decision::Degraded(_) => false,
    }
}

fn dump(tcx: rustc_middle::ty::TyCtxt<'_>, table: &bo_rewriter::decision::DecisionTable) {
    for (subject, decision) in &table.entries {
        println!("{} {:?} {:?}", subject.label, subject.kind, decision);
    }
    for proof in &table.seams.overlap_proofs {
        println!(
            "overlap {} => {} #{} verdict={:?} reason={} fallback={:?} peers={}",
            tcx.def_path_str(proof.caller.to_def_id()),
            tcx.def_path_str(proof.callee.to_def_id()),
            proof.index,
            proof.verdict,
            proof.reason,
            proof.fallback.key(),
            proof.peer_receipts,
        );
    }
}

/// ht `ht_set` → `ht_set_entry((*table).entries, …, &mut (*table).length)`:
/// `plength: *mut size_t` beside `entries: *mut ht_entry`, both rooted at
/// `table`. `size_t` and `ht_entry` are distinct, neither a wildcard, neither a
/// member type of the other, no union carries both — the strict-aliasing type
/// rule certifies the pair.
const HT_SET_ENTRY: &str = r#"
    #[repr(C)]
    pub struct ht_entry { pub key: *const i8, pub value: *mut core::ffi::c_void }
    #[repr(C)]
    pub struct ht { pub entries: *mut ht_entry, pub capacity: u64, pub length: u64 }
    pub unsafe fn ht_set_entry(entries: *mut ht_entry, capacity: u64, key: *const i8, plength: *mut u64) -> *const i8 {
        let mut index = capacity.wrapping_sub(1);
        while !(*entries.offset(index as isize)).key.is_null() {
            index = index.wrapping_add(1);
            if index >= capacity { index = 0; }
        }
        if !plength.is_null() {
            *plength = (*plength).wrapping_add(1);
        }
        (*entries.offset(index as isize)).key = key;
        key
    }
    pub unsafe fn ht_set(table: *mut ht, key: *const i8) -> *const i8 {
        if (*table).length >= (*table).capacity.wrapping_div(2) {
            return 0 as *const i8;
        }
        ht_set_entry((*table).entries, (*table).capacity, key, &mut (*table).length)
    }
"#;

#[test]
fn w6p_type_rule_ht_set_entry_plength_delivers() {
    ::utils::compilation::run_compiler_on_str(HT_SET_ENTRY, |tcx| {
        let (table, ctx) =
            bo_rewriter::decide_table_with_ctx_config(tcx, precise()).expect("ht fixture decision");
        dump(tcx, &table);
        let plength = param_decision(tcx, &table, "ht_set_entry", 3);
        assert!(
            !is_pair_raw_view(plength),
            "plength must not stay pair-raw-view under the type-rule certificate: {plength:?}"
        );
        assert!(
            is_safe_reference(plength),
            "plength delivers as a safe reference form: {plength:?}"
        );
        let ledger = ctx
            .a5_site_proofs
            .pair_certificates()
            .expect("certificates ride the attested index")
            .ledger();
        assert!(
            ledger
                .iter()
                .any(|row| row.outcome == Ok(CertificateKind::TypeRule)),
            "the ledger records the type-rule certificate: {ledger:?}"
        );
        let certified = table
            .seams
            .overlap_proofs
            .iter()
            .chain(std::iter::empty())
            .filter(|proof| proof.peer_receipts.contains(CERTIFICATE_FAMILY))
            .count();
        let pair_rows = ctx
            .coconv
            .pair_sites()
            .iter()
            .filter(|site| site.peer_receipts.contains(CertificateKind::TypeRule.key()))
            .count();
        assert!(
            certified + pair_rows > 0,
            "the certificate is recorded per site in a pair receipt"
        );
    })
    .expect("ht fixture compilation");
}

/// The same call with `plength: *mut u64` replaced by a `*mut i8` reader: a
/// character-typed pointee is the wildcard and may alias anything, so the pair
/// stays held. This is the type rule's negative control.
const HT_SET_ENTRY_CHAR: &str = r#"
    #[repr(C)]
    pub struct ht_entry { pub key: *const i8, pub value: *mut core::ffi::c_void }
    #[repr(C)]
    pub struct ht { pub entries: *mut ht_entry, pub capacity: u64, pub tag: i8 }
    pub unsafe fn ht_set_entry(entries: *mut ht_entry, capacity: u64, key: *const i8, ptag: *mut i8) -> *const i8 {
        let mut index = capacity.wrapping_sub(1);
        while !(*entries.offset(index as isize)).key.is_null() {
            index = index.wrapping_add(1);
            if index >= capacity { index = 0; }
        }
        if !ptag.is_null() {
            *ptag = (*ptag).wrapping_add(1);
        }
        (*entries.offset(index as isize)).key = key;
        key
    }
    pub unsafe fn ht_set(table: *mut ht, key: *const i8) -> *const i8 {
        if (*table).capacity == 0 {
            return 0 as *const i8;
        }
        ht_set_entry((*table).entries, (*table).capacity, key, &mut (*table).tag)
    }
"#;

#[test]
fn w6p_type_rule_wildcard_char_pointee_stays_held() {
    ::utils::compilation::run_compiler_on_str(HT_SET_ENTRY_CHAR, |tcx| {
        let (table, ctx) = bo_rewriter::decide_table_with_ctx_config(tcx, precise())
            .expect("ht char fixture decision");
        dump(tcx, &table);
        let ledger = ctx
            .a5_site_proofs
            .pair_certificates()
            .expect("certificates ride the attested index")
            .ledger();
        assert!(
            ledger
                .iter()
                .all(|row| row.outcome != Ok(CertificateKind::TypeRule)),
            "a wildcard pointee never certifies by type: {ledger:?}"
        );
        assert!(
            ledger
                .iter()
                .any(|row| row.outcome == Err(Unproved::WildcardPointee)),
            "the hold names the wildcard: {ledger:?}"
        );
        let ptag = param_decision(tcx, &table, "ht_set_entry", 3);
        assert!(
            !is_safe_reference(ptag) || is_pair_raw_view(ptag),
            "ptag must not deliver beside `entries` on the wildcard: {ptag:?}"
        );
    })
    .expect("ht char fixture compilation");
}

/// brotli `BrotliCompressFragmentFastImpl` →
/// `BuildAndStoreCommandPrefixCode(cmd_histo.as_mut_ptr(), cmd_depth, cmd_bits,
/// storage_ix, storage)`: `storage_ix: *mut size_t` (a parameter of the
/// caller, never reassigned) beside `cmd_histo.as_mut_ptr()` (a caller-local
/// array). A stack object of the caller is disjoint from every pointer that
/// existed at entry — the distinct-roots certificate.
const CMD_HISTO: &str = r#"
    pub unsafe fn BuildAndStoreCommandPrefixCode(histogram: *const u32, depth: *mut u8, bits: *mut u16, storage_ix: *mut u64, storage: *mut u8) {
        let mut i = 0usize;
        while i < 128 {
            *depth.offset(i as isize) = (*histogram.offset(i as isize) & 7) as u8;
            *bits.offset(i as isize) = *histogram.offset(i as isize) as u16;
            i += 1;
        }
        *storage_ix = (*storage_ix).wrapping_add(8);
        *storage.offset((*storage_ix >> 3) as isize) = 0;
    }
    pub unsafe fn BrotliCompressFragmentFastImpl(input: *const u8, input_size: u64, cmd_depth: *mut u8, cmd_bits: *mut u16, storage_ix: *mut u64, storage: *mut u8) {
        let mut cmd_histo: [u32; 128] = [0; 128];
        let mut i = 0u64;
        while i < input_size {
            let byte = *input.offset(i as isize) as usize;
            cmd_histo[byte & 127] = cmd_histo[byte & 127].wrapping_add(1);
            i += 1;
        }
        BuildAndStoreCommandPrefixCode(cmd_histo.as_mut_ptr(), cmd_depth, cmd_bits, storage_ix, storage);
    }
"#;

#[test]
fn w6p_distinct_roots_local_array_beside_entry_parameter_delivers() {
    ::utils::compilation::run_compiler_on_str(CMD_HISTO, |tcx| {
        let (table, ctx) = bo_rewriter::decide_table_with_ctx_config(tcx, precise())
            .expect("cmd_histo fixture decision");
        dump(tcx, &table);
        let storage_ix = param_decision(tcx, &table, "BuildAndStoreCommandPrefixCode", 3);
        assert!(
            !is_pair_raw_view(storage_ix),
            "storage_ix must not stay pair-raw-view beside a caller-local array: {storage_ix:?}"
        );
        assert!(
            is_safe_reference(storage_ix),
            "storage_ix delivers as a safe reference: {storage_ix:?}"
        );
        let ledger = ctx
            .a5_site_proofs
            .pair_certificates()
            .expect("certificates ride the attested index")
            .ledger();
        assert!(
            ledger
                .iter()
                .any(|row| row.outcome == Ok(CertificateKind::DistinctRoots)),
            "the ledger records the distinct-roots certificate: {ledger:?}"
        );
    })
    .expect("cmd_histo fixture compilation");
}

/// Negative control for (a): the "array" argument is a pointer PARAMETER of
/// the caller, so both sides are entry storage and may alias — no certificate.
const CMD_HISTO_PARAM: &str = r#"
    pub unsafe fn BuildAndStoreCommandPrefixCode(histogram: *const u32, storage_ix: *mut u64) {
        *storage_ix = (*storage_ix).wrapping_add(*histogram as u64);
    }
    pub unsafe fn BrotliCompressFragmentFastImpl(cmd_histo: *mut u32, storage_ix: *mut u64) {
        BuildAndStoreCommandPrefixCode(cmd_histo, storage_ix);
    }
"#;

#[test]
fn w6p_distinct_roots_two_entry_parameters_stay_unproved() {
    ::utils::compilation::run_compiler_on_str(CMD_HISTO_PARAM, |tcx| {
        let (table, ctx) = bo_rewriter::decide_table_with_ctx_config(tcx, precise())
            .expect("cmd_histo param fixture decision");
        dump(tcx, &table);
        let ledger = ctx
            .a5_site_proofs
            .pair_certificates()
            .expect("certificates ride the attested index")
            .ledger();
        assert!(
            ledger
                .iter()
                .all(|row| row.outcome != Ok(CertificateKind::DistinctRoots)),
            "two entry pointers never certify by roots: {ledger:?}"
        );
    })
    .expect("cmd_histo param fixture compilation");
}

/// brotli `EncodeData` → `BrotliCreateBackwardReferences(…, &mut (*s).params,
/// &mut (*s).hasher_, (*s).dist_cache_.as_mut_ptr(), …)`: places under one
/// root that diverge at a `Field` — disjoint by layout.
const DISJOINT_FIELDS: &str = r#"
    #[repr(C)]
    pub struct Params { pub quality: i32, pub lgwin: i32 }
    #[repr(C)]
    pub struct State { pub params: Params, pub dist_cache_: [i32; 4], pub last_insert_len_: u64 }
    pub unsafe fn CreateBackwardReferences(params: *mut Params, dist_cache: *mut i32, last_insert_len: *mut u64) {
        (*params).quality += 1;
        *dist_cache.offset(0) = (*params).lgwin;
        *last_insert_len = (*last_insert_len).wrapping_add(1);
    }
    pub unsafe fn EncodeData(s: *mut State) {
        CreateBackwardReferences(&mut (*s).params, (*s).dist_cache_.as_mut_ptr(), &mut (*s).last_insert_len_);
    }
"#;

#[test]
fn w6p_disjoint_fields_of_one_object_certify() {
    ::utils::compilation::run_compiler_on_str(DISJOINT_FIELDS, |tcx| {
        let (table, ctx) = bo_rewriter::decide_table_with_ctx_config(tcx, precise())
            .expect("disjoint fields fixture decision");
        dump(tcx, &table);
        let ledger = ctx
            .a5_site_proofs
            .pair_certificates()
            .expect("certificates ride the attested index")
            .ledger();
        // `Params` vs `i32`: `i32` is a member type of `Params`, so the type
        // rule refuses that pair; the field certificate is what proves it.
        assert!(
            ledger
                .iter()
                .any(|row| { row.outcome == Ok(CertificateKind::DisjointFields) }),
            "disjoint fields of `*s` are certified: {ledger:?}"
        );
        assert!(
            ledger
                .iter()
                .all(|row| row.outcome != Err(Unproved::RootsUnknown)),
            "every pair under `s` is resolved: {ledger:?}"
        );
        for index in 0..3 {
            let decision = param_decision(tcx, &table, "CreateBackwardReferences", index);
            assert!(
                !is_pair_raw_view(decision),
                "parameter #{index} must not stay pair-raw-view: {decision:?}"
            );
        }
    })
    .expect("disjoint fields fixture compilation");
}

/// The same syntactic place passed twice is never disjoint from itself. (The
/// same place cast to two DIFFERENT pointee types is already held raw by the
/// analysis at the cast — `SilentCoercion { via: ArgCastFormUnbuilt }` — so no
/// pair reaches the consumer there; this witness pins the refusal on the pair
/// that does reach it.)
const SAME_PLACE: &str = r#"
    pub unsafe fn split(a: *mut u64, b: *mut u64) {
        *a = 1;
        *b = (*b).wrapping_add(2);
    }
    pub unsafe fn caller(p: *mut u64) {
        split(p, p);
    }
"#;

#[test]
fn w6p_same_place_is_refused_before_any_rule() {
    ::utils::compilation::run_compiler_on_str(SAME_PLACE, |tcx| {
        let (table, _ctx) = bo_rewriter::decide_table_with_ctx_config(tcx, precise())
            .expect("same-place fixture decision");
        dump(tcx, &table);
        let a = param_decision(tcx, &table, "split", 0);
        let b = param_decision(tcx, &table, "split", 1);
        assert!(
            !(is_safe_reference(a) && is_safe_reference(b)),
            "two live safe views of one place must not both deliver: {a:?} / {b:?}"
        );
        // The analysis frame decides one side raw before any pair is consulted,
        // so the refusal is exercised on the index directly.
        let program = bo_rewriter::collect_program(tcx);
        let index =
            bo_rewriter::decision::pair_disjointness::PairDisjointnessIndex::derive(&program);
        let function = |name: &str| {
            *program
                .functions
                .iter()
                .find(|did| tcx.item_name(did.to_def_id()).as_str() == name)
                .unwrap_or_else(|| panic!("no fn {name}"))
        };
        assert_eq!(
            index.certify_recorded(function("caller"), function("split"), 0, 1),
            Err(Unproved::SamePlace)
        );
        let _ = A5SiteProofVerdict::Clear;
    })
    .expect("same-place fixture compilation");
}

/// binn `binn_map_next(iter: *mut binn_iter, pid: *mut c_int, value: *mut binn)`:
/// `binn_iter` has `c_int` members (`type_0`, `count`, `current`), so an
/// `int*` may address one of them — the member-type clause of 6.5p7 refuses the
/// pair. This is the charter's own example, and the rule it sharpens holds it.
const MEMBER_TYPE: &str = r#"
    #[repr(C)]
    pub struct binn_iter { pub pnext: *mut u8, pub plimit: *mut u8, pub type_0: i32, pub count: i32, pub current: i32 }
    pub unsafe fn binn_read_next_pair(iter: *mut binn_iter, pid: *mut i32) -> i32 {
        if (*iter).current >= (*iter).count { return 0; }
        (*iter).current += 1;
        *pid = (*iter).current;
        1
    }
    pub unsafe fn binn_map_next(iter: *mut binn_iter, pid: *mut i32) -> i32 {
        binn_read_next_pair(iter, pid)
    }
"#;

#[test]
fn w6p_type_rule_member_type_stays_held() {
    ::utils::compilation::run_compiler_on_str(MEMBER_TYPE, |tcx| {
        let (table, ctx) = bo_rewriter::decide_table_with_ctx_config(tcx, precise())
            .expect("member-type fixture decision");
        dump(tcx, &table);
        let ledger = ctx
            .a5_site_proofs
            .pair_certificates()
            .expect("certificates ride the attested index")
            .ledger();
        assert!(
            ledger
                .iter()
                .any(|row| row.outcome == Err(Unproved::MemberType)),
            "an `int*` beside a struct with `int` members is held by the member clause: {ledger:?}"
        );
        assert!(ledger.iter().all(|row| row.outcome.is_err()), "{ledger:?}");
        let iter = param_decision(tcx, &table, "binn_read_next_pair", 0);
        let pid = param_decision(tcx, &table, "binn_read_next_pair", 1);
        assert!(
            !(is_safe_reference(iter) && is_safe_reference(pid)),
            "iter and pid must not both deliver: {iter:?} / {pid:?}"
        );
    })
    .expect("member-type fixture compilation");
}

/// brotli's `union { u64_0: uint64_t, u8_0: [uint8_t; 8] }` shape: a program
/// with a union carrying both `u64` and `f32` members means a `u64` object and
/// an `f32` object CAN overlap (two members of one union object), so the
/// type rule refuses the pair even though the two types are otherwise distinct.
const UNION_SIBLING: &str = r#"
    #[repr(C)]
    pub union Bits { pub u: u64, pub f: f32 }
    pub unsafe fn store(a: *mut u64, b: *mut f32) {
        *a = 1;
        *b = 2.0;
    }
    pub unsafe fn caller(x: *mut u64, y: *mut f32, bits: *mut Bits) {
        (*bits).u = 0;
        store(x, y);
    }
"#;

#[test]
fn w6p_type_rule_union_sibling_stays_held() {
    ::utils::compilation::run_compiler_on_str(UNION_SIBLING, |tcx| {
        let (table, ctx) = bo_rewriter::decide_table_with_ctx_config(tcx, precise())
            .expect("union-sibling fixture decision");
        dump(tcx, &table);
        let ledger = ctx
            .a5_site_proofs
            .pair_certificates()
            .expect("certificates ride the attested index")
            .ledger();
        assert!(
            ledger
                .iter()
                .any(|row| row.outcome == Err(Unproved::UnionSibling)),
            "a union carrying both types holds the pair: {ledger:?}"
        );
        assert!(ledger.iter().all(|row| row.outcome.is_err()), "{ledger:?}");
    })
    .expect("union-sibling fixture compilation");
}
