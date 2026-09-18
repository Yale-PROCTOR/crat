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
        let mut_facts =
            crate::analyses::borrow_ownership::mutability_facts::MutFacts::from_program(&program);
        let index = bo_rewriter::decision::pair_disjointness::PairDisjointnessIndex::derive(
            &program, &mut_facts, None,
        );
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

/// wave-6k's READ/READ shape (brotli `ExtendLastCommand` →
/// `CommandRestoreDistanceCode(last_command, &mut (*s).dist)`, both formals
/// immutable): `Command` and `BrotliDistanceParams` would pass the type rule,
/// but a READ/READ pair is the shared-read consumer's (charter (d)) — this lane
/// leaves it untouched so that consumer's receipts stay identical.
const READ_READ_PEERS: &str = r#"
    #[repr(C)]
    pub struct Command { pub insert_len_: u32, pub copy_len_: u32, pub dist_extra_: u32, pub cmd_prefix_: u16, pub dist_prefix_: u16 }
    #[repr(C)]
    pub struct BrotliDistanceParams { pub distance_postfix_bits: u32, pub num_direct_distance_codes: u32 }
    #[repr(C)]
    pub struct State { pub dist: BrotliDistanceParams }
    pub unsafe fn CommandRestoreDistanceCode(self_0: *const Command, dist: *const BrotliDistanceParams) -> u32 {
        if ((*self_0).dist_prefix_ as u32 & 0x3ff) < 16u32.wrapping_add((*dist).num_direct_distance_codes) {
            (*self_0).dist_prefix_ as u32 & 0x3ff
        } else { (*self_0).dist_extra_.wrapping_add((*dist).distance_postfix_bits) }
    }
    pub unsafe fn ExtendLastCommand(last_command: *mut Command, s: *mut State) -> u32 {
        let distance_code = CommandRestoreDistanceCode(last_command, &mut (*s).dist);
        (*last_command).dist_extra_ = distance_code;
        distance_code
    }
"#;

#[test]
fn w6p_read_read_pair_is_left_to_the_shared_read_consumer() {
    ::utils::compilation::run_compiler_on_str(READ_READ_PEERS, |tcx| {
        let (table, ctx) = bo_rewriter::decide_table_with_ctx_config(tcx, precise())
            .expect("read/read fixture decision");
        dump(tcx, &table);
        let ledger = ctx
            .a5_site_proofs
            .pair_certificates()
            .expect("certificates ride the attested index")
            .ledger();
        assert!(
            ledger
                .iter()
                .any(|row| row.outcome == Err(Unproved::ReadReadPeers)),
            "a READ/READ pair is refused to the shared-read consumer: {ledger:?}"
        );
        assert!(ledger.iter().all(|row| row.outcome.is_err()), "{ledger:?}");
        let proof = table
            .seams
            .overlap_proofs
            .iter()
            .find(|proof| {
                tcx.item_name(proof.callee.to_def_id()).as_str() == "CommandRestoreDistanceCode"
                    && proof.index == 1
            })
            .expect("the shared-read receipt is still produced");
        assert_eq!(proof.verdict, A5SiteProofVerdict::Overlapping);
        assert!(
            proof.reason.contains("native-shared-read-peers"),
            "{}",
            proof.reason
        );
    })
    .expect("read/read fixture compilation");
}

/// brotli `BrotliBuildMetaBlock`: `distance_histograms = BrotliAllocate(m, n)`
/// beside `&mut (*mb).distance_histograms_size`. `HistogramDistance` carries a
/// `size_t` member, so the type rule holds the pair; the distinct-roots
/// certificate needs `BrotliAllocate` admitted as an allocator — it returns a
/// local assigned through `(*m).alloc_func`, a function pointer whose only
/// closed-world target is `BrotliDefaultAllocFunc` → `malloc` (R402-5(6)).
const FN_PTR_ALLOCATOR: &str = r#"
    use core::ffi::c_void;
    extern "C" { fn malloc(n: u64) -> *mut c_void; fn exit(code: i32) -> !; }
    #[repr(C)]
    pub struct MemoryManager { pub alloc_func: Option<unsafe extern "C" fn(*mut c_void, u64) -> *mut c_void>, pub opaque: *mut c_void }
    #[repr(C)]
    pub struct HistogramDistance { pub data: [u32; 4], pub total_count: u64 }
    #[repr(C)]
    pub struct MetaBlockSplit { pub distance_histograms_size: u64, pub literal_count: u64 }
    pub unsafe extern "C" fn BrotliDefaultAllocFunc(opaque: *mut c_void, size: u64) -> *mut c_void { malloc(size) }
    pub unsafe fn BrotliInitMemoryManager(m: *mut MemoryManager, opaque: *mut c_void) {
        (*m).alloc_func = Some(BrotliDefaultAllocFunc as unsafe extern "C" fn(*mut c_void, u64) -> *mut c_void);
        (*m).opaque = opaque;
    }
    pub unsafe fn BrotliAllocate(m: *mut MemoryManager, n: u64) -> *mut c_void {
        let mut result = ((*m).alloc_func).expect("non-null function pointer")((*m).opaque, n);
        if result.is_null() { exit(1); }
        return result;
    }
    pub unsafe fn ClusterHistograms(histograms: *mut HistogramDistance, out_size: *mut u64) {
        (*histograms.offset(0)).total_count = 1;
        *out_size = (*out_size).wrapping_add(1);
    }
    pub unsafe fn BrotliBuildMetaBlock(m: *mut MemoryManager, mb: *mut MetaBlockSplit) {
        let mut distance_histograms = 0 as *mut HistogramDistance;
        if (*mb).distance_histograms_size > 0 {
            distance_histograms = BrotliAllocate(m, (*mb).distance_histograms_size.wrapping_mul(::core::mem::size_of::<HistogramDistance>() as u64)) as *mut HistogramDistance;
        }
        ClusterHistograms(distance_histograms, &mut (*mb).distance_histograms_size);
    }
    #[repr(C)]
    pub struct Encoder { pub memory_manager_: MemoryManager, pub mb: MetaBlockSplit }
    pub unsafe fn BrotliEncoderCreateInstance() -> *mut Encoder {
        let s = malloc(::core::mem::size_of::<Encoder>() as u64) as *mut Encoder;
        BrotliInitMemoryManager(&mut (*s).memory_manager_, 0 as *mut c_void);
        s
    }
    pub unsafe fn EncodeData(s: *mut Encoder) {
        BrotliBuildMetaBlock(&mut (*s).memory_manager_, &mut (*s).mb);
    }
"#;

/// The SAME program with one more store into `(*m).alloc_func`: a function
/// that returns its own `opaque` argument, which is not an allocator. The
/// field's admission is all-or-nothing (R433-6(2)), so `BrotliAllocate` is not
/// a wrapper here, `distance_histograms` is not a fresh root, and the pair
/// stays held by the type rule's member clause — the same verdict as before
/// the admission was built.
const FN_PTR_ALLOCATOR_FOREIGN_STORE: &str = r#"
    use core::ffi::c_void;
    extern "C" { fn malloc(n: u64) -> *mut c_void; fn exit(code: i32) -> !; }
    #[repr(C)]
    pub struct MemoryManager { pub alloc_func: Option<unsafe extern "C" fn(*mut c_void, u64) -> *mut c_void>, pub opaque: *mut c_void }
    #[repr(C)]
    pub struct HistogramDistance { pub data: [u32; 4], pub total_count: u64 }
    #[repr(C)]
    pub struct MetaBlockSplit { pub distance_histograms_size: u64, pub literal_count: u64 }
    pub unsafe extern "C" fn BrotliDefaultAllocFunc(opaque: *mut c_void, size: u64) -> *mut c_void { malloc(size) }
    pub unsafe extern "C" fn ArenaAllocFunc(opaque: *mut c_void, size: u64) -> *mut c_void { opaque }
    pub unsafe fn BrotliInitMemoryManager(m: *mut MemoryManager, opaque: *mut c_void) {
        (*m).alloc_func = Some(BrotliDefaultAllocFunc as unsafe extern "C" fn(*mut c_void, u64) -> *mut c_void);
        (*m).opaque = opaque;
    }
    pub unsafe fn BrotliUseArena(m: *mut MemoryManager, arena: *mut c_void) {
        (*m).alloc_func = Some(ArenaAllocFunc as unsafe extern "C" fn(*mut c_void, u64) -> *mut c_void);
        (*m).opaque = arena;
    }
    pub unsafe fn BrotliAllocate(m: *mut MemoryManager, n: u64) -> *mut c_void {
        let mut result = ((*m).alloc_func).expect("non-null function pointer")((*m).opaque, n);
        if result.is_null() { exit(1); }
        return result;
    }
    pub unsafe fn ClusterHistograms(histograms: *mut HistogramDistance, out_size: *mut u64) {
        (*histograms.offset(0)).total_count = 1;
        *out_size = (*out_size).wrapping_add(1);
    }
    pub unsafe fn BrotliBuildMetaBlock(m: *mut MemoryManager, mb: *mut MetaBlockSplit) {
        let mut distance_histograms = 0 as *mut HistogramDistance;
        if (*mb).distance_histograms_size > 0 {
            distance_histograms = BrotliAllocate(m, (*mb).distance_histograms_size.wrapping_mul(::core::mem::size_of::<HistogramDistance>() as u64)) as *mut HistogramDistance;
        }
        ClusterHistograms(distance_histograms, &mut (*mb).distance_histograms_size);
    }
"#;

/// brotli `SplitByteVectorCommand` → `FindBlocksCommand`, mirrored: three
/// separate `BrotliAllocate` locals handed to one call. `cost` and
/// `insert_cost` are both `*mut f64` (same type), `switch_signal` is `*mut u8`
/// (a wildcard) and `histograms` carries an `f64` member — so no type-rule
/// route exists and rule (a) is the only one, which needs `BrotliAllocate`
/// admitted through `(*m).alloc_func`. The field carries a caller-supplied
/// store, so only R409-1's allocator contract admits it: these are the nine
/// `FindBlocks{Command,Distance,Literal}` rows of report 007.
const CONTRACT_FIND_BLOCKS: &str = r#"
    use core::ffi::c_void;
    extern "C" { fn malloc(n: u64) -> *mut c_void; fn exit(code: i32) -> !; }
    #[repr(C)]
    pub struct MemoryManager { pub alloc_func: Option<unsafe extern "C" fn(*mut c_void, u64) -> *mut c_void>, pub opaque: *mut c_void }
    #[repr(C)]
    pub struct HistogramCommand { pub data_: [u32; 8], pub total_count_: u64, pub bit_cost_: f64 }
    pub unsafe extern "C" fn BrotliDefaultAllocFunc(opaque: *mut c_void, size: u64) -> *mut c_void { malloc(size) }
    pub unsafe extern "C" fn BrotliInitMemoryManager(m: *mut MemoryManager, alloc_func: Option<unsafe extern "C" fn(*mut c_void, u64) -> *mut c_void>, opaque: *mut c_void) {
        if alloc_func.is_none() {
            (*m).alloc_func = Some(BrotliDefaultAllocFunc as unsafe extern "C" fn(*mut c_void, u64) -> *mut c_void);
            (*m).opaque = 0 as *mut c_void;
        } else {
            (*m).alloc_func = alloc_func;
            (*m).opaque = opaque;
        };
    }
    pub unsafe fn BrotliAllocate(m: *mut MemoryManager, n: u64) -> *mut c_void {
        let mut result = ((*m).alloc_func).expect("non-null function pointer")((*m).opaque, n);
        if result.is_null() { exit(1); }
        return result;
    }
    pub unsafe fn FindBlocksCommand(data: *const u16, length: u64, histograms: *const HistogramCommand, insert_cost: *mut f64, cost: *mut f64, switch_signal: *mut u8) {
        *insert_cost = 0f64;
        *cost = *insert_cost + 1f64;
        *switch_signal = 1;
    }
    pub unsafe fn SplitByteVectorCommand(m: *mut MemoryManager, data: *const u16, length: u64, histograms: *const HistogramCommand, num_histograms: u64) {
        let mut insert_cost = BrotliAllocate(m, num_histograms.wrapping_mul(8)) as *mut f64;
        let mut cost = BrotliAllocate(m, num_histograms.wrapping_mul(8)) as *mut f64;
        let mut switch_signal = BrotliAllocate(m, length) as *mut u8;
        FindBlocksCommand(data, length, histograms, insert_cost, cost, switch_signal);
    }
"#;

/// brotli `CreateBackwardReferencesNH55` → `InitCommand`, mirrored: the
/// cursor idiom C2Rust emits everywhere — `let fresh15 = commands; commands =
/// commands.offset(1); InitCommand(fresh15, &mut …)`. Both pointers walk
/// inside objects the caller can name, but neither is an allocation, so today
/// `fresh15` and the reassigned parameter both classify `Unknown` and the pair
/// reads `pair-disjointness-unproved:roots-unknown` — brotli's single largest
/// unproven reason (2,376 sites; report 012 §3). The peer here is a stack
/// scalar, so the moment the cursor HAS a class, rule (a) fires.
const DERIVED_ROOT_CURSOR: &str = r#"
    #[repr(C)]
    pub struct Command { pub len: u32, pub code: u32 }
    pub unsafe fn InitCommand(cmd: *mut Command, scratch: *mut u32, len: u32) {
        (*cmd).len = len.wrapping_add(*scratch);
        *scratch = (*cmd).len;
    }
    pub unsafe fn CreateBackwardReferences(mut commands: *mut Command, n: u64) {
        let mut scratch: u32 = 0;
        let mut i: u64 = 0;
        while i < n {
            let fresh15 = commands;
            commands = commands.offset(1);
            InitCommand(fresh15, &mut scratch, 3);
            i = i.wrapping_add(1);
        }
    }
"#;

/// The derived-root rule: a local whose every assignment derives from ONE
/// place inherits that place's root, and a parameter that only walks within
/// its own object keeps its entry class. `Command` carries a `u32` member, so
/// the type rule cannot fire — the roots are what separate the pair.
#[test]
fn w6p_derived_root_cursor_certifies_against_a_stack_peer() {
    ::utils::compilation::run_compiler_on_str(DERIVED_ROOT_CURSOR, |tcx| {
        let program = bo_rewriter::collect_program(tcx);
        let mut_facts =
            crate::analyses::borrow_ownership::mutability_facts::MutFacts::from_program(&program);
        let index = bo_rewriter::decision::pair_disjointness::PairDisjointnessIndex::derive(
            &program, &mut_facts, None,
        );
        let function = |name: &str| {
            *program
                .functions
                .iter()
                .find(|did| tcx.item_name(did.to_def_id()).as_str() == name)
                .unwrap_or_else(|| panic!("no fn {name}"))
        };
        assert_eq!(
            index.certify_recorded(
                function("CreateBackwardReferences"),
                function("InitCommand"),
                0,
                1
            ),
            Ok(CertificateKind::DistinctRoots),
            "the cursor derives from the parameter; the peer is a stack object"
        );
    })
    .expect("derived-root fixture compilation");
}

/// Two different sources keep the local `Unknown` — the rule is single
/// derivation, not any derivation.
const DERIVED_ROOT_TWO_SOURCES: &str = r#"
    #[repr(C)]
    pub struct Command { pub len: u32, pub code: u32 }
    pub unsafe fn InitCommand(cmd: *mut Command, scratch: *mut u32, len: u32) {
        (*cmd).len = len.wrapping_add(*scratch);
        *scratch = (*cmd).len;
    }
    pub unsafe fn CreateBackwardReferences(mut commands: *mut Command, spare: *mut Command, n: u64) {
        let mut scratch: u32 = 0;
        let mut cursor = commands;
        if n > 7 { cursor = spare; }
        InitCommand(cursor, &mut scratch, 3);
    }
"#;

#[test]
fn w6p_two_sources_keep_the_root_unknown() {
    ::utils::compilation::run_compiler_on_str(DERIVED_ROOT_TWO_SOURCES, |tcx| {
        let program = bo_rewriter::collect_program(tcx);
        let mut_facts =
            crate::analyses::borrow_ownership::mutability_facts::MutFacts::from_program(&program);
        let index = bo_rewriter::decision::pair_disjointness::PairDisjointnessIndex::derive(
            &program, &mut_facts, None,
        );
        let function = |name: &str| {
            *program
                .functions
                .iter()
                .find(|did| tcx.item_name(did.to_def_id()).as_str() == name)
                .unwrap_or_else(|| panic!("no fn {name}"))
        };
        assert_eq!(
            index.certify_recorded(
                function("CreateBackwardReferences"),
                function("InitCommand"),
                0,
                1
            ),
            // Once the roots decline, `certify` reports the next rule's own
            // reason — here the member clause (`Command` carries a `u32`).
            Err(Unproved::MemberType),
            "a local assigned from two different places has no single root"
        );
    })
    .expect("two-source fixture compilation");
}

/// brotli `ClusterBlocksCommand` → `RemapBlockIdsCommand`, mirrored: the
/// caller allocates `block_ids` and `new_id` at two DIFFERENT
/// `BrotliAllocate` statements and hands both to one call. `*mut u8` beside
/// `*mut u16` is a wildcard pair, so rule (b) cannot fire; the two roots are
/// what separates them. These are the three `RemapBlockIds{Command,Distance,
/// Literal}::new_id#3` rows — the contract-roots consumer's whole measured
/// market at batch 12 (report 011 §5).
const CONTRACT_REMAP_BLOCK_IDS: &str = r#"
    use core::ffi::c_void;
    extern "C" { fn malloc(n: u64) -> *mut c_void; fn exit(code: i32) -> !; }
    #[repr(C)]
    pub struct MemoryManager { pub alloc_func: Option<unsafe extern "C" fn(*mut c_void, u64) -> *mut c_void>, pub opaque: *mut c_void }
    pub unsafe extern "C" fn BrotliDefaultAllocFunc(opaque: *mut c_void, size: u64) -> *mut c_void { malloc(size) }
    pub unsafe extern "C" fn BrotliInitMemoryManager(m: *mut MemoryManager, alloc_func: Option<unsafe extern "C" fn(*mut c_void, u64) -> *mut c_void>, opaque: *mut c_void) {
        if alloc_func.is_none() {
            (*m).alloc_func = Some(BrotliDefaultAllocFunc as unsafe extern "C" fn(*mut c_void, u64) -> *mut c_void);
            (*m).opaque = 0 as *mut c_void;
        } else {
            (*m).alloc_func = alloc_func;
            (*m).opaque = opaque;
        };
    }
    pub unsafe fn BrotliAllocate(m: *mut MemoryManager, n: u64) -> *mut c_void {
        let mut result = ((*m).alloc_func).expect("non-null function pointer")((*m).opaque, n);
        if result.is_null() { exit(1); }
        return result;
    }
    pub unsafe fn RemapBlockIdsCommand(block_ids: *mut u8, length: u64, new_id: *mut u16, num_histograms: u64) -> u64 {
        let mut i: u64 = 0;
        while i < num_histograms { *new_id.offset(i as isize) = 256; i = i.wrapping_add(1); }
        i = 0;
        while i < length {
            *new_id.offset(*block_ids.offset(i as isize) as isize) = 1;
            i = i.wrapping_add(1);
        }
        num_histograms
    }
    pub unsafe fn ClusterBlocksCommand(m: *mut MemoryManager, length: u64, num_histograms: u64) {
        let mut block_ids = BrotliAllocate(m, length) as *mut u8;
        let mut new_id = BrotliAllocate(m, num_histograms.wrapping_mul(2)) as *mut u16;
        RemapBlockIdsCommand(block_ids, length, new_id, num_histograms);
    }
"#;

/// The three `RemapBlockIds*::new_id` rows: two ports of one contract-backed
/// allocator in ONE caller, at two distinct statements, are two fresh roots —
/// and the pair says which premise it rests on.
#[test]
fn w6p_remap_block_ids_pair_certifies_on_two_allocator_ports() {
    ::utils::compilation::run_compiler_on_str(CONTRACT_REMAP_BLOCK_IDS, |tcx| {
        let program = bo_rewriter::collect_program(tcx);
        let mut_facts =
            crate::analyses::borrow_ownership::mutability_facts::MutFacts::from_program(&program);
        let index = bo_rewriter::decision::pair_disjointness::PairDisjointnessIndex::derive(
            &program, &mut_facts, None,
        );
        let function = |name: &str| {
            *program
                .functions
                .iter()
                .find(|did| tcx.item_name(did.to_def_id()).as_str() == name)
                .unwrap_or_else(|| panic!("no fn {name}"))
        };
        assert_eq!(
            index.certify_recorded(
                function("ClusterBlocksCommand"),
                function("RemapBlockIdsCommand"),
                0,
                2
            ),
            Ok(CertificateKind::DistinctRootsUnderContract),
            "block_ids and new_id are two ports of one allocator at distinct statements"
        );
    })
    .expect("RemapBlockIds fixture compilation");
}

/// The nine rows: two allocations of one contract-backed allocator are
/// distinct roots, and the certificate says so — `DistinctRootsUnderContract`,
/// the auditable receipt R434-4(5) asks for.
#[test]
fn w6p_find_blocks_pairs_certify_under_the_allocator_contract() {
    ::utils::compilation::run_compiler_on_str(CONTRACT_FIND_BLOCKS, |tcx| {
        let program = bo_rewriter::collect_program(tcx);
        let mut_facts =
            crate::analyses::borrow_ownership::mutability_facts::MutFacts::from_program(&program);
        let index = bo_rewriter::decision::pair_disjointness::PairDisjointnessIndex::derive(
            &program, &mut_facts, None,
        );
        let function = |name: &str| {
            *program
                .functions
                .iter()
                .find(|did| tcx.item_name(did.to_def_id()).as_str() == name)
                .unwrap_or_else(|| panic!("no fn {name}"))
        };
        let (caller, callee) = (
            function("SplitByteVectorCommand"),
            function("FindBlocksCommand"),
        );
        for (left, right) in [(3usize, 4usize), (3, 5), (4, 5)] {
            assert_eq!(
                index.certify_recorded(caller, callee, left, right),
                Ok(CertificateKind::DistinctRootsUnderContract),
                "FindBlocksCommand#{left} beside #{right}"
            );
        }
    })
    .expect("FindBlocks contract fixture compilation");
}

/// brotli's REAL init, mirrored: `BrotliInitMemoryManager` stores
/// `BrotliDefaultAllocFunc` when the caller passes `None` and the caller's own
/// function pointer otherwise (`lib.rs:488888` and `:488898`; the decoder's
/// `BrotliDecoderStateInit` is the same shape at `:115002`). The second store
/// is a PARAMETER, which this read cannot resolve to a function item, so the
/// field is refused — and since `BrotliEncoderCreateInstance` is a
/// `#[no_mangle]` entry point that forwards its own parameter, no closed-world
/// argument can settle it either. Only the allocator CONTRACT can (R409-1,
/// era-5c). This witness pins that the rule does NOT quietly admit it.
const FN_PTR_ALLOCATOR_PARAMETER_STORE: &str = r#"
    use core::ffi::c_void;
    extern "C" { fn malloc(n: u64) -> *mut c_void; fn exit(code: i32) -> !; }
    #[repr(C)]
    pub struct MemoryManager { pub alloc_func: Option<unsafe extern "C" fn(*mut c_void, u64) -> *mut c_void>, pub opaque: *mut c_void }
    #[repr(C)]
    pub struct HistogramDistance { pub data: [u32; 4], pub total_count: u64 }
    #[repr(C)]
    pub struct MetaBlockSplit { pub distance_histograms_size: u64, pub literal_count: u64 }
    pub unsafe extern "C" fn BrotliDefaultAllocFunc(opaque: *mut c_void, size: u64) -> *mut c_void { malloc(size) }
    pub unsafe extern "C" fn BrotliInitMemoryManager(m: *mut MemoryManager, alloc_func: Option<unsafe extern "C" fn(*mut c_void, u64) -> *mut c_void>, opaque: *mut c_void) {
        if alloc_func.is_none() {
            (*m).alloc_func = Some(BrotliDefaultAllocFunc as unsafe extern "C" fn(*mut c_void, u64) -> *mut c_void);
            (*m).opaque = 0 as *mut c_void;
        } else {
            (*m).alloc_func = alloc_func;
            (*m).opaque = opaque;
        };
    }
    pub unsafe fn BrotliAllocate(m: *mut MemoryManager, n: u64) -> *mut c_void {
        let mut result = ((*m).alloc_func).expect("non-null function pointer")((*m).opaque, n);
        if result.is_null() { exit(1); }
        return result;
    }
    pub unsafe fn ClusterHistograms(histograms: *mut HistogramDistance, out_size: *mut u64) {
        (*histograms.offset(0)).total_count = 1;
        *out_size = (*out_size).wrapping_add(1);
    }
    pub unsafe fn BrotliBuildMetaBlock(m: *mut MemoryManager, mb: *mut MetaBlockSplit) {
        let mut distance_histograms = 0 as *mut HistogramDistance;
        if (*mb).distance_histograms_size > 0 {
            distance_histograms = BrotliAllocate(m, (*mb).distance_histograms_size.wrapping_mul(::core::mem::size_of::<HistogramDistance>() as u64)) as *mut HistogramDistance;
        }
        ClusterHistograms(distance_histograms, &mut (*mb).distance_histograms_size);
    }
"#;

/// The corpus's own shape, admitted under the contract (R434-4(5)): the store
/// from a parameter is what report 008 measured, and R409-1 is the user's
/// decision that brotli's `alloc_func` is malloc-like. The certificate says
/// which premise it rests on.
#[test]
fn w6p_parameter_supplied_allocator_field_certifies_under_the_contract() {
    ::utils::compilation::run_compiler_on_str(FN_PTR_ALLOCATOR_PARAMETER_STORE, |tcx| {
        let (table, ctx) = bo_rewriter::decide_table_with_ctx_config(tcx, precise())
            .expect("parameter-store fixture decision");
        dump(tcx, &table);
        let ledger = ctx
            .a5_site_proofs
            .pair_certificates()
            .expect("certificates ride the attested index")
            .ledger();
        assert!(
            ledger
                .iter()
                .any(|row| row.outcome == Ok(CertificateKind::DistinctRootsUnderContract)),
            "the contract admits the caller-supplied allocator, with its receipt: {ledger:?}"
        );
        assert!(
            ledger
                .iter()
                .all(|row| row.outcome != Ok(CertificateKind::DistinctRoots)),
            "and never as a PROVEN root — the receipt is the point: {ledger:?}"
        );
    })
    .expect("parameter-store fixture compilation");
}

/// One store this read cannot call an allocator refuses the whole field.
#[test]
fn w6p_one_foreign_store_refuses_the_allocator_field() {
    ::utils::compilation::run_compiler_on_str(FN_PTR_ALLOCATOR_FOREIGN_STORE, |tcx| {
        let (table, ctx) = bo_rewriter::decide_table_with_ctx_config(tcx, precise())
            .expect("arena fixture decision");
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
            "a field with one non-allocator store is not an allocator field: {ledger:?}"
        );
        assert!(
            ledger
                .iter()
                .any(|row| row.outcome == Err(Unproved::MemberType)),
            "the pair stays held by the member clause: {ledger:?}"
        );
    })
    .expect("arena fixture compilation");
}

/// End-to-end through the production web. RED until R433-6(2): the MIR
/// inventory does not resolve the field-stored allocator pointer
/// `(*m).alloc_func` in this reduction (no `BrotliAllocate → *` site is
/// produced), and the corpus agrees — report 007 measured brotli's 13
/// `distinct-roots` certificates and not one rests on a heap root. The field
/// rule admits it instead: every store into `MemoryManager::alloc_func` in
/// the program is `BrotliDefaultAllocFunc`, itself a wrapper of `malloc`, so
/// `BrotliAllocate` is a wrapper, `distance_histograms` a fresh root, and the
/// pair beside `&mut (*mb).distance_histograms_size` certifies by distinct
/// roots.
#[test]
fn w6p_distinct_roots_fn_pointer_allocator_wrapper_delivers() {
    ::utils::compilation::run_compiler_on_str(FN_PTR_ALLOCATOR, |tcx| {
        let (table, ctx) = bo_rewriter::decide_table_with_ctx_config(tcx, precise())
            .expect("fn-pointer allocator fixture decision");
        dump(tcx, &table);
        let ledger = ctx
            .a5_site_proofs
            .pair_certificates()
            .expect("certificates ride the attested index")
            .ledger();
        assert!(
            ledger
                .iter()
                .any(|row| row.outcome == Ok(CertificateKind::DistinctRoots)),
            "BrotliAllocate's result is a fresh root through the closed-world fn-pointer group: {ledger:?}"
        );
        let out_size = param_decision(tcx, &table, "ClusterHistograms", 1);
        assert!(
            !is_pair_raw_view(out_size),
            "out_size must not stay pair-raw-view beside the wrapper allocation: {out_size:?}"
        );
    })
    .expect("fn-pointer allocator fixture compilation");
}

/// The mechanism, with the inventory naming the target the way the closed
/// world does on the corpus: `BrotliAllocate`'s call through `(*m).alloc_func`
/// resolves to `BrotliDefaultAllocFunc` (a wrapper of `malloc`), so
/// `BrotliAllocate` is a wrapper, its result a fresh root, and the pair beside
/// `&mut (*mb).distance_histograms_size` certifies by distinct roots — while
/// the same pair without the inventory stays held by the member clause.
#[test]
fn w6p_distinct_roots_fn_pointer_allocator_wrapper_admitted_by_the_inventory() {
    // The ARENA fixture: its `alloc_func` carries one non-allocator store, so
    // R433-6(2)'s field rule refuses it and the MIR inventory is the only
    // route left — which is what this witness is about.
    ::utils::compilation::run_compiler_on_str(FN_PTR_ALLOCATOR_FOREIGN_STORE, |tcx| {
        use rustc_hir::intravisit::{self, Visitor};
        let program = bo_rewriter::collect_program(tcx);
        let mut_facts =
            crate::analyses::borrow_ownership::mutability_facts::MutFacts::from_program(&program);
        let function = |name: &str| {
            *program
                .functions
                .iter()
                .find(|did| tcx.item_name(did.to_def_id()).as_str() == name)
                .unwrap_or_else(|| panic!("no fn {name}"))
        };
        // The span of the one call through a function pointer in BrotliAllocate.
        struct IndirectCalls(Vec<rustc_span::Span>);
        impl<'tcx> Visitor<'tcx> for IndirectCalls {
            fn visit_expr(&mut self, expr: &'tcx rustc_hir::Expr<'tcx>) {
                if let rustc_hir::ExprKind::Call(callee, _) = &expr.kind
                    && !matches!(callee.kind, rustc_hir::ExprKind::Path(..))
                {
                    self.0.push(expr.span);
                }
                intravisit::walk_expr(self, expr);
            }
        }
        let allocate = function("BrotliAllocate");
        let body = tcx.hir_body(tcx.hir_node_by_def_id(allocate).body_id().expect("body"));
        let mut calls = IndirectCalls(Vec::new());
        calls.visit_body(body);
        assert_eq!(calls.0.len(), 1, "one call through the function pointer");
        let sites = vec![bo_rewriter::decision::lifetime::MirCallTargetSite {
            caller: allocate,
            callee: function("BrotliDefaultAllocFunc"),
            block: 0,
            argument_count: 2,
            span: calls.0[0],
        }];
        let with = bo_rewriter::decision::pair_disjointness::PairDisjointnessIndex::derive(
            &program,
            &mut_facts,
            Some(&sites),
        );
        assert_eq!(
            with.certify_recorded(
                function("BrotliBuildMetaBlock"),
                function("ClusterHistograms"),
                0,
                1
            ),
            Ok(CertificateKind::DistinctRoots)
        );
        // A target that is NOT an allocator wrapper admits nothing.
        let sites = vec![bo_rewriter::decision::lifetime::MirCallTargetSite {
            caller: allocate,
            callee: function("ArenaAllocFunc"),
            block: 0,
            argument_count: 2,
            span: calls.0[0],
        }];
        let without = bo_rewriter::decision::pair_disjointness::PairDisjointnessIndex::derive(
            &program,
            &mut_facts,
            Some(&sites),
        );
        assert_eq!(
            without.certify_recorded(
                function("BrotliBuildMetaBlock"),
                function("ClusterHistograms"),
                0,
                1
            ),
            Err(Unproved::MemberType)
        );
        // An inventory that names no target for THIS call (a site elsewhere in
        // the body) admits nothing either: an unresolved call is not fresh.
        let sites = vec![bo_rewriter::decision::lifetime::MirCallTargetSite {
            caller: allocate,
            callee: function("BrotliDefaultAllocFunc"),
            block: 0,
            argument_count: 2,
            span: rustc_span::DUMMY_SP,
        }];
        let unresolved = bo_rewriter::decision::pair_disjointness::PairDisjointnessIndex::derive(
            &program,
            &mut_facts,
            Some(&sites),
        );
        assert_eq!(
            unresolved.certify_recorded(
                function("BrotliBuildMetaBlock"),
                function("ClusterHistograms"),
                0,
                1
            ),
            Err(Unproved::MemberType)
        );
    })
    .expect("fn-pointer allocator mechanism compilation");
}

/// Negative control: a wrapper whose function pointer is resolvable NEITHER
/// by the field rule (the arena fixture stores a non-allocator into the same
/// field) NOR by the web (no inventory) stays unproved.
#[test]
fn w6p_fn_pointer_allocator_without_the_web_stays_unproved() {
    ::utils::compilation::run_compiler_on_str(FN_PTR_ALLOCATOR_FOREIGN_STORE, |tcx| {
        let program = bo_rewriter::collect_program(tcx);
        let mut_facts =
            crate::analyses::borrow_ownership::mutability_facts::MutFacts::from_program(&program);
        let index = bo_rewriter::decision::pair_disjointness::PairDisjointnessIndex::derive(
            &program, &mut_facts, None,
        );
        let function = |name: &str| {
            *program
                .functions
                .iter()
                .find(|did| tcx.item_name(did.to_def_id()).as_str() == name)
                .unwrap_or_else(|| panic!("no fn {name}"))
        };
        assert_eq!(
            index.certify_recorded(
                function("BrotliBuildMetaBlock"),
                function("ClusterHistograms"),
                0,
                1
            ),
            Err(Unproved::MemberType),
            "with neither route the wrapper is not an allocator and the type rule holds"
        );
    })
    .expect("fn-pointer allocator control compilation");
}

/// brotli `FindLongestMatchH65` → `FindLongestMatchH6(&mut (*self_0).ha, dictionary,
/// data, …, distance_cache, …, out)` / `FindLongestMatchHROLLING(&mut (*self_0).hb, …)`,
/// called from `CreateBackwardReferencesNH65(privat, &(*params).dictionary, …,
/// dist_cache, …, &mut sr)`. Report 002: the whole family reverted at compile
/// once its pairs were certified; the round-1 diagnostics were not retained, so
/// this fixture reproduces the shape and reads them.
const FIND_LONGEST_MATCH_FAMILY: &str = r#"
    #[repr(C)]
    pub struct HasherCommon { pub is_prepared_: i32, pub dict_num_lookups: u64 }
    #[repr(C)]
    pub struct H6 { pub common: *mut HasherCommon, pub buckets_: *mut u32, pub hash_shift_: i32 }
    #[repr(C)]
    pub struct HROLLING { pub common: *mut HasherCommon, pub state: u32, pub table: *mut u32 }
    #[repr(C)]
    pub struct H65 { pub ha: H6, pub hb: HROLLING, pub hb_common: HasherCommon, pub extra: *mut core::ffi::c_void, pub common: *mut HasherCommon }
    #[repr(C)]
    pub struct BrotliEncoderDictionary { pub words: *const u8, pub cutoffTransformsCount: u32 }
    #[repr(C)]
    pub struct DistanceParams { pub max_distance: u64 }
    #[repr(C)]
    pub struct BrotliEncoderParams { pub dictionary: BrotliEncoderDictionary, pub dist: DistanceParams }
    #[repr(C)]
    pub struct HasherSearchResult { pub len: u64, pub distance: u64, pub score: u64, pub len_code_delta: i32 }
    pub unsafe fn FindLongestMatchH6(self_0: *mut H6, dictionary: *const BrotliEncoderDictionary, data: *const u8, ring_buffer_mask: u64, distance_cache: *const i32, cur_ix: u64, max_length: u64, max_backward: u64, dictionary_distance: u64, max_distance: u64, out: *mut HasherSearchResult) {
        let mut best_score = (*out).score;
        let mut best_len = (*out).len;
        (*out).len = 0;
        (*out).len_code_delta = 0;
        let mut i = 0;
        while i < 4 {
            let backward = *distance_cache.offset(i as isize) as u64;
            if backward <= max_backward && backward <= max_distance {
                let prev_ix = cur_ix.wrapping_sub(backward) & ring_buffer_mask;
                if *data.offset(prev_ix as isize) == *data.offset((cur_ix & ring_buffer_mask) as isize) {
                    best_len = best_len.wrapping_add(1);
                    best_score = best_score.wrapping_add(max_length);
                    (*out).len = best_len;
                    (*out).distance = backward;
                    (*out).score = best_score;
                }
            }
            i += 1;
        }
        (*self_0).hash_shift_ = (*dictionary).cutoffTransformsCount as i32;
        (*(*self_0).common).dict_num_lookups = (*(*self_0).common).dict_num_lookups.wrapping_add(dictionary_distance);
    }
    pub unsafe fn FindLongestMatchHROLLING(self_0: *mut HROLLING, dictionary: *const BrotliEncoderDictionary, data: *const u8, ring_buffer_mask: u64, distance_cache: *const i32, cur_ix: u64, max_length: u64, max_backward: u64, dictionary_distance: u64, max_distance: u64, out: *mut HasherSearchResult) {
        let backward = *distance_cache.offset(0) as u64;
        if backward <= max_backward && backward <= max_distance && max_length > 0 {
            let prev_ix = cur_ix.wrapping_sub(backward) & ring_buffer_mask;
            (*self_0).state = *data.offset(prev_ix as isize) as u32;
            (*out).len = max_length;
            (*out).distance = backward.wrapping_add(dictionary_distance);
        }
        (*self_0).state = (*self_0).state.wrapping_add((*dictionary).cutoffTransformsCount);
    }
    pub unsafe fn FindLongestMatchH65(self_0: *mut H65, dictionary: *const BrotliEncoderDictionary, data: *const u8, ring_buffer_mask: u64, distance_cache: *const i32, cur_ix: u64, max_length: u64, max_backward: u64, dictionary_distance: u64, max_distance: u64, out: *mut HasherSearchResult) {
        FindLongestMatchH6(&mut (*self_0).ha, dictionary, data, ring_buffer_mask, distance_cache, cur_ix, max_length, max_backward, dictionary_distance, max_distance, out);
        FindLongestMatchHROLLING(&mut (*self_0).hb, dictionary, data, ring_buffer_mask, distance_cache, cur_ix, max_length, max_backward, dictionary_distance, max_distance, out);
    }
    pub unsafe fn CreateBackwardReferencesNH65(privat: *mut H65, params: *const BrotliEncoderParams, ringbuffer: *const u8, ringbuffer_mask: u64, dist_cache: *mut i32, position: u64, max_length: u64) {
        let mut sr = HasherSearchResult { len: 0, distance: 0, score: 0, len_code_delta: 0 };
        sr.score = 4;
        FindLongestMatchH65(privat, &(*params).dictionary, ringbuffer, ringbuffer_mask, dist_cache, position, max_length, position, 16, (*params).dist.max_distance, &mut sr);
        if sr.score > 4 {
            *dist_cache.offset(0) = sr.distance as i32;
        }
    }
"#;

/// The reduction emits with no revert through the census's path entry. The
/// corpus function did revert (report 002); its round-1 diagnostics are not
/// retained by the instrument, and this reduction does not reproduce the
/// cause — report 003 STOP 1.
#[test]
fn w6p_find_longest_match_family_reduction_emits_without_a_revert() {
    let (source, reverted, diags) = path_emission(FIND_LONGEST_MATCH_FAMILY, "flm");
    println!("W6P_FLM_SOURCE_BEGIN\n{source}\nW6P_FLM_SOURCE_END");
    assert_eq!(
        reverted, 0,
        "the family must emit without a revert: {diags:?}"
    );
}

/// binn `binn_load(data, value)` → `binn_is_valid(data, &mut (*value).type_0,
/// &mut (*value).count, &mut (*value).size)`: `value` is null-checked, so it
/// delivers as `Option<&mut binn>`, and three disjoint-field views under one
/// Option-form root are each bridged through `value.as_mut().unwrap()` — three
/// live `&mut` borrows of the Option: E0499 (report 002's confirmed revert).
const BINN_LOAD: &str = r#"
    #[repr(C)]
    pub struct binn { pub header: i32, pub type_0: i32, pub count: i32, pub size: i32, pub ptr: *mut core::ffi::c_void }
    pub unsafe fn binn_is_valid(ptr: *mut core::ffi::c_void, ptype: *mut i32, pcount: *mut i32, psize: *mut i32) -> i32 {
        if ptr.is_null() { return 0; }
        let p = ptr as *mut u8;
        *ptype = *p as i32;
        *pcount = *p.offset(1) as i32;
        *psize = *p.offset(2) as i32;
        1
    }
    pub unsafe fn binn_load(data: *mut core::ffi::c_void, value: *mut binn) -> i32 {
        if data.is_null() || value.is_null() { return 0; }
        (*value).header = 0x1f22b11f;
        if binn_is_valid(data, &mut (*value).type_0, &mut (*value).count, &mut (*value).size) == 0 {
            return 0;
        }
        (*value).ptr = data;
        1
    }
"#;

fn path_emission(source: &str, tag: &str) -> (String, usize, Vec<String>) {
    let dir = std::env::temp_dir().join(format!("crat-w6p-{tag}-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("fixture dir");
    let root = dir.join("lib.rs");
    std::fs::write(&root, source).expect("fixture file");
    let outcome = bo_rewriter::rewrite_m1_path_a5_injected(
        &root,
        A5Mode::PreciseReplay,
        Some(WholeProgramAttestation::FrozenBenchmarkGraph),
        &|_| {},
    );
    let _ = std::fs::remove_dir_all(&dir);
    match outcome {
        bo_rewriter::RewriteOutcome::Emitted {
            source,
            reverted_count,
            first_diags,
            ..
        } => (
            source,
            reverted_count,
            first_diags.iter().map(|diag| format!("{diag:?}")).collect(),
        ),
        other => panic!("{other:?}"),
    }
}

/// R412-14: the interim refusal of two certified views under one nullable
/// root is dropped. binn `binn_load`'s three disjoint-field views under the
/// `Option<&mut binn>` root certify by disjoint fields, and none of them is
/// refused for its root. This half is the lane's own obligation and holds at
/// every frame; the emission half — which additionally needs every view to be
/// decided safe — is the `#[ignore]`d witness below.
#[test]
fn w6p_option_root_multi_view_certifies_under_the_nullable_root() {
    ::utils::compilation::run_compiler_on_str(BINN_LOAD, |tcx| {
        let (table, ctx) = bo_rewriter::decide_table_with_ctx_config(tcx, precise())
            .expect("binn_load fixture decision");
        dump(tcx, &table);
        let ledger = ctx
            .a5_site_proofs
            .pair_certificates()
            .expect("certificates ride the attested index")
            .ledger();
        assert!(
            ledger
                .iter()
                .any(|row| row.outcome == Ok(CertificateKind::DisjointFields)),
            "the three views under the nullable root certify by disjoint fields: {ledger:?}"
        );
        assert!(
            ledger
                .iter()
                .all(|row| row.outcome != Err(Unproved::SiteUnresolved)
                    && row.outcome != Err(Unproved::RootsUnknown)),
            "no view under the nullable root is refused for its root: {ledger:?}"
        );
        for index in 1..4 {
            let decision = param_decision(tcx, &table, "binn_is_valid", index);
            assert!(
                !is_pair_raw_view(decision),
                "binn_is_valid#{index} must not stay pair-raw-view: {decision:?}"
            );
        }
    })
    .expect("binn_load fixture compilation");
}

/// The emission half of the same fixture: with wave-6o's per-call reborrow
/// hoist (`258c6f29`) in the frame AND all three views decided safe, the call
/// is wrapped as `({ let value = value.as_deref_mut().unwrap();
/// binn_is_valid(.., &mut (*value).type_0, ..) })` — one reborrow of the
/// Option for the whole call — and nothing reverts. GREEN on `batch-8-dry3`
/// (`991d62b3`, report 005). RED at the batch-8 landed head `08b9035e`: two of
/// the three views (`binn_is_valid::pcount`, `::psize`) are degraded
/// `kind-raw` there, so the hoist's precondition is gone and the two raw
/// bridges take `*value.as_mut().unwrap()` twice in one call (E0499). That is
/// a frame change outside this lane — the certificates above are unchanged —
/// so the witness is kept `#[ignore]`d with that typed reason rather than
/// weakened (report 006 STOP 1).
#[test]
fn w6p_option_root_multi_view_emits_with_the_hoist() {
    let (source, reverted, diags) = path_emission(BINN_LOAD, "binn-load");
    for diag in &diags {
        println!("W6P_BINN diag {diag}");
    }
    println!("W6P_BINN_SOURCE_BEGIN\n{source}\nW6P_BINN_SOURCE_END");
    assert_eq!(reverted, 0, "binn_load must not revert: {diags:?}");
    let compact: String = source.chars().filter(|c| !c.is_whitespace()).collect();
    assert!(
        compact.contains("letvalue=value.as_deref_mut().unwrap();"),
        "the Option root is reborrowed once for the call (wave-6o's hoist):\n{source}"
    );
}

/// The same three field views under a NON-nullable root (`value` never
/// null-tested, never null-assigned) keep their disjoint-fields certificate
/// and emit without a revert: `&mut value.type_0, &mut value.count,
/// &mut value.size` are disjoint borrows through one `&mut binn`.
const BINN_LOAD_PLAIN: &str = r#"
    #[repr(C)]
    pub struct binn { pub header: i32, pub type_0: i32, pub count: i32, pub size: i32, pub ptr: *mut core::ffi::c_void }
    pub unsafe fn binn_is_valid(ptr: *mut core::ffi::c_void, ptype: *mut i32, pcount: *mut i32, psize: *mut i32) -> i32 {
        if ptr.is_null() { return 0; }
        let p = ptr as *mut u8;
        *ptype = *p as i32;
        *pcount = *p.offset(1) as i32;
        *psize = *p.offset(2) as i32;
        1
    }
    pub unsafe fn binn_load(data: *mut core::ffi::c_void, value: *mut binn) -> i32 {
        if data.is_null() { return 0; }
        (*value).header = 0x1f22b11f;
        if binn_is_valid(data, &mut (*value).type_0, &mut (*value).count, &mut (*value).size) == 0 {
            return 0;
        }
        (*value).ptr = data;
        1
    }
"#;

#[test]
fn w6p_plain_root_multi_view_keeps_the_certificate_and_emits() {
    ::utils::compilation::run_compiler_on_str(BINN_LOAD_PLAIN, |tcx| {
        let (table, ctx) = bo_rewriter::decide_table_with_ctx_config(tcx, precise())
            .expect("plain binn_load fixture decision");
        dump(tcx, &table);
        let ledger = ctx
            .a5_site_proofs
            .pair_certificates()
            .expect("certificates ride the attested index")
            .ledger();
        assert!(
            ledger
                .iter()
                .any(|row| row.outcome == Ok(CertificateKind::DisjointFields)),
            "{ledger:?}"
        );
    })
    .expect("plain binn_load fixture compilation");
    let (source, reverted, diags) = path_emission(BINN_LOAD_PLAIN, "binn-load-plain");
    println!("W6P_BINN_PLAIN_SOURCE_BEGIN\n{source}\nW6P_BINN_PLAIN_SOURCE_END");
    assert_eq!(reverted, 0, "{diags:?}");
}

/// brotli `ChooseDistanceParams` → `ComputeDistanceCost(cmds, num_commands,
/// &mut orig_params.dist, &mut orig_params.dist, &mut dist_cost_0)`: the SAME
/// place passed twice as `&mut` into two SHARED formals (`*const
/// BrotliDistanceParams`). The two `&mut` borrows coerce to `&` but are still
/// two mutable borrows of one place — E0499 — and that one error's class revert
/// closed over ~260 brotli functions (report 003). With the shared-argument
/// weakening (R407-5) both arguments emit as `&(orig_params.dist)`.
const COMPUTE_DISTANCE_COST: &str = r#"
    #[repr(C)]
    pub struct Command { pub insert_len_: u32, pub copy_len_: u32, pub dist_extra_: u32, pub cmd_prefix_: u16, pub dist_prefix_: u16 }
    #[repr(C)]
    pub struct BrotliDistanceParams { pub distance_postfix_bits: u32, pub num_direct_distance_codes: u32, pub alphabet_size_max: u32, pub alphabet_size_limit: u32, pub max_distance: u64 }
    #[repr(C)]
    pub struct BrotliEncoderParams { pub quality: i32, pub dist: BrotliDistanceParams }
    pub unsafe fn ComputeDistanceCost(cmds: *const Command, num_commands: u64, orig_params: *const BrotliDistanceParams, new_params: *const BrotliDistanceParams, cost: *mut f64) -> i32 {
        let mut equal_params = 0;
        if (*orig_params).distance_postfix_bits == (*new_params).distance_postfix_bits
            && (*orig_params).num_direct_distance_codes == (*new_params).num_direct_distance_codes {
            equal_params = 1;
        }
        let mut i = 0u64;
        let mut extra_bits = 0.0f64;
        while i < num_commands {
            let cmd: *const Command = &*cmds.offset(i as isize) as *const Command;
            if (*cmd).cmd_prefix_ as i32 >= 128 {
                if equal_params == 0 && (*cmd).dist_extra_ as u64 > (*new_params).max_distance {
                    return 0;
                }
                extra_bits += (*cmd).dist_prefix_ as f64;
            }
            i += 1;
        }
        *cost = extra_bits;
        1
    }
    pub unsafe fn ChooseDistanceParams(params: *mut BrotliEncoderParams, cmds: *const Command, num_commands: u64) {
        let mut orig_params = BrotliEncoderParams { quality: (*params).quality, dist: BrotliDistanceParams { distance_postfix_bits: 0, num_direct_distance_codes: 0, alphabet_size_max: 0, alphabet_size_limit: 0, max_distance: 0 } };
        orig_params.dist = BrotliDistanceParams { distance_postfix_bits: (*params).dist.distance_postfix_bits, num_direct_distance_codes: (*params).dist.num_direct_distance_codes, alphabet_size_max: 0, alphabet_size_limit: 0, max_distance: (*params).dist.max_distance };
        let mut new_params = BrotliEncoderParams { quality: 0, dist: BrotliDistanceParams { distance_postfix_bits: 1, num_direct_distance_codes: 4, alphabet_size_max: 0, alphabet_size_limit: 0, max_distance: 1024 } };
        let mut dist_cost = 0.0f64;
        let skip = (ComputeDistanceCost(cmds, num_commands, &mut orig_params.dist, &mut new_params.dist, &mut dist_cost) == 0) as i32;
        if skip == 0 {
            (*params).dist = new_params.dist;
        }
        let mut dist_cost_0 = 0.0f64;
        ComputeDistanceCost(cmds, num_commands, &mut orig_params.dist, &mut orig_params.dist, &mut dist_cost_0);
        if dist_cost_0 < dist_cost {
            (*params).dist = orig_params.dist;
        }
    }
"#;

#[test]
fn w6p_shared_formal_takes_a_shared_borrow_of_the_place_passed_twice() {
    let (source, reverted, diags) = path_emission(COMPUTE_DISTANCE_COST, "cdc");
    for diag in &diags {
        println!("W6P_CDC diag {diag}");
    }
    println!("W6P_CDC_SOURCE_BEGIN\n{source}\nW6P_CDC_SOURCE_END");
    assert_eq!(
        reverted, 0,
        "ComputeDistanceCost must not revert: {diags:?}"
    );
    let compact: String = source.chars().filter(|c| !c.is_whitespace()).collect();
    assert!(
        compact.contains("&(orig_params.dist),&(orig_params.dist),&mutdist_cost_0"),
        "both shared formals receive the weaker borrow:\n{source}"
    );
    assert!(
        compact.contains("&(orig_params.dist),&(new_params.dist),&mutdist_cost"),
        "the distinct-place call is weakened too:\n{source}"
    );
    assert!(
        !compact.contains("&mutorig_params.dist"),
        "no `&mut` spelling survives at the shared formals:\n{source}"
    );
}

#[test]
fn w6p_debug_wave6r_held() {
    let input = r#"
#![allow(dead_code, unused_unsafe, unused_mut)]
pub struct H6 { num: i32 }
pub struct HROLLING { tag: i32 }
pub struct H65 { ha: H6, hb: HROLLING }
pub unsafe fn prepare_h6(s: *mut H6, cache: *mut i32) {
    *cache = (*s).num + (s as usize) as i32;
}
pub unsafe fn prepare_hrolling(s: *mut HROLLING, cache: *mut i32) {
    *cache += (s as usize) as i32;
}
pub unsafe fn prepare_h65(s: *mut H65, cache: *mut i32) {
    prepare_h6(&mut (*s).ha, cache);
    prepare_hrolling(&mut (*s).hb, cache);
}
"#;
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let (table, ctx) = bo_rewriter::decide_table_with_ctx_config(tcx, precise()).expect("d");
        for edit in &table.seams.edits {
            println!(
                "W6P_DBG_SEAM {} => {} #{} family={:?} text={:?} key={}",
                edit.caller_fn,
                edit.owner_fn,
                edit.param_index,
                edit.family,
                edit.replacement,
                edit.spec.template_key()
            );
        }
        let emission =
            bo_rewriter::emit_files(tcx, &table, &Default::default(), &ctx.retained_c9_plans)
                .expect("e");
        for class in emission.plan.held_classes() {
            println!(
                "W6P_DBG_HELD {} {:?}",
                tcx.def_path_str(class.local_def_id().to_def_id()),
                emission.plan.class_hold_reason(class)
            );
        }
    })
    .expect("c");
}

/// R459-4(2) PROBE — run explicitly against one corpus program:
/// `CRAT_PROBE_LIB=<lib.rs> cargo test … w6p_probe_pair_roots -- --ignored --nocapture`.
/// Reads nothing but the decision layer (no emission, no verify round) and
/// prints one `W6P_PROBE` row per recorded formal pair: the two root classes,
/// the caller-parameter index of each root when the root IS a parameter, and
/// the rule's own verdict. Report 011 §3 could not map 88 pairs to a caller
/// parameter from the source text; this asks the compiler instead.
#[test]
#[ignore = "probe: needs CRAT_PROBE_LIB and the frozen analysis cache (R459-4(2))"]
fn w6p_probe_pair_roots() {
    let path = std::env::var("CRAT_PROBE_LIB").expect("CRAT_PROBE_LIB");
    let input = std::fs::read_to_string(path).expect("probe input");
    ::utils::compilation::run_compiler_on_str(&input, |tcx| {
        let program = bo_rewriter::collect_program(tcx);
        let mut_facts =
            crate::analyses::borrow_ownership::mutability_facts::MutFacts::from_program(&program);
        let index = bo_rewriter::decision::pair_disjointness::PairDisjointnessIndex::derive(
            &program, &mut_facts, None,
        );
        let name = |did: rustc_span::def_id::LocalDefId| tcx.def_path_str(did.to_def_id());
        let rows = index.probe_rows(&program);
        println!("W6P_PROBE_ROWS {}", rows.len());
        for row in rows {
            println!(
                "W6P_PROBE\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
                name(row.caller),
                name(row.callee),
                row.left,
                row.right,
                row.left_class,
                row.right_class,
                row.left_param.map_or("-".to_owned(), |i| i.to_string()),
                row.right_param.map_or("-".to_owned(), |i| i.to_string()),
                row.outcome
            );
        }
    })
    .expect("probe compilation");
}

/// (e) + R462-1. binn's public-API shape: an exported entry takes two pointer
/// parameters and hands both to a helper. No in-crate caller can say the two
/// do not alias — the embedder supplies them — so the chain bottoms out on the
/// user's waiver, and the certificate says so in its own key.
const EXPORTED_ENTRY_PAIR: &str = r#"
    use core::ffi::c_void;
    pub unsafe fn binn_object_set_raw(obj: *mut c_void, key: *mut u8, size: u64) -> i32 {
        *(obj as *mut u8) = *key;
        size as i32
    }
    #[no_mangle]
    pub unsafe extern "C" fn binn_object_set(obj: *mut c_void, key: *mut u8, size: u64) -> i32 {
        binn_object_set_raw(obj, key, size)
    }
"#;

#[test]
fn w6p_exported_entry_pair_certifies_under_the_waiver() {
    ::utils::compilation::run_compiler_on_str(EXPORTED_ENTRY_PAIR, |tcx| {
        let program = bo_rewriter::collect_program(tcx);
        let mut_facts =
            crate::analyses::borrow_ownership::mutability_facts::MutFacts::from_program(&program);
        let index = bo_rewriter::decision::pair_disjointness::PairDisjointnessIndex::derive(
            &program, &mut_facts, None,
        );
        let function = |name: &str| {
            *program
                .functions
                .iter()
                .find(|did| tcx.item_name(did.to_def_id()).as_str() == name)
                .unwrap_or_else(|| panic!("no fn {name}"))
        };
        let outcome = index.certify_recorded(
            function("binn_object_set"),
            function("binn_object_set_raw"),
            0,
            1,
        );
        assert_eq!(
            outcome,
            Ok(CertificateKind::ExportedEntryWaiver),
            "the embedder's two arguments are waived, not proven"
        );
        assert_eq!(
            outcome.expect("waived").key(),
            "pair-disjoint:exported-entry-waiver",
            "the receipt names the waiver at every site that rests on it"
        );
    })
    .expect("exported-entry fixture compilation");
}

/// The same shape with the entry NOT exported: nothing in the program can
/// separate the two parameters, and no waiver speaks for them.
const UNEXPORTED_ENTRY_PAIR: &str = r#"
    use core::ffi::c_void;
    pub unsafe fn binn_object_set_raw(obj: *mut c_void, key: *mut u8, size: u64) -> i32 {
        *(obj as *mut u8) = *key;
        size as i32
    }
    pub unsafe fn binn_object_set(obj: *mut c_void, key: *mut u8, size: u64) -> i32 {
        binn_object_set_raw(obj, key, size)
    }
"#;

#[test]
fn w6p_unexported_entry_pair_stays_unproved() {
    ::utils::compilation::run_compiler_on_str(UNEXPORTED_ENTRY_PAIR, |tcx| {
        let program = bo_rewriter::collect_program(tcx);
        let mut_facts =
            crate::analyses::borrow_ownership::mutability_facts::MutFacts::from_program(&program);
        let index = bo_rewriter::decision::pair_disjointness::PairDisjointnessIndex::derive(
            &program, &mut_facts, None,
        );
        let function = |name: &str| {
            *program
                .functions
                .iter()
                .find(|did| tcx.item_name(did.to_def_id()).as_str() == name)
                .unwrap_or_else(|| panic!("no fn {name}"))
        };
        assert!(
            index
                .certify_recorded(
                    function("binn_object_set"),
                    function("binn_object_set_raw"),
                    0,
                    1
                )
                .is_err(),
            "the waiver speaks only for `#[no_mangle]` entries"
        );
    })
    .expect("unexported fixture compilation");
}

/// R462-1 (2): the waiver covers the external-caller edge only. An in-crate
/// caller that hands the entry the SAME place refuses the pair outright.
const EXPORTED_ENTRY_ALIASING_CALLER: &str = r#"
    use core::ffi::c_void;
    pub unsafe fn binn_object_set_raw(obj: *mut c_void, key: *mut u8, size: u64) -> i32 {
        *(obj as *mut u8) = *key;
        size as i32
    }
    #[no_mangle]
    pub unsafe extern "C" fn binn_object_set(obj: *mut c_void, key: *mut u8, size: u64) -> i32 {
        binn_object_set_raw(obj, key, size)
    }
    pub unsafe fn binn_object_set_self(buf: *mut u8, size: u64) -> i32 {
        binn_object_set(buf as *mut c_void, buf, size)
    }
"#;

#[test]
fn w6p_in_crate_aliasing_caller_refuses_the_waiver() {
    ::utils::compilation::run_compiler_on_str(EXPORTED_ENTRY_ALIASING_CALLER, |tcx| {
        let program = bo_rewriter::collect_program(tcx);
        let mut_facts =
            crate::analyses::borrow_ownership::mutability_facts::MutFacts::from_program(&program);
        let index = bo_rewriter::decision::pair_disjointness::PairDisjointnessIndex::derive(
            &program, &mut_facts, None,
        );
        let function = |name: &str| {
            *program
                .functions
                .iter()
                .find(|did| tcx.item_name(did.to_def_id()).as_str() == name)
                .unwrap_or_else(|| panic!("no fn {name}"))
        };
        assert!(
            index
                .certify_recorded(
                    function("binn_object_set"),
                    function("binn_object_set_raw"),
                    0,
                    1
                )
                .is_err(),
            "an in-crate caller passing one place twice refuses the pair, waiver or not"
        );
    })
    .expect("aliasing-caller fixture compilation");
}

/// R462-1 (2), the load-bearing form: an in-crate caller whose OWN two
/// arguments cannot be separated refuses the pair even though the callee is
/// exported. Here `binn_object_set_pair` is not exported and has no caller, so
/// nothing can separate its two parameters — and that undischarged in-crate
/// edge must sink the waiver.
const EXPORTED_ENTRY_UNDISCHARGED_CALLER: &str = r#"
    use core::ffi::c_void;
    pub unsafe fn binn_object_set_raw(obj: *mut c_void, key: *mut u8, size: u64) -> i32 {
        *(obj as *mut u8) = *key;
        size as i32
    }
    #[no_mangle]
    pub unsafe extern "C" fn binn_object_set(obj: *mut c_void, key: *mut u8, size: u64) -> i32 {
        binn_object_set_raw(obj, key, size)
    }
    pub unsafe fn binn_object_set_pair(first: *mut c_void, second: *mut u8, size: u64) -> i32 {
        binn_object_set(first, second, size)
    }
"#;

#[test]
fn w6p_undischarged_in_crate_caller_sinks_the_waiver() {
    ::utils::compilation::run_compiler_on_str(EXPORTED_ENTRY_UNDISCHARGED_CALLER, |tcx| {
        let program = bo_rewriter::collect_program(tcx);
        let mut_facts =
            crate::analyses::borrow_ownership::mutability_facts::MutFacts::from_program(&program);
        let index = bo_rewriter::decision::pair_disjointness::PairDisjointnessIndex::derive(
            &program, &mut_facts, None,
        );
        let function = |name: &str| {
            *program
                .functions
                .iter()
                .find(|did| tcx.item_name(did.to_def_id()).as_str() == name)
                .unwrap_or_else(|| panic!("no fn {name}"))
        };
        assert!(
            index
                .certify_recorded(
                    function("binn_object_set"),
                    function("binn_object_set_raw"),
                    0,
                    1
                )
                .is_err(),
            "the waiver covers the EXTERNAL edge only; an in-crate call that nothing separates refuses"
        );
    })
    .expect("undischarged-caller fixture compilation");
}

/// (e) WITHOUT the waiver: a non-exported callee whose every in-program call
/// hands it two distinct stack objects. This is the arm report 012 measured at
/// four sole-blocker rows; it rests on no assumption at all.
const PARAMETER_PAIR_PROVEN: &str = r#"
    pub unsafe fn write_two(left: *mut u32, right: *mut u32) {
        *left = *right;
    }
    pub unsafe fn caller_one() {
        let mut a: u32 = 1;
        let mut b: u32 = 2;
        write_two(&mut a, &mut b);
    }
    pub unsafe fn caller_two() {
        let mut c: u32 = 3;
        let mut d: u32 = 4;
        write_two(&mut c, &mut d);
    }
"#;

#[test]
fn w6p_parameter_pair_certifies_without_the_waiver() {
    ::utils::compilation::run_compiler_on_str(PARAMETER_PAIR_PROVEN, |tcx| {
        let program = bo_rewriter::collect_program(tcx);
        let mut_facts =
            crate::analyses::borrow_ownership::mutability_facts::MutFacts::from_program(&program);
        let index = bo_rewriter::decision::pair_disjointness::PairDisjointnessIndex::derive(
            &program, &mut_facts, None,
        );
        let function = |name: &str| {
            *program
                .functions
                .iter()
                .find(|did| tcx.item_name(did.to_def_id()).as_str() == name)
                .unwrap_or_else(|| panic!("no fn {name}"))
        };
        // The pair is separated at both call sites by rule (a), so `write_two`
        // itself is separated — which is what (e) records.
        assert_eq!(
            index
                .parameter_pair_for_tests(function("write_two"), 0, 1)
                .expect("both callers separate the pair"),
            "proven"
        );
    })
    .expect("parameter-pair fixture compilation");
}
