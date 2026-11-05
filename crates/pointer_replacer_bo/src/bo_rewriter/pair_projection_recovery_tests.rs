//! wave-6p R513-3: projection recovery through a single-definition local.
//!
//! brotli's `ReadHuffmanCode` holds two pointers into ONE object:
//!
//! ```text
//! let mut br: *mut BrotliBitReader           = &mut (*s).br;
//! let mut h:  *mut BrotliMetablockHeaderArena = &mut (*s).arena.header;
//! BrotliSafeReadBits(br, 2, &mut (*h).sub_loop_counter)
//! ```
//!
//! The two arguments are `(*s).br` and `(*s).arena.header.sub_loop_counter` —
//! disjoint fields of one object, which `disjoint_fields` certifies on sight.
//! It never saw them: the field prefix is consumed by the locals, so the
//! recorded paths root at `br` and `h` with the prefix gone, and (e) read the
//! pair as "a caller passes one formal twice".
//!
//! The rule folds a local's prefix into the `PlacePath` when the local is
//! defined EXACTLY ONCE as `&mut <place>` / `&<place>` and its own address is
//! never taken. Both conditions are load-bearing and each has a control: a
//! local written a second time may point elsewhere by the call, and a local
//! whose address is taken may be rewritten through that address.
//!
//! No new assumption rides this: `br = &mut (*s).br` makes `*br` BE `(*s).br`,
//! which is already what the input says.

/// The certificate's verdict on one recorded pair of a fixture.
fn verdict_of(
    src: &str,
    caller: &str,
    callee: &str,
    left: usize,
    right: usize,
) -> Result<
    super::decision::pair_disjointness::CertificateKind,
    super::decision::pair_disjointness::Unproved,
> {
    let mut out = None;
    ::utils::compilation::run_compiler_on_str(src, |tcx| {
        let program = super::collect_program(tcx);
        let mut_facts =
            crate::analyses::borrow_ownership::mutability_facts::MutFacts::from_program(&program);
        let index = super::decision::pair_disjointness::PairDisjointnessIndex::derive(
            &program, &mut_facts, None,
        );
        let function = |name: &str| {
            *program
                .functions
                .iter()
                .find(|did| tcx.item_name(did.to_def_id()).as_str() == name)
                .unwrap_or_else(|| panic!("no fn {name}"))
        };
        out = Some(index.certify_recorded(function(caller), function(callee), left, right));
    })
    .expect("fixture compilation");
    out.expect("the compiler callback ran")
}

const PRELUDE: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables, unused_assignments)]
#[repr(C)]
pub struct Reader { pub bits: u32, pub avail: u32 }
#[repr(C)]
pub struct Header { pub sub_loop_counter: u32, pub repeat: u32 }
#[repr(C)]
pub struct Arena { pub header: Header }
#[repr(C)]
pub struct State { pub br: Reader, pub arena: Arena }

pub unsafe fn SafeReadBits(mut br: *mut Reader, mut n: u32, mut val: *mut u32) -> i32 {
    (*br).bits = n;
    *val = (*br).avail;
    1
}
"#;

/// `ReadHuffmanCode`'s shape, to the line: one local holds `&mut (*s).br`, the
/// other `&mut (*s).arena.header`, and the call pairs the first with a field of
/// the second.
const READ_HUFFMAN_CODE: &str = r#"
pub unsafe fn ReadHuffmanCode(mut s: *mut State) -> i32 {
    let mut br: *mut Reader = &mut (*s).br;
    let mut h: *mut Header = &mut (*s).arena.header;
    SafeReadBits(br, 2, &mut (*h).sub_loop_counter)
}
"#;

/// The same object reached through two single-definition locals, both handed
/// over as bare pointer VALUES rather than one of them as `&mut place`.
const BOTH_SIDES_ARE_LOCALS: &str = r#"
pub unsafe fn BothLocals(mut s: *mut State) -> i32 {
    let mut br: *mut Reader = &mut (*s).br;
    let mut counter: *mut u32 = &mut (*s).arena.header.sub_loop_counter;
    SafeReadBits(br, 2, counter)
}
"#;

/// CONTROL for the single-definition conjunct: `br` is written a second time,
/// so by the call it may address anything. The prefix must NOT fold.
const REDEFINED_LOCAL: &str = r#"
pub unsafe fn Redefined(mut s: *mut State, mut other: *mut Reader) -> i32 {
    let mut br: *mut Reader = &mut (*s).br;
    br = other;
    SafeReadBits(br, 2, &mut (*s).arena.header.sub_loop_counter)
}
"#;

/// CONTROL for the address-not-taken conjunct: `&mut br` escapes into a callee
/// that may rewrite it, so `br`'s value is no longer its initializer's place.
const ADDRESS_TAKEN_LOCAL: &str = r#"
pub unsafe fn Retarget(mut p: *mut *mut Reader) { }
pub unsafe fn AddressTaken(mut s: *mut State) -> i32 {
    let mut br: *mut Reader = &mut (*s).br;
    Retarget(&mut br);
    SafeReadBits(br, 2, &mut (*s).arena.header.sub_loop_counter)
}
"#;

/// CONTROL: folding must not INVENT disjointness. The whole pointee of `s`
/// beside a field of it overlaps, and recovering the prefix leaves it
/// overlapping — there is no first DIFFERING field.
const WHOLE_BESIDE_FIELD: &str = r#"
#[repr(C)]
pub struct Pair { pub head: Reader, pub tail: u32 }
pub unsafe fn TakeBoth(mut whole: *mut Reader, mut n: u32, mut part: *mut u32) -> i32 {
    (*whole).bits = n;
    *part = 0;
    1
}
pub unsafe fn WholeBesideField(mut s: *mut State) -> i32 {
    let mut br: *mut Reader = &mut (*s).br;
    TakeBoth(br, 2, &mut (*br).bits)
}
"#;

fn source(body: &str) -> String {
    format!("{PRELUDE}{body}")
}

#[test]
fn w6p_read_huffman_code_shape_recovers_both_prefixes_and_separates_the_fields() {
    let verdict = verdict_of(
        &source(READ_HUFFMAN_CODE),
        "ReadHuffmanCode",
        "SafeReadBits",
        0,
        2,
    );
    assert_eq!(
        verdict,
        Ok(super::decision::pair_disjointness::CertificateKind::DisjointFields),
        "`(*s).br` and `(*s).arena.header.sub_loop_counter` are disjoint fields of one object"
    );
}

#[test]
fn w6p_two_single_definition_locals_separate_as_pointer_values() {
    let verdict = verdict_of(
        &source(BOTH_SIDES_ARE_LOCALS),
        "BothLocals",
        "SafeReadBits",
        0,
        2,
    );
    assert_eq!(
        verdict,
        Ok(super::decision::pair_disjointness::CertificateKind::DisjointFields)
    );
}

#[test]
fn w6p_a_local_written_twice_does_not_fold_its_initializer_prefix() {
    let verdict = verdict_of(&source(REDEFINED_LOCAL), "Redefined", "SafeReadBits", 0, 2);
    assert!(
        verdict.is_err(),
        "a redefined local may address anything by the call, so its prefix is not its value's: \
         got {verdict:?}"
    );
}

#[test]
fn w6p_a_local_whose_address_escapes_does_not_fold_its_initializer_prefix() {
    let verdict = verdict_of(
        &source(ADDRESS_TAKEN_LOCAL),
        "AddressTaken",
        "SafeReadBits",
        0,
        2,
    );
    assert!(
        verdict.is_err(),
        "the callee holds `&mut br` and may retarget it: got {verdict:?}"
    );
}

#[test]
fn w6p_recovering_a_prefix_never_invents_disjointness_for_a_whole_beside_its_field() {
    let verdict = verdict_of(
        &source(WHOLE_BESIDE_FIELD),
        "WholeBesideField",
        "TakeBoth",
        0,
        2,
    );
    assert!(
        !matches!(
            verdict,
            Ok(super::decision::pair_disjointness::CertificateKind::DisjointFields)
        ),
        "`(*s).br` contains `(*s).br.bits`: got {verdict:?}"
    );
}

#[test]
fn w6p_the_recovered_prefix_is_visible_in_the_ledger_receipt() {
    let mut receipt = None;
    ::utils::compilation::run_compiler_on_str(&source(READ_HUFFMAN_CODE), |tcx| {
        let program = super::collect_program(tcx);
        let mut_facts =
            crate::analyses::borrow_ownership::mutability_facts::MutFacts::from_program(&program);
        let index = super::decision::pair_disjointness::PairDisjointnessIndex::derive(
            &program, &mut_facts, None,
        );
        let function = |name: &str| {
            *program
                .functions
                .iter()
                .find(|did| tcx.item_name(did.to_def_id()).as_str() == name)
                .unwrap_or_else(|| panic!("no fn {name}"))
        };
        index.certify_recorded(function("ReadHuffmanCode"), function("SafeReadBits"), 0, 2);
        receipt = Some(
            index
                .ledger()
                .iter()
                .filter_map(|row| row.outcome.as_ref().ok().map(|kind| kind.key()))
                .collect::<Vec<_>>()
                .join(","),
        );
    })
    .expect("fixture compilation");
    let receipt = receipt.expect("the compiler callback ran");
    assert!(
        receipt.contains("disjoint-fields"),
        "the ledger names the certificate that carried it: {receipt}"
    );
}
