//! wave-6f — struct fields as references (rule W6F-1, charter relay
//! wave-6f/001).
//!
//! Fixtures are reductions of real corpus functions: ht `ht_iterator` /
//! `ht_next` (subjects `ht_iterator::table#1` = `escapes-via-field-store`,
//! `ht_next::table#3` = `place-read-pointee`), lodepng `LodePNGBitReader_init`
//! / `ensureBits9` / `inflateNoCompression` / `lodepng_inflatev` (subject
//! `LodePNGBitReader_init::data#2` = `escapes-via-field-store`, the field read
//! at offsets with its `size` sibling), and a lil-shaped thin field with a
//! null test.
//!
//! RED against the base (`30d69d95`): the two ht subjects report
//! `SilentCoercion { via: EscapesViaFieldStore }` and `PlaceReadPointee`, the
//! lodepng subject `SilentCoercion { via: EscapesViaFieldStore }`
//! (`red-probe.log` in the report's artifact directory).

use std::sync::OnceLock;

use super::{A5Mode, RewriteOutcome, WholeProgramAttestation, decision::Decision};

const HT: &str = include_str!("wave6f_fixture_ht.rs");
const LODEPNG: &str = include_str!("wave6f_fixture_lodepng.rs");
const CTX: &str = include_str!("wave6f_fixture_ctx.rs");

struct Observed {
    decisions: Vec<(String, String)>,
    /// `(struct, field, status, form, cause)` rows of the field receipt.
    /// `(struct, field, status, form, cause)` per receipt row.
    fields: Vec<(String, String, String, String, String)>,
    /// `(struct, field, bridges)` per applied row (W6F-3 receipt counts).
    bridges: Vec<(String, String, String)>,
    /// `(caller, replacement)` per planned seam edit.
    seam_edits: Vec<(String, String)>,
}

fn observe(source: &str) -> Observed {
    ::utils::compilation::run_compiler_on_str(source, |tcx| {
        let (table, ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                A5Mode::PreciseReplay,
                Some(WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .unwrap();
        let mut decisions = Vec::new();
        for (subject, decision) in &table.entries {
            decisions.push((subject.label.clone(), format!("{decision:?}")));
            println!("W6F-DECISION {} => {decision:?}", subject.label);
        }
        let receipt = table.field_transactions.receipt_tsv(tcx);
        println!("W6F-FIELDS\n{receipt}");
        println!("W6F-RETENTION\n{}", ctx.retention.to_tsv());
        for blocked in &table.seams.blocked {
            println!("W6F-BLOCKED {blocked:?}");
        }
        let seam_edits: Vec<(String, String)> = table
            .seams
            .edits
            .iter()
            .map(|edit| (edit.caller_fn.clone(), edit.replacement.clone()))
            .collect();
        for (caller, replacement) in &seam_edits {
            println!("W6F-SEAM {caller} {replacement}");
        }
        for site in &ctx.raw_boundary_sites.sites {
            println!(
                "W6F-SITE {} {:?} #{} {} shape={}",
                site.key.caller,
                site.key.callee.symbol,
                site.key.argument_index,
                site.source_site,
                site.source_shape
            );
        }
        for failure in &ctx.raw_boundary_sites.failures {
            println!(
                "W6F-SITE-FAIL {} {:?} #{} {:?}",
                failure.caller, failure.callee.symbol, failure.argument_index, failure.reason
            );
        }
        println!("W6F-DISPOSITIONS\n{}", ctx.raw_boundary.receipts_tsv());
        let rows: Vec<Vec<String>> = receipt
            .lines()
            .skip(1)
            .map(|line| line.split('\t').map(str::to_owned).collect())
            .collect();
        let fields = rows
            .iter()
            .map(|cells| {
                (
                    cells[0].clone(),
                    cells[1].clone(),
                    cells[2].clone(),
                    cells[3].clone(),
                    // cause (after the W6F-3 `bridges` column)
                    cells[9].clone(),
                )
            })
            .collect();
        let bridges = rows
            .iter()
            .filter(|cells| cells[2] == "applied")
            .map(|cells| (cells[0].clone(), cells[1].clone(), cells[8].clone()))
            .collect();
        Observed {
            decisions,
            fields,
            bridges,
            seam_edits,
        }
    })
    .unwrap()
}

fn decision_of<'a>(observed: &'a Observed, label: &str) -> &'a str {
    &observed
        .decisions
        .iter()
        .find(|(candidate, _)| candidate == label)
        .unwrap_or_else(|| panic!("subject {label}: {:?}", observed.decisions))
        .1
}

fn field_row<'a>(
    observed: &'a Observed,
    struct_name: &str,
    field: &str,
) -> &'a (String, String, String, String, String) {
    observed
        .fields
        .iter()
        .find(|row| row.0 == struct_name && row.1 == field)
        .unwrap_or_else(|| panic!("field {struct_name}.{field}: {:?}", observed.fields))
}

fn emitted_with(
    name: &str,
    source: &str,
    inject: &(dyn Fn(&mut super::decision::DecisionTable) + Sync),
) -> RewriteOutcome {
    let dir = std::env::temp_dir().join(format!("crat-wave6f-{name}-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let root = dir.join("lib.rs");
    std::fs::write(&root, source).unwrap();
    let outcome = super::rewrite_m1_path_a5_injected(
        &root,
        A5Mode::PreciseReplay,
        Some(WholeProgramAttestation::FrozenBenchmarkGraph),
        inject,
    );
    std::fs::remove_dir_all(dir).unwrap();
    match &outcome {
        RewriteOutcome::Degraded {
            reason,
            degradations,
            ..
        } => {
            println!("W6F-DEGRADED {name}: {reason}\n{degradations:?}");
        }
        RewriteOutcome::Emitted {
            source,
            emitted_count,
            reverted_count,
            degradations,
            first_diags,
            e1_reverts,
            escalated,
            ..
        } => {
            println!(
                "W6F-OUTCOME {name}: emitted={emitted_count} reverted={reverted_count} degradations={degradations:?} diags={first_diags:?} escalated={escalated:?}\nW6F-EMITTED {name}\n{source}\nW6F-END {name}"
            );
            for revert in e1_reverts {
                println!(
                    "W6F-REVERT {name}: {} {:?} {}",
                    revert.function, revert.diagnostic.message, revert.attribution
                );
            }
        }
    }
    outcome
}

fn emitted(name: &str, source: &str) -> RewriteOutcome {
    emitted_with(name, source, &|_| {})
}

fn emitted_source(outcome: &RewriteOutcome) -> (&str, usize, usize) {
    match outcome {
        RewriteOutcome::Emitted {
            source,
            emitted_count,
            reverted_count,
            ..
        } => (source, *emitted_count, *reverted_count),
        RewriteOutcome::Degraded { reason, .. } => panic!("degraded: {reason}"),
    }
}

fn ht_emitted() -> &'static RewriteOutcome {
    static AFTER: OnceLock<RewriteOutcome> = OnceLock::new();
    AFTER.get_or_init(|| emitted("ht", HT))
}

fn lodepng_emitted() -> &'static RewriteOutcome {
    static AFTER: OnceLock<RewriteOutcome> = OnceLock::new();
    AFTER.get_or_init(|| emitted("lodepng", LODEPNG))
}

fn ctx_emitted() -> &'static RewriteOutcome {
    static AFTER: OnceLock<RewriteOutcome> = OnceLock::new();
    AFTER.get_or_init(|| emitted("ctx", CTX))
}

/// Witness 1 — the thin shared field (ht `hti._table`): the stored parameter
/// and the loaded local both deliver, the struct carries one lifetime, the
/// null literal becomes `None`, the load bridges the Option to the thin local.
#[test]
fn w6f_ht_store_and_load_deliver_through_the_field() {
    let observed = observe(HT);
    assert_eq!(
        decision_of(&observed, "ht_iterator::table"),
        "Ref { mutable: false }"
    );
    assert_eq!(
        decision_of(&observed, "ht_next::table"),
        "Ref { mutable: false }"
    );
    let row = field_row(&observed, "hti", "_table");
    assert_eq!(
        (row.2.as_str(), row.3.as_str()),
        ("applied", "opt-ref-shared")
    );

    let (source, emitted_count, reverted_count) = emitted_source(ht_emitted());
    assert_eq!(reverted_count, 0);
    assert_eq!(
        emitted_count, 4,
        "ht_length, ht_iterator::table, ht_next::it, ht_next::table"
    );
    for needle in [
        "pub struct hti<'a> {",
        "pub _table: Option<&'a ht>,",
        "impl<'a> ::core::marker::Copy for hti<'a> { }",
        "impl<'a> ::core::clone::Clone for hti<'a> {",
        "fn clone(&self) -> hti<'a> {",
        "pub unsafe extern \"C\" fn ht_iterator<'a>(mut table: &'a ht) -> hti<'a> {",
        "_table: None,",
        "it._table = Some(table);",
        "pub unsafe extern \"C\" fn ht_next(mut it: &mut hti) -> bool {",
        "let mut table: &crate::ht = (*it)._table.unwrap();",
    ] {
        assert!(source.contains(needle), "missing {needle:?} in\n{source}");
    }
    assert!(
        !source.contains("*mut ht,"),
        "the raw field survived:\n{source}"
    );
}

/// Witness 2 — the fat shared field with its `size` sibling (lodepng
/// `LodePNGBitReader.data`): the stored parameter is forced to the slice form
/// the field's readers need, the caller licenses the adjacent length, the 28
/// element reads and the raw sink take the slice, and the retention the
/// callee performs is discharged by the signature's lifetime tie.
#[test]
fn w6f_lodepng_slice_field_with_size_delivers() {
    let observed = observe(LODEPNG);
    assert_eq!(
        decision_of(&observed, "LodePNGBitReader_init::data"),
        "Slice { mutable: false, uses: [] }"
    );
    let row = field_row(&observed, "LodePNGBitReader", "data");
    assert_eq!(
        (row.2.as_str(), row.3.as_str()),
        ("applied", "opt-slice-shared")
    );

    let (source, emitted_count, reverted_count) = emitted_source(lodepng_emitted());
    assert_eq!(reverted_count, 0);
    // The field's own seven subjects (10 on this stack: the yield refinement
    // lets `inflatev`'s three parameters reach `custom_inflate`, pinned by
    // the needle below); other lanes' rules add rows of their own in this
    // fixture, so the crate total is not this transaction's pin.
    assert!(emitted_count >= 10, "{emitted_count}\n{source}");
    for needle in [
        "fn inflatev(mut out: &mut u8, mut in_0: &u8,",
        "pub struct LodePNGBitReader<'a> {",
        "pub data: Option<&'a [u8]>,",
        "impl<'a> ::core::marker::Copy for LodePNGBitReader<'a> { }",
        "fn LodePNGBitReader_init<'a>(mut reader:\n        &mut LodePNGBitReader<'a>, mut data: &'a [u8], mut size: size_t)",
        "(*reader).data = Some(data);",
        "((*reader).data).unwrap()[(start.wrapping_add(0 as i32 as u64)) as\n",
        "((*reader).data).unwrap()[(bytepos) as usize..].as_ptr() as\n                *const ::std::ffi::c_void",
        "data: None,",
        "core::slice::from_raw_parts(in_0, (insize) as usize), insize);",
        "fn ensureBits9(mut reader: &mut LodePNGBitReader,",
    ] {
        assert!(source.contains(needle), "missing {needle:?} in\n{source}");
    }
    assert!(
        !source.contains("data).offset("),
        "a raw offset survived on the field:\n{source}"
    );
    assert!(
        !source.contains("FALLBACK_SLICE_EXTENT"),
        "the length is the licensed sibling, never the fallback:\n{source}"
    );
}

/// Witness 3 — a thin field with a null test and a dereference (lil-shaped):
/// `is_null` becomes `is_none`, the dereference opens the Option.
#[test]
fn w6f_thin_field_null_test_and_deref() {
    let observed = observe(CTX);
    assert_eq!(
        decision_of(&observed, "env_set_name::name"),
        "Ref { mutable: false }"
    );
    let row = field_row(&observed, "lil_env", "name");
    assert_eq!(
        (row.2.as_str(), row.3.as_str()),
        ("applied", "opt-ref-shared")
    );
    let (source, _, reverted_count) = emitted_source(ctx_emitted());
    assert_eq!(reverted_count, 0);
    for needle in [
        "pub name: Option<&'a i8>,",
        "fn env_set_name<'a>(mut env: &mut lil_env<'a>,\n    mut name: &'a i8) {",
        "(*env).name = Some(name);",
        "if ((*env).name).is_none() {",
        "return *(*env).name.unwrap();",
    ] {
        assert!(source.contains(needle), "missing {needle:?} in\n{source}");
    }
}

/// Witness 4 — a field written through stays raw (`field-mutable-held`): the
/// rule admits shared fields only this wave.
#[test]
fn w6f_mutable_field_is_held() {
    let source = HT.replace(
        "    let mut table = (*it)._table;\n",
        "    let mut table = (*it)._table;\n    (*table).length = 0;\n",
    );
    let observed = observe(&source);
    let row = field_row(&observed, "hti", "_table");
    assert_eq!(
        (row.2.as_str(), row.4.as_str()),
        ("held", "field-mutable-held")
    );
    assert!(
        decision_of(&observed, "ht_iterator::table").contains("EscapesViaFieldStore"),
        "{}",
        decision_of(&observed, "ht_iterator::table")
    );
}

/// Witness 5 — a field whose use shape the transaction cannot express (the
/// field value returned bare) is held typed, and the field moves nothing.
/// (The load local `ht_next::table` is `PlaceReadPointee` while the field
/// holds; with `c9543ff7` on the head the raw-place-value reborrow declares
/// it `&ht` from the RAW field instead — either way the field moved nothing.)
#[test]
fn w6f_unsupported_use_shape_is_held() {
    let source = format!(
        "{HT}\n#[no_mangle]\npub unsafe extern \"C\" fn ht_iter_table(mut it: *mut hti) -> *mut ht {{\n    return (*it)._table;\n}}\n"
    );
    let observed = observe(&source);
    let row = field_row(&observed, "hti", "_table");
    assert_eq!(
        (row.2.as_str(), row.4.as_str()),
        ("held", "field-transaction-incomplete:use-shape")
    );
    let table = decision_of(&observed, "ht_next::table");
    assert!(
        table == "Ref { mutable: false }" || table.contains("PlaceReadPointee"),
        "{table}"
    );
}

/// Witness 6 — the transaction is one edit region: a dependent owner reverted
/// by the verify loop withdraws the field and every site with it, so the tree
/// converges on the raw field rather than on a half-converted struct.
#[test]
fn w6f_dependent_owner_revert_withdraws_the_transaction() {
    let outcome = emitted_with("ht-revert", HT, &|table| {
        for (subject, decision) in &mut table.entries {
            if subject.label == "ht_iterator::table" {
                *decision = Decision::Degraded(super::decision::Degradation {
                    subject: subject.label.clone(),
                    site: "injected".to_owned(),
                    reason: super::decision::DegradeReason::KindRaw,
                });
            }
        }
    });
    let (source, _, reverted_count) = emitted_source(&outcome);
    assert!(
        reverted_count >= 1,
        "the injected raw store must revert its owner"
    );
    assert!(
        source.contains("pub _table: *mut ht,"),
        "the struct must return to its raw field:\n{source}"
    );
    assert!(
        !source.contains("unwrap()"),
        "the load bridge must withdraw with the field:\n{source}"
    );
    assert!(
        !source.contains("hti<'a>"),
        "the lifetime must withdraw:\n{source}"
    );
}

const QUADTREE: &str = include_str!("wave6f_fixture_quadtree.rs");

/// Witness 7 (W6F-2, `escapes-via-foreign-arg`): a subject passed to a call
/// through a FUNCTION POINTER (quadtree `quadtree_walk::root` → `descent(root)`
/// / `ascent(root)`). The indirect call is a raw seam like an extern call —
/// its argument sites are recorded, dispositioned T2 (`retention-open-boundary`,
/// the callee unknown) under the named waiver — and the escape is discharged by
/// its own receipted site, while the subject's recursive-call sites keep their
/// arm-C reborrows.
#[test]
fn w6f_indirect_call_argument_bridges_under_t2() {
    let observed = observe(QUADTREE);
    assert_eq!(
        decision_of(&observed, "quadtree_walk::root"),
        "Ref { mutable: true }"
    );
    let outcome = emitted("quadtree", QUADTREE);
    let (source, emitted_count, reverted_count) = emitted_source(&outcome);
    assert_eq!(reverted_count, 0);
    assert_eq!(emitted_count, 3);
    for needle in [
        "pub unsafe extern \"C\" fn quadtree_walk(mut root: &mut quadtree_node_t,",
        ".expect(\"non-null function pointer\")(root);",
        "quadtree_walk(&mut *(*root).nw, descent, ascent);",
    ] {
        assert!(source.contains(needle), "missing {needle:?} in\n{source}");
    }
}

const BST: &str = include_str!("wave6f_fixture_bst.rs");

/// era-5c's coming frame for bst (relay 003), stated as slot-kind overrides:
/// the two `node` fields `Owning`, the owning parameters / locals `Owning`,
/// the walkers `Ref`.
fn bst_frame() {
    use crate::analyses::borrow_ownership::SlotKind;
    super::test_model_override::set(
        "w6f-bst-frame",
        vec![
            ("node".to_owned(), 1, SlotKind::Owning),
            ("node".to_owned(), 2, SlotKind::Owning),
        ],
        vec![
            ("insert::node".to_owned(), SlotKind::Owning),
            ("deleteNode::root".to_owned(), SlotKind::Owning),
            ("newNode::temp".to_owned(), SlotKind::Owning),
            ("deleteNode::temp".to_owned(), SlotKind::Owning),
            ("deleteNode::temp_0".to_owned(), SlotKind::Owning),
            ("minValueNode::node".to_owned(), SlotKind::Ref),
            ("deleteNode::temp_1".to_owned(), SlotKind::Ref),
            ("inorder::root".to_owned(), SlotKind::Ref),
        ],
    );
}

/// Witness 8 (W6F-3, relay 003) — owned fields. Without the frame the model
/// leaves the fields Raw and the transaction holds them (RED control); under
/// the era-5c-shaped frame both `node` fields become `Option<Box<node>>`
/// with null = `None`, a fresh store `Some(..)`/moved Option, a load
/// `.as_deref()`, a move-out `.take()`, every raw consumer a receipted
/// bridge, and the C `free` untouched.
#[test]
fn w6f_bst_owned_fields_deliver_under_the_era5c_frame() {
    // RED control: the landed model has no Owning field verdict here, so the
    // fields are not candidates at all and every stored subject degrades.
    let control = observe(BST);
    assert!(control.fields.is_empty(), "{:?}", control.fields);
    assert!(decision_of(&control, "insert::node").contains("Degraded"));

    bst_frame();
    let observed = observe(BST);
    let outcome = emitted("bst", BST);
    super::test_model_override::clear();
    for field in ["left", "right"] {
        let row = field_row(&observed, "node", field);
        assert_eq!(
            (row.2.as_str(), row.3.as_str()),
            ("applied", "opt-box"),
            "{row:?}"
        );
    }
    assert_eq!(
        observed.bridges,
        vec![
            (
                "node".to_owned(),
                "left".to_owned(),
                "raw-move=3;raw-view=1;raw-store=3".to_owned()
            ),
            (
                "node".to_owned(),
                "right".to_owned(),
                "raw-move=4;raw-view=1;raw-store=4".to_owned()
            ),
        ]
    );
    // The seam sees an owned argument in its consumer's form: no glue is
    // planned over a field site (a planned glue would stack on the wrap).
    assert!(
        observed
            .seam_edits
            .iter()
            .all(|(_, replacement)| !replacement.contains(".left")
                && !replacement.contains(".right")),
        "{:?}",
        observed.seam_edits
    );
    let (source, emitted_count, reverted) = emitted_source(&outcome);
    assert_eq!((emitted_count, reverted), (1, 0), "{source}");
    let flat: String = source.split_whitespace().collect::<Vec<_>>().join(" ");
    for needle in [
        // the declaration: null = None, ABI preserved (NPO)
        "pub left: Option<Box<node>>,",
        "pub right: Option<Box<node>>,",
        // a fresh allocation is written, never dropped through raw memory
        "core::ptr::write(&raw mut (*temp).left, None);",
        // a Ref-frame walker views the child
        "inorder((*root.unwrap()).left.as_deref());",
        // a raw owning consumer receives the moved Box (receipted raw-move)
        "core::ptr::write(&raw mut (*node).left, core::ptr::NonNull::new(insert((*node).left.take().map_or(core::ptr::null_mut(), Box::into_raw), key)).map(|__p| Box::from_raw(__p.as_ptr())));",
        // the null test
        "if ((*root).left).is_none() {",
        "while !node.is_null() && !((*node).left).is_none() {",
        // a raw view for a raw-declared walker (receipted raw-view)
        "node = (*node).left.as_deref_mut().map_or(core::ptr::null_mut(), core::ptr::from_mut);",
        // a move-out into a raw owning local
        "let mut temp = (*root).right.take().map_or(core::ptr::null_mut(), Box::into_raw);",
        // the C free site is untouched
        "free(root as *mut ::std::ffi::c_void); return temp;",
    ] {
        assert!(flat.contains(needle), "missing {needle:?} in\n{source}");
    }
    // A struct owning a Box is not Copy: the derives are withdrawn.
    assert!(
        !source.contains("impl ::core::marker::Copy for node"),
        "{source}"
    );
    assert!(
        !source.contains("impl ::core::clone::Clone for node"),
        "{source}"
    );
}

/// wave-6s2's pin (tulipindicators `fuzzer::check_output::options#4`,
/// relay wave-6f/005 §2): the indirect callee `start: fn(*const f64) -> i32`
/// returns no pointer and has no writable carrier, so it cannot hand a child
/// of the argument back; the slice delivers and the indirect site takes the
/// raw view `options.as_ptr()` under T2.
const CHECK_OUTPUT: &str = r#"
 #![allow(dead_code, unused_mut, unused_variables, non_camel_case_types)]
 #[repr(C)] pub struct ti_indicator_info { pub start: Option<unsafe extern "C" fn(*const f64) -> i32>, pub options: i32 }
 pub unsafe extern "C" fn check_output(mut info: *const ti_indicator_info, mut size: i32, mut options: *const f64) -> i32 {
    let mut s: i32 = 0;
    s = (*info).start.expect("non-null function pointer")(options);
    let mut k: i32 = 0;
    let mut acc: f64 = 0.0;
    while k < (*info).options { acc += *options.offset(k as isize); k += 1; }
    s + acc as i32
 }
"#;

/// Witness 9 (W6F-2 refinement, R407-8 §2): an indirect callee's yield
/// verdict is read from the function-pointer SIGNATURE — the same predicate
/// the direct arm applies to a definition — instead of defaulting to "may
/// yield". Control: a pointer-returning function pointer keeps the hold.
#[test]
fn w6f_indirect_callee_yield_is_read_from_the_signature() {
    let observed = observe(CHECK_OUTPUT);
    for (label, decision) in &observed.decisions {
        println!("W6F-CHECK-OUTPUT {label} => {decision}");
    }
    let outcome = emitted("check-output", CHECK_OUTPUT);
    let (source, emitted_count, reverted_count) = emitted_source(&outcome);
    // `info` (a shared reference) and `options` (the slice).
    assert_eq!((emitted_count, reverted_count), (2, 0), "{source}");
    assert!(source.contains("mut options: &[f64]"), "{source}");
    let flat: String = source.split_whitespace().collect::<Vec<_>>().join(" ");
    assert!(
        flat.contains("(*info).start.expect(\"non-null function pointer\")(options.as_ptr());"),
        "{source}"
    );
    assert!(flat.contains("acc += options[(k) as usize];"), "{source}");

    // Control: `child: fn(*const u8) -> *mut u8` may hand a child back.
    let control = CHECK_OUTPUT
        .replace("fn(*const f64) -> i32", "fn(*const f64) -> *mut f64")
        .replace(
            "s = (*info).start.expect(\"non-null function pointer\")(options);",
            "s = *(*info).start.expect(\"non-null function pointer\")(options) as i32;",
        );
    let held = observe(&control);
    assert!(
        decision_of(&held, "check_output::options").contains("Degraded"),
        "{}",
        decision_of(&held, "check_output::options")
    );
}

const H35: &str = include_str!("wave6f_fixture_h35.rs");

/// Witness 10 (E, R407-8 §4): the brotli `H35.params` shape. RED control:
/// with the `ref mut fresh` idiom refused the field holds. GREEN: the c2rust
/// store idiom `let ref mut fresh = (*s).f; *fresh = v;` is the field's
/// store site (kept verbatim — `fresh` reborrows the converted place); the
/// field at a local callee's `&T` parameter is an identity seam (no `&*`);
/// the storing signature AND the caller that forwards its own parameter into
/// the tied position carry the lifetime (`HasherSetupH35<'a>`).
#[test]
fn w6f_h35_ref_mut_store_idiom_and_field_argument_deliver() {
    let observed = observe(H35);
    let row = field_row(&observed, "H35", "params");
    assert_eq!(
        (row.2.as_str(), row.3.as_str()),
        ("applied", "ref-shared"),
        "{row:?}"
    );
    for label in [
        "InitializeH35::params",
        "HashMemAllocInBytesH35::params",
        "HasherSetupH35::params",
    ] {
        assert_eq!(
            decision_of(&observed, label),
            "Ref { mutable: false }",
            "{label}"
        );
    }
    let outcome = emitted("h35", H35);
    let (source, emitted_count, reverted) = emitted_source(&outcome);
    assert_eq!((emitted_count, reverted), (6, 0), "{source}");
    let flat: String = source.split_whitespace().collect::<Vec<_>>().join(" ");
    for needle in [
        "pub struct H35<'a> { pub fresh: i32, pub params: &'a BrotliEncoderParams, }",
        "fn InitializeH35<'a>(mut self_0: &mut H35<'a>, mut params: &'a BrotliEncoderParams) {",
        "let ref mut fresh15 = (*self_0).params; *fresh15 = params;",
        "fn PrepareH35(mut self_0: &H35, mut one_shot: i32, mut input_size: size_t) -> size_t { return HashMemAllocInBytesH35((*self_0).params, one_shot, input_size); }",
        "fn HasherSetupH35<'a>(mut h: &mut H35<'a>, mut params: &'a BrotliEncoderParams, mut input_size: size_t) -> size_t { InitializeH35(h, params);",
    ] {
        assert!(flat.contains(needle), "missing {needle:?} in\n{source}");
    }

    // A nullable field (`Option<&'a T>`) at the same `&T` parameter is glued
    // by the seam (`.unwrap()`), the null store is `None`.
    let nullable = H35.replace(
        "unsafe extern \"C\" fn PrepareH35(",
        "unsafe extern \"C\" fn ResetH35(mut self_0: *mut H35) {\n    let ref mut fresh16 = (*self_0).params;\n    *fresh16 = 0 as *const BrotliEncoderParams;\n}\nunsafe extern \"C\" fn PrepareH35(",
    );
    let observed = observe(&nullable);
    let row = field_row(&observed, "H35", "params");
    assert_eq!(
        (row.2.as_str(), row.3.as_str()),
        ("applied", "opt-ref-shared"),
        "{row:?}"
    );
    let outcome = emitted("h35-nullable", &nullable);
    let (source, emitted_count, reverted) = emitted_source(&outcome);
    assert_eq!((emitted_count, reverted), (7, 0), "{source}");
    let flat: String = source.split_whitespace().collect::<Vec<_>>().join(" ");
    for needle in [
        "pub params: Option<&'a BrotliEncoderParams>,",
        "let ref mut fresh16 = (*self_0).params; *fresh16 = None;",
        "let ref mut fresh15 = (*self_0).params; *fresh15 = Some(params);",
        "HashMemAllocInBytesH35((*self_0).params.unwrap(), one_shot, input_size);",
    ] {
        assert!(flat.contains(needle), "missing {needle:?} in\n{source}");
    }
}

const BLOCK_ENCODER: &str = include_str!("wave6f_fixture_block_encoder.rs");

/// Witness 11 (E): brotli `BlockEncoder` — TWO reference fields of one
/// struct share its one generated lifetime (`block_types_`, `block_lengths_`;
/// the one-field-per-struct hold is lifted); a field handed to a
/// slice-walking callee is fat by Foster's `Arr` fact even without its own
/// element read (`block_lengths_` is only ever passed on), so nothing thin is
/// widened at the callee; both stores are the `ref mut fresh` idiom.
#[test]
fn w6f_block_encoder_two_fields_share_the_lifetime_and_walkers_take_slices() {
    let observed = observe(BLOCK_ENCODER);
    for (field, form) in [
        ("block_types_", "opt-slice-shared"),
        ("block_lengths_", "opt-slice-shared"),
    ] {
        let row = field_row(&observed, "BlockEncoder", field);
        assert_eq!(
            (row.2.as_str(), row.3.as_str()),
            ("applied", form),
            "{row:?}"
        );
    }
    let outcome = emitted("block-encoder", BLOCK_ENCODER);
    let (source, emitted_count, reverted) = emitted_source(&outcome);
    assert_eq!((emitted_count, reverted), (9, 0), "{source}");
    let flat: String = source.split_whitespace().collect::<Vec<_>>().join(" ");
    for needle in [
        "pub struct BlockEncoder<'a> { pub histogram_length_: size_t, pub num_block_types_: size_t, pub block_types_: Option<&'a [u8]>, pub block_lengths_: Option<&'a [u32]>, pub num_blocks_: size_t, }",
        "fn InitBlockEncoder<'a>(mut self_0: &mut BlockEncoder<'a>, mut histogram_length: size_t, mut num_block_types: size_t, mut block_types: &'a [u8], mut block_lengths: &'a [u32], num_blocks: size_t) {",
        "let ref mut fresh10 = (*self_0).block_types_; *fresh10 = Some(block_types); let ref mut fresh11 = (*self_0).block_lengths_; *fresh11 = Some(block_lengths);",
        "return BuildAndStoreBlockSplitCode((*self_0).block_types_.unwrap(), (*self_0).block_lengths_.unwrap(), (*self_0).num_blocks_);",
        "let mut block_type = ((*self_0).block_types_).unwrap()[(block_ix) as usize];",
        "block_types_: None, block_lengths_: None,",
    ] {
        assert!(flat.contains(needle), "missing {needle:?} in\n{source}");
    }
}

const HOIST: &str = include_str!("wave6f_fixture_hoist.rs");

/// era-5c's E5C-3 shape (relay 006 §1): the store's value is a call whose
/// moving argument (`.take()` of the field) invalidates a view a LATER
/// argument reads through (`(*temp).key`, `temp` a reference into the
/// moved subtree). Frame: fields Owning; `removeMin::root` a `&mut` view,
/// `removeMin::temp` a reference; `deleteNode` stays raw at this frame.
fn hoist_frame() {
    use crate::analyses::borrow_ownership::SlotKind;
    super::test_model_override::set(
        "w6f-hoist-frame",
        vec![
            ("node".to_owned(), 1, SlotKind::Owning),
            ("node".to_owned(), 2, SlotKind::Owning),
        ],
        vec![
            ("deleteNode::root".to_owned(), SlotKind::Owning),
            ("deleteNode::temp".to_owned(), SlotKind::Owning),
            ("removeMin::root".to_owned(), SlotKind::Ref),
            ("removeMin::temp".to_owned(), SlotKind::Ref),
        ],
    );
}

/// Witness 12 (E5C-3, relay 006 §1): the store's value is a call whose
/// moving argument (`.take()` of the field) invalidates the view a LATER
/// argument reads through; the pure `Copy` read is hoisted before the
/// statement (`let __crat_hoist0 = (*temp).key;`), the same value as in
/// place (a move relocates a pointer, it writes nothing the read observes),
/// so the checker accepts what was E0502 without it.
#[test]
fn w6f_hoist_pure_read_before_a_moving_argument() {
    hoist_frame();
    let observed = observe(HOIST);
    let outcome = emitted("hoist", HOIST);
    super::test_model_override::clear();
    for field in ["left", "right"] {
        let row = field_row(&observed, "node", field);
        assert_eq!(
            (row.2.as_str(), row.3.as_str()),
            ("applied", "opt-box"),
            "{row:?}"
        );
    }
    let (source, emitted_count, reverted) = emitted_source(&outcome);
    assert_eq!((emitted_count, reverted), (2, 0), "{source}");
    let flat: String = source.split_whitespace().collect::<Vec<_>>().join(" ");
    for needle in [
        "pub unsafe extern \"C\" fn removeMin(mut root: &mut node) { let mut temp: &crate::node = (*root).right.as_deref().unwrap(); (*root).key = (*temp).key; let __crat_hoist0 = (*temp).key; (*root).right = core::ptr::NonNull::new(deleteNode((*root).right.take().map_or(core::ptr::null_mut(), Box::into_raw), __crat_hoist0)).map(|__p| Box::from_raw(__p.as_ptr())); }",
        // a bare local read (`key`) is not hoisted — nothing a move invalidates
        "deleteNode((*root).left.take().map_or(core::ptr::null_mut(), Box::into_raw), key)",
    ] {
        assert!(flat.contains(needle), "missing {needle:?} in\n{source}");
    }
    assert_eq!(flat.matches("__crat_hoist").count(), 2, "{source}");
}
