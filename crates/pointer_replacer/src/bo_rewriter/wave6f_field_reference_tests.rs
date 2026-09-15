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
    fields: Vec<(String, String, String, String, String)>,
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
        let fields = receipt
            .lines()
            .skip(1)
            .map(|line| {
                let cells: Vec<&str> = line.split('\t').collect();
                (
                    cells[0].to_owned(),
                    cells[1].to_owned(),
                    cells[2].to_owned(),
                    cells[3].to_owned(),
                    cells[8].to_owned(),
                )
            })
            .collect();
        Observed { decisions, fields }
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
    assert_eq!(emitted_count, 7);
    for needle in [
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
/// field value returned bare) is held typed, and nothing moves.
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
    assert!(decision_of(&observed, "ht_next::table").contains("PlaceReadPointee"));
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
