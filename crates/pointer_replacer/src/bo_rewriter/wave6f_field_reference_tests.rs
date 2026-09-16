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
    /// E5C-3 local-move hoist plans (on the model).
    local_move_hoists: usize,
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
            local_move_hoists: table.field_transactions.local_move_hoists.len(),
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
    // Nothing of the field's reverts. On the batch-8 composition the one
    // revert is `lodepng_memcpy::dst` — wave-6v's counted-void view of the
    // memcpy call YIELDS (R410-2(d)) where an A5 raw-view snapshot already
    // replaced that call for `src` (`38f836cb`), and the dst class pays at
    // the compile gate; the field's sites in that call are untouched.
    let reverted_names: Vec<&str> = match lodepng_emitted() {
        RewriteOutcome::Emitted { degradations, .. } => degradations
            .iter()
            .filter(|d| format!("{:?}", d.reason).contains("RevertedAfterVerifyFailure"))
            .map(|d| d.subject.as_str())
            .collect(),
        RewriteOutcome::Degraded { .. } => Vec::new(),
    };
    assert!(
        reverted_count == 0 || (reverted_count == 1 && reverted_names == ["lodepng_memcpy::dst#1"]),
        "{reverted_count} reverted {reverted_names:?}\n{source}"
    );
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
        "fn ensureBits9(mut reader: &mut LodePNGBitReader,",
    ] {
        // The pins are of the emitted FORM, not of its line breaks: a
        // composition that nests the argument deeper (a counted-void twin, an
        // A5 raw view) re-wraps the same text. Compare whitespace-flattened.
        let flat: String = source.split_whitespace().collect::<Vec<_>>().join(" ");
        let needle: String = needle.split_whitespace().collect::<Vec<_>>().join(" ");
        assert!(flat.contains(&needle), "missing {needle:?} in\n{source}");
    }
    // The store's slice at the raw caller `lodepng_inflatev`: ruling B's
    // adjacency licenses `insize` where the head takes the bare adjacency;
    // under R408-1 (an adjacent integer is a length only with count
    // evidence, which a field-stored parameter has none of) the construction
    // carries the addendum-77 fabricated extent with its receipt. Either
    // way the field delivers; the length arm is the seam's, not this
    // transaction's.
    // R411 §2: the count companion — `LodePNGBitReader_init(reader, data,
    // size)` stores `size` into the sibling that bounds `data`'s reads
    // (`start + 1 < size`), so parameter 2 is parameter 1's count; with the
    // companion the raw caller's construction is the exact `insize` on every
    // head (bare adjacency without R408-1, the companion under it).
    assert!(
        observed
            .bridges
            .iter()
            .any(|(_, field, receipt)| field == "data"
                && receipt.contains("count-companion=LodePNGBitReader_init:1<-2(size)")),
        "{:?}",
        observed.bridges
    );
    assert!(
        source.contains("core::slice::from_raw_parts(in_0, (insize) as usize), insize);"),
        "{source}"
    );
    assert!(
        !source.contains("data).offset("),
        "a raw offset survived on the field:\n{source}"
    );
    // Control: without the bound (`size` no longer compared against the
    // reads' indices) the sibling store alone names no count.
    let unbounded = LODEPNG
        .replace(
            "if start.wrapping_add(1 as u32 as u64) < size {",
            "if start.wrapping_add(1 as u32 as u64) < 4096 {",
        )
        .replace(
            "if start.wrapping_add(0 as i32 as u64) < size {",
            "if start.wrapping_add(0 as i32 as u64) < 4096 {",
        )
        .replace(
            "if bytepos.wrapping_add(4 as i32 as u64) >= size { return 52 as i32 as u32; }",
            "if bytepos.wrapping_add(4 as i32 as u64) >= 4096 { return 52 as i32 as u32; }",
        );
    let control = observe(&unbounded);
    assert!(
        control
            .bridges
            .iter()
            .any(|(_, field, receipt)| field == "data" && receipt.ends_with("count-companion=")),
        "{:?}",
        control.bridges
    );
    // The field's own store fabricates nothing: `Some(data)` carries the
    // parameter's slice as it arrived (pinned above); a fabricated extent, if
    // any, is the caller's seam construction, receipted there.
    assert!(
        !source.contains("(*reader).data = Some(core::slice::from_raw_parts"),
        "the field store fabricated a length:\n{source}"
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

/// The frame override is process-global; every test that sets it holds
/// this lock for its whole run so a concurrent test cannot clear it.
fn frame_lock() -> std::sync::MutexGuard<'static, ()> {
    static LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());
    LOCK.lock().unwrap_or_else(|poisoned| poisoned.into_inner())
}

const BST: &str = include_str!("wave6f_fixture_bst.rs");

/// era-5c's bst frame (report era-5c/002 §5, the full solve under E5C-3:
/// 0 raw / 13 ref / 31 owning), stated as slot-kind overrides by subject
/// name. The MIR locals of that report map to these subjects: both `node`
/// fields (`field1@d0` / `field2@d0`) Owning; `insert::_1` (`node`),
/// `newNode::_0` (`temp`), `deleteNode::_1` (`root`) and its `temp` /
/// `temp_0` Owning; the Ref list `minValueNode::_1` (`node`),
/// `deleteNode::_36` (`temp_1`, the `minValueNode` receiver) and
/// `inorder::_1` (`root`). `deleteNode::_37` (the traversal ARGUMENT
/// `(*root).right`, Owning) is a field site, not a named subject — the
/// `.take()` move; `minValueNode::_8` and `inorder::_5/_13` are unnamed
/// temporaries. Re-pinned 2026-09-16 against 002; era-5c 003 (R425-2)
/// confirms the corpus entry IS this shape (0 raw / 13 ref / 31 owning), so
/// the frame stands as the corpus's own.
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
    let _frame = frame_lock();
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
                "raw-move=3;raw-view=1;raw-store=3;dealloc-transfer=0;allocator-contract=0;waiver-drop-scope-exit=0;count-companion=".to_owned()
            ),
            (
                "node".to_owned(),
                "right".to_owned(),
                "raw-move=4;raw-view=1;raw-store=4;dealloc-transfer=0;allocator-contract=0;waiver-drop-scope-exit=0;count-companion=".to_owned()
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
        // R425-2: the recursive walker's two arguments are VIEWS of the
        // children, not moves — the callee formal stays `ref`
        "inorder((*root.unwrap()).right.as_deref());",
        // R425-2: the `minValueNode` receiver is a raw view of the child
        "minValueNode((*root).right.as_deref_mut().map_or(core::ptr::null_mut(), core::ptr::from_mut))",
        // E5C-3 (report 007): the two-children branch hoists the pure read
        // before the moving argument
        "let __crat_hoist0 = (*temp_1).key;",
    ] {
        assert!(flat.contains(needle), "missing {needle:?} in\n{source}");
    }
    // R425-2 (era-5c 003) — the E5C-3 emission contract's SECOND clause:
    // the four Owning kinds at the traversal / recursive-call arguments
    // (`deleteNode::_37`, `minValueNode::_8`, `inorder::_5/_13`) are token
    // loads whose callee formals stay `ref`, so they license NO drop. bst's
    // only deallocation sites are `deleteNode`'s two C `free`s, both
    // RETAINED; a `Box` dropped at one of those argument sites would free a
    // linked subtree. Emission side: no Rust drop anywhere, the two frees
    // exactly as C wrote them (the bridges row's
    // `waiver-drop-scope-exit=0` is the receipt side of the same clause).
    assert_eq!(source.matches("drop(").count(), 0, "{source}");
    assert_eq!(
        source
            .matches("free(root as *mut ::std::ffi::c_void);")
            .count(),
        2,
        "{source}"
    );
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
    let _frame = frame_lock();
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

const MOVE_LOCAL: &str = include_str!("wave6f_fixture_move_local.rs");

/// Witness 13 (relay 008 §2, R410 STOP 1 = YES): E5C-3 over a moving owned
/// LOCAL — C1's `consume(p, *p)`. The plan is made on the model (`producer::p`
/// Owning at `consume::p` Owning; the later argument `*p` a pure `Copy` read
/// through the moved local); the hoist is EMITTED only while `producer::p`
/// delivers as a `Box`: on a head with wave-6a's C1 Box-parameter chain the
/// tree is `let __crat_hoist0 = *p; return consume(p, __crat_hoist0);`
/// (E0382 without it); on a head where the local stays raw nothing is
/// hoisted — a raw local moves nothing the checker sees.
#[test]
fn w6f_hoist_pure_read_before_a_moving_owned_local() {
    let _frame = frame_lock();
    use crate::analyses::borrow_ownership::SlotKind;
    super::test_model_override::set(
        "w6f-move-local-frame",
        vec![],
        vec![
            ("producer::p".to_owned(), SlotKind::Owning),
            ("consume::p".to_owned(), SlotKind::Owning),
        ],
    );
    let observed = observe(MOVE_LOCAL);
    let outcome = emitted("move-local", MOVE_LOCAL);
    super::test_model_override::clear();
    assert_eq!(observed.local_move_hoists, 1, "{:?}", observed.decisions);
    let (source, _, reverted) = emitted_source(&outcome);
    assert_eq!(reverted, 0, "{source}");
    let flat: String = source.split_whitespace().collect::<Vec<_>>().join(" ");
    println!("W6F-MOVE-LOCAL-SOURCE\n{source}");
    if decision_of(&observed, "producer::p").starts_with("Box") {
        assert!(
            flat.contains("let __crat_hoist0 = *p; return consume(p, __crat_hoist0);"),
            "{source}"
        );
    } else {
        assert!(!flat.contains("__crat_hoist"), "{source}");
        assert!(flat.contains("return consume(p, *p);"), "{source}");
    }
}

const RING_BUFFER: &str = include_str!("wave6f_fixture_ring_buffer.rs");

fn ring_buffer_frame() {
    use crate::analyses::borrow_ownership::SlotKind;
    super::test_model_override::set(
        "w6f-ring-buffer-frame",
        vec![("RingBuffer".to_owned(), 1, SlotKind::Owning)],
        vec![(
            "RingBufferInitBuffer::new_data".to_owned(),
            SlotKind::Owning,
        )],
    );
}

/// Witness 16 (relay 007, R409-3; the RingBuffer shape, spelled as the
/// substrate of record spells it — `(*rb).data_ = new_data;`, R416-12): a FAT
/// owned field `Option<Box<[u8]>>` — at this frame the store from a raw thin
/// local (`new_data = malloc(..) as *mut u8`) carries no
/// length, so the field holds typed; on a head where `new_data` delivers as
/// a `Box<[u8]>` the store is the moved Option and the free site is the
/// transfer.
#[test]
fn w6f_ring_buffer_fat_owned_field_store_needs_a_length_or_a_boxed_source() {
    let _frame = frame_lock();
    ring_buffer_frame();
    let observed = observe(RING_BUFFER);
    let outcome = emitted("ring-buffer", RING_BUFFER);
    super::test_model_override::clear();
    let row = field_row(&observed, "RingBuffer", "data_");
    let source_boxed = decision_of(&observed, "RingBufferInitBuffer::new_data").starts_with("Box");
    let (source, _, reverted) = emitted_source(&outcome);
    assert_eq!(reverted, 0, "{source}");
    if source_boxed {
        assert_eq!(
            (row.2.as_str(), row.3.as_str()),
            ("applied", "opt-box-slice"),
            "{row:?}"
        );
        let flat: String = source.split_whitespace().collect::<Vec<_>>().join(" ");
        for needle in [
            "pub data_: Option<Box<[u8]>>,",
            "free((*rb).data_.take().map_or(core::ptr::null_mut(), |__b| Box::into_raw(__b) as *mut ::std::ffi::c_void));",
            "(*rb).data_.as_deref().map_or(core::ptr::null(), |__s| __s.as_ptr()) as *const ::std::ffi::c_void",
            "(*rb).buffer_ = (*rb).data_.as_deref_mut().map_or(core::ptr::null_mut(), |__s| __s.as_mut_ptr()).offset(2 as isize);",
            "return (*rb).data_.as_deref().unwrap()[(i) as usize];",
        ] {
            assert!(flat.contains(needle), "missing {needle:?} in\n{source}");
        }
    } else {
        assert_eq!(
            (row.2.as_str(), row.4.as_str()),
            (
                "held",
                "field-transaction-incomplete:owned-slice-store-length"
            ),
            "{row:?}"
        );
        assert!(source.contains("pub data_: *mut u8,"), "{source}");
    }
}

const SLOT: &str = include_str!("wave6f_fixture_slot.rs");

/// Witness 14 (relay 007 / wave-6a 006 §2): a THIN owned field's C free
/// site through libc `free` takes the allocation (`take()` + `Box::into_raw`,
/// the call kept), a foreign `memcpy` gets the raw view, the deref read the
/// shared view, the null test `is_none()`, and every store through the raw
/// base is `ptr::write`; the by-value `Holder` in `drive` is a scope exit
/// the language drops — addendum 101's `waiver-drop(scope-exit)`, receipted.
#[test]
fn w6f_thin_owned_field_free_site_transfers_and_memcpy_takes_a_raw_view() {
    let _frame = frame_lock();
    use crate::analyses::borrow_ownership::SlotKind;
    super::test_model_override::set(
        "w6f-slot-frame",
        vec![("Holder".to_owned(), 1, SlotKind::Owning)],
        vec![("HolderFill::fresh".to_owned(), SlotKind::Owning)],
    );
    let observed = observe(SLOT);
    let outcome = emitted("slot", SLOT);
    super::test_model_override::clear();
    let row = field_row(&observed, "Holder", "slot_");
    assert_eq!(
        (row.2.as_str(), row.3.as_str()),
        ("applied", "opt-box"),
        "{row:?}"
    );
    assert_eq!(
        observed.bridges,
        vec![(
            "Holder".to_owned(),
            "slot_".to_owned(),
            "raw-move=0;raw-view=1;raw-store=2;dealloc-transfer=1;allocator-contract=0;waiver-drop-scope-exit=1;count-companion=".to_owned()
        )]
    );
    let (source, emitted_count, reverted) = emitted_source(&outcome);
    assert_eq!((emitted_count, reverted), (1, 0), "{source}");
    let flat: String = source.split_whitespace().collect::<Vec<_>>().join(" ");
    for needle in [
        "pub slot_: Option<Box<i32>>,",
        "free((*h).slot_.take().map_or(core::ptr::null_mut(), |__b| Box::into_raw(__b) as *mut ::std::ffi::c_void));",
        "core::ptr::write(&raw mut *fresh1, None);",
        "if !((*h).slot_).is_none() {",
        "(*h).slot_.as_deref().map_or(core::ptr::null(), core::ptr::from_ref) as *const ::std::ffi::c_void,",
        "core::ptr::write(&raw mut *fresh2, core::ptr::NonNull::new(fresh).map(|__p| Box::from_raw(__p.as_ptr())));",
        "return *(*h).slot_.as_deref().unwrap();",
        "let mut h = Holder { count: 0, slot_: None };",
    ] {
        assert!(flat.contains(needle), "missing {needle:?} in\n{source}");
    }
}

const SLOT_CONTRACT: &str = include_str!("wave6f_fixture_slot_contract.rs");

/// Witness 15 (R409-3, the allocator contract): the free site through a
/// contract deallocator (`CustomFree(m, p)`, freeing through the manager's
/// `free_func` — not source-provable, named by the frame's contract) is the
/// same transfer with the `allocator-contract` receipt; the container lives
/// on the heap (freed raw), so no Rust drop can reach the field. Control:
/// a by-value instance of the struct is a scope exit the language would
/// drop — `contract-allocation:implicit-close`, a typed hold.
#[test]
fn w6f_contract_deallocator_transfers_and_a_value_instance_holds() {
    let _frame = frame_lock();
    use crate::analyses::borrow_ownership::SlotKind;
    let frame = || {
        super::test_model_override::set_with_contract(
            "w6f-slot-contract-frame",
            vec![("Holder".to_owned(), 1, SlotKind::Owning)],
            vec![("HolderFill::fresh".to_owned(), SlotKind::Owning)],
            vec![("CustomFree".to_owned(), 1)],
        )
    };
    frame();
    let observed = observe(SLOT_CONTRACT);
    let outcome = emitted("slot-contract", SLOT_CONTRACT);
    super::test_model_override::clear();
    let row = field_row(&observed, "Holder", "slot_");
    assert_eq!(
        (row.2.as_str(), row.3.as_str()),
        ("applied", "opt-box"),
        "{row:?}"
    );
    assert!(
        observed.bridges[0]
            .2
            .contains("dealloc-transfer=1;allocator-contract=1;waiver-drop-scope-exit=0"),
        "{:?}",
        observed.bridges
    );
    let (source, _, reverted) = emitted_source(&outcome);
    assert_eq!(reverted, 0, "{source}");
    let flat: String = source.split_whitespace().collect::<Vec<_>>().join(" ");
    assert!(
        flat.contains("CustomFree(m, (*h).slot_.take().map_or(core::ptr::null_mut(), |__b| Box::into_raw(__b) as *mut ::std::ffi::c_void));"),
        "{source}"
    );

    // Control: a by-value instance.
    let by_value = SLOT_CONTRACT.replace(
        "    let mut h = HolderNew();",
        "    let mut hv = Holder { count: 0, slot_: 0 as *mut i32 };\n    let mut h = HolderNew();",
    );
    frame();
    let held = observe(&by_value);
    super::test_model_override::clear();
    let row = field_row(&held, "Holder", "slot_");
    assert_eq!(
        (row.2.as_str(), row.4.as_str()),
        ("held", "contract-allocation:implicit-close"),
        "{row:?}"
    );
}

const TULIP_ARRAYS: &str = include_str!("wave6f_fixture_tulip_arrays.rs");

/// Witness 20 (relay 023 §3, build 1) — the census's eleven
/// `array-local-incomplete:initializer` rows are tulip's element LISTS, the
/// substrate's other spelling of the same array. A list whose elements are
/// all the null literal is the repeat form written out: it is admitted and
/// renders `[None; N]`, so the array reaches its next gate — here the whole
/// array handed to a callee (`inputs.as_ptr()`), `array-use-shape`, which is
/// the next build. A list with a VALUE element is a different family (each
/// element is a store whose source must deliver) and holds under its own
/// reason, `initializer-element-source`, instead of the blanket one.
#[test]
fn w6f_tulip_element_list_initializers_split_by_their_elements() {
    let observed = observe(TULIP_ARRAYS);
    let null_list = field_row(&observed, "stress", "inputs");
    assert_eq!(
        (null_list.2.as_str(), null_list.4.as_str()),
        ("held", "array-local-incomplete:array-use-shape"),
        "{null_list:?}"
    );
    let value_list = field_row(&observed, "main_0", "all_inputs");
    assert_eq!(
        (value_list.2.as_str(), value_list.4.as_str()),
        ("held", "array-local-incomplete:initializer-element-source"),
        "{value_list:?}"
    );
    // A zero-length array has no element to convert: `[]` is not the null
    // initializer, it is nothing, and the transaction stays out of it.
    let empty = field_row(&observed, "empty_0", "none_at_all");
    assert_eq!(
        (empty.2.as_str(), empty.4.as_str()),
        ("held", "array-local-incomplete:initializer-element-source"),
        "{empty:?}"
    );
}

const AVL: &str = include_str!("wave6f_fixture_avl.rs");

/// era-5c-shaped frame for avl (the rotation family, relay 003 §2): both
/// `Node` pointer fields Owning, the rotation's owners Owning, the readers
/// Ref.
fn avl_frame() {
    use crate::analyses::borrow_ownership::SlotKind;
    super::test_model_override::set(
        "w6f-avl-frame",
        vec![
            ("Node".to_owned(), 1, SlotKind::Owning),
            ("Node".to_owned(), 2, SlotKind::Owning),
        ],
        vec![
            ("newNode::node".to_owned(), SlotKind::Owning),
            ("rightRotate::y".to_owned(), SlotKind::Owning),
            ("rightRotate::x".to_owned(), SlotKind::Owning),
            ("rightRotate::T2".to_owned(), SlotKind::Owning),
            ("leftRotate::x".to_owned(), SlotKind::Owning),
            ("leftRotate::y".to_owned(), SlotKind::Owning),
            ("leftRotate::T2".to_owned(), SlotKind::Owning),
            ("insert::node".to_owned(), SlotKind::Owning),
            ("height::N".to_owned(), SlotKind::Ref),
            ("getBalance::N".to_owned(), SlotKind::Ref),
            ("minValueNode::node".to_owned(), SlotKind::Ref),
            ("preOrder::root".to_owned(), SlotKind::Ref),
        ],
    );
}

/// Witness 19 (relay 003 §2 / R426-2, the Box-first market) — avl's
/// rotations, the substrate's own text. Under an era-5c-shaped frame the
/// two `Node` pointer fields DERIVE and the transaction is `applied` as
/// `opt-box`: the field side of the `TerminalRoleC` shape (a child moved
/// out, the parent stored into it, the rotated owner returned) needs
/// nothing new from this lane.
///
/// What blocks the delivery is the OWNING LOCALS' side, held by the native
/// Box family: `newNode::node`, `rightRotate::x` / `T2`, `leftRotate::y` /
/// `T2` hold `box-initializer-unsupported` (a Box local initialized from an
/// owning field's load — `let mut x = (*y).left;`), and `rightRotate::y`,
/// `leftRotate::x`, `insert::node` hold `box-param-caller-unknown` (a Box
/// PARAMETER whose callers' hand-over is not evidenced; `insert` is itself
/// held, so the two are one fixpoint). Those holds degrade the parameters,
/// their signature classes are withheld, and — exactly as witness 18 shows
/// for heman — the field transaction is then inactive at AST time, so the
/// struct keeps `*mut Node`.
///
/// The pin is a TRIPWIRE for the Box-first route: when ownership-fields
/// admit either prior key, avl's rotation family delivers and this witness
/// fails, at which point the emitted forms are pinned here instead.
#[test]
fn w6f_avl_rotation_fields_derive_and_the_box_locals_hold() {
    let _frame = frame_lock();
    avl_frame();
    let observed = observe(AVL);
    let outcome = emitted("avl", AVL);
    super::test_model_override::clear();
    for field in ["left", "right"] {
        let row = field_row(&observed, "Node", field);
        assert_eq!(
            (row.2.as_str(), row.3.as_str()),
            ("applied", "opt-box"),
            "{row:?}"
        );
    }
    for (label, prior) in [
        ("newNode::node", "box-initializer-unsupported"),
        ("rightRotate::x", "box-initializer-unsupported"),
        ("rightRotate::T2", "box-initializer-unsupported"),
        ("leftRotate::y", "box-initializer-unsupported"),
        ("leftRotate::T2", "box-initializer-unsupported"),
        ("rightRotate::y", "box-param-caller-unknown"),
        ("leftRotate::x", "box-param-caller-unknown"),
        ("insert::node", "box-param-caller-unknown"),
    ] {
        let decision = decision_of(&observed, label);
        assert!(
            decision.contains("BoxFailure") && decision.contains(prior),
            "{label}: {decision}"
        );
    }
    let (source, _, _) = emitted_source(&outcome);
    let flat: String = source.split_whitespace().collect::<Vec<_>>().join(" ");
    // The withheld owners keep the raw field declarations …
    assert!(flat.contains("pub left: *mut Node,"), "{source}");
    assert!(!flat.contains("Option<Box<Node>>"), "{source}");
    // … while the readers this lane does not own still deliver.
    assert!(
        flat.contains("fn height(mut N: Option<&Node>) -> i32 {"),
        "{source}"
    );
}

const HEMAN_RAY2: &str = include_str!("wave6f_fixture_heman_ray2.rs");

/// Witness 18 (relay 020 / R427-3) — heman's OWN `kmRay2IntersectBox`, the
/// substrate's text. G's transaction is derived and `applied` on the
/// decision side, and the three element loads decide `Ref` — but the
/// function's signature class is WITHHELD (its `ray` parameter degrades
/// `SilentCoercion { via: BorrowedIntoRawParam }`, and the callee
/// `kmRay2IntersectLineSegment::intersection` degrades `KindRaw`), so the
/// AST application is inactive for both owners and the two functions keep
/// their input text — no retype, no element wraps, no load declarations.
/// The other five functions of the reduction deliver.
///
/// This is why the candidate's custody comparator reads
/// `delivery-custody:inferred-type` on `this_point/next_point/other_point`:
/// the subjects are decided and counted, their owner is withheld, and the
/// tree therefore carries the input's inferred `let mut this_point = …`.
/// The pin is a TRIPWIRE: when the withholding lifts (another family
/// converts `ray`, or this lane bridges the loads at a withheld consumer),
/// this witness fails and the array's delivery is re-read here.
#[test]
fn w6f_heman_ray2_withheld_class_keeps_the_array_transaction_inactive() {
    let observed = observe(HEMAN_RAY2);
    let row = field_row(&observed, "kmRay2IntersectBox", "points");
    assert_eq!(
        (row.2.as_str(), row.3.as_str()),
        ("applied", "array-opt-ref-shared"),
        "{row:?}"
    );
    for label in [
        "kmRay2IntersectBox::this_point",
        "kmRay2IntersectBox::next_point",
        "kmRay2IntersectBox::other_point",
    ] {
        assert_eq!(
            decision_of(&observed, label),
            "Ref { mutable: false }",
            "{label}"
        );
    }
    assert!(
        decision_of(&observed, "kmRay2IntersectBox::ray").contains("BorrowedIntoRawParam"),
        "{:?}",
        decision_of(&observed, "kmRay2IntersectBox::ray")
    );
    let outcome = emitted("heman_ray2", HEMAN_RAY2);
    let (source, _, reverted) = emitted_source(&outcome);
    assert_eq!(reverted, 0, "{source}");
    let flat: String = source.split_whitespace().collect::<Vec<_>>().join(" ");
    for input_text in [
        // the withheld owner keeps every line of its input
        "let mut points: [*const kmVec2; 4] = [0 as *const kmVec2; 4];",
        "points[0 as i32 as usize] = p1;",
        "let mut this_point = points[i as usize];",
        // and its signature
        "fn kmRay2IntersectBox(mut ray: *const kmRay2, mut p1: *const kmVec2,",
    ] {
        assert!(
            flat.contains(input_text),
            "missing {input_text:?} in\n{source}"
        );
    }
    assert!(
        !flat.contains("[Option<&kmVec2>; 4]"),
        "the withheld class must carry no retype\n{source}"
    );
    // The five functions whose classes are not withheld DO deliver.
    for delivered in [
        "fn kmVec2Dot(mut pV1: &kmVec2, mut pV2: &kmVec2)",
        "fn kmVec2Length(mut pIn: &kmVec2) -> f32 {",
        "fn calculate_line_normal(mut p1: kmVec2, mut p2: kmVec2, mut other_point: kmVec2, mut normal_out: &mut kmVec2)",
    ] {
        assert!(
            flat.contains(delivered),
            "missing {delivered:?} in\n{source}"
        );
    }
}

const POINTS: &str = include_str!("wave6f_fixture_points.rs");

/// Witness 17 (G, relay 002 / R416): heman's `kmRay2IntersectBox` — a LOCAL
/// array of pointers is a transaction of the field vocabulary: the
/// declaration `[Option<&kmVec2>; 4]`, the null repeat `[None; 4]`, the
/// stores `Some(p1)`.., the loads `points[i].unwrap()` into explicitly typed
/// locals; the stored parameters deliver (`escapes-via-field-store`
/// discharged) and the loaded locals' opaque-provenance `Raw` is lifted (the
/// model registers no slots for a local's array). Control: a store from a
/// model-Raw local holds the whole array typed.
#[test]
fn w6f_array_of_references_local_delivers() {
    let observed = observe(POINTS);
    let row = field_row(&observed, "kmRay2IntersectBox", "points");
    assert_eq!(
        (row.2.as_str(), row.3.as_str()),
        ("applied", "array-opt-ref-shared"),
        "{row:?}"
    );
    for label in [
        "kmRay2IntersectBox::p1",
        "kmRay2IntersectBox::p4",
        "kmRay2IntersectBox::this_point",
        "kmRay2IntersectBox::next_point",
        "kmRay2IntersectBox::other_point",
    ] {
        assert_eq!(
            decision_of(&observed, label),
            "Ref { mutable: false }",
            "{label}"
        );
    }
    let outcome = emitted("points", POINTS);
    let (source, emitted_count, reverted) = emitted_source(&outcome);
    assert_eq!((emitted_count, reverted), (9, 0), "{source}");
    let flat: String = source.split_whitespace().collect::<Vec<_>>().join(" ");
    for needle in [
        "fn kmRay2IntersectBox(mut p1: &kmVec2, mut p2: &kmVec2, mut p3: &kmVec2, mut p4: &kmVec2) -> f32 {",
        "let mut points: [Option<&kmVec2>; 4] = [None; 4];",
        "points[0 as usize] = Some(p1);",
        "points[3 as usize] = Some(p4);",
        "let mut this_point: &crate::kmVec2 = points[i as usize].unwrap();",
        "let mut other_point: &crate::kmVec2 = if i == 3 as u32 || i == 0 as u32 { points[1 as usize].unwrap() } else { points[0 as usize].unwrap() };",
        "acc += kmVec2Dot(this_point, next_point) + (*this_point).x + (*other_point).y;",
    ] {
        // A composition may reborrow a thin Ref local's initializer
        // (`= &*points[i as usize].unwrap()`, another family's rule): the same
        // delivered form, one `&*` deeper. The pin is of the form, so a
        // reborrow-free reading of both sides satisfies it too.
        let reborrowless = flat.replace("&*", "");
        assert!(
            flat.contains(needle) || reborrowless.contains(&needle.replace("&*", "")),
            "missing {needle:?} in\n{source}"
        );
    }

    // Control: a raw-model source stored into the array.
    let raw_source = POINTS.replace(
        "    points[1 as usize] = p2;",
        "    let mut q = (p2 as usize + 8 as usize) as *const kmVec2;\n    points[1 as usize] = q;",
    );
    // (`q` is model-Ref but decides `copy-source-coupled`: the store's source
    // does not deliver, so the array holds at finalization.)
    let held = observe(&raw_source);
    let row = field_row(&held, "kmRay2IntersectBox", "points");
    assert_eq!(row.2, "held", "{row:?}");
    assert!(
        row.4
            .starts_with("store-source-degraded:kmRay2IntersectBox::q")
            || row.4 == "array-local-incomplete:store-source",
        "{row:?}"
    );

    // Control: the array used whole (copied) is a shape the transaction does
    // not express — a typed hold, never a silent skip.
    let copied = POINTS.replace(
        "    let mut i = 0 as u32;",
        "    let mut alias: [*const kmVec2; 4] = points;\n    let mut i = 0 as u32;",
    );
    let held = observe(&copied);
    let row = field_row(&held, "kmRay2IntersectBox", "points");
    assert_eq!(
        (row.2.as_str(), row.4.as_str()),
        ("held", "array-local-incomplete:array-use-shape"),
        "{row:?}"
    );
}
