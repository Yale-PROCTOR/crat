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
    // **R525-2** — one of the three rotating names. It sets no override of its
    // own, which is why it had no lock; but it READS shared frame state, and
    // the member of a coupled group that loses is decided by thread order. It
    // holds the crate-wide lock for its whole body, cache initialization
    // included.
    let _frame = frame_lock();
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
/// The CRATE-WIDE frame lock (R525-2). This file had its own mutex, which
/// serialized this lane's witnesses against each other and against nothing
/// else — and the rotation wave-6l 046 measured is a coupling with wave-6a's
/// two A1-e tests, in a different file. One lock, named where both can reach
/// it, is the only version of "serialize it" that can work.
fn frame_lock() -> std::sync::MutexGuard<'static, ()> {
    super::test_model_override::frame_lock()
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
    // **R538-3: a dichotomy on wave-6a's re-seat (`95f485540`).** `insert` and
    // `deleteNode` consume and return their node, and the re-seat makes those
    // formals owners (`Option<Box<node>>`). The moves then go into owned
    // formals, not raw ones, so the receipt's raw-move / raw-store fall and two
    // more classes deliver. The field contract below is the same on both
    // frames; the branch is decided by `deleteNode`'s formal, one structural
    // fact, and each branch pins its whole shape.
    let (source, emitted_count, reverted) = emitted_source(&outcome);
    let flat: String = source.split_whitespace().collect::<Vec<_>>().join(" ");
    let reseated = flat.contains("fn deleteNode(mut root: Option<Box<node>>,");
    assert!(
        reseated || flat.contains("fn deleteNode(mut root: *mut node,"),
        "deleteNode's formal is either raw or the re-seated owner:\n{source}"
    );
    let bridges = |moves: usize, stores: usize| {
        format!(
            "raw-move={moves};raw-view=1;raw-store={stores};dealloc-transfer=0;allocator-contract=0;waiver-drop-scope-exit=0;count-companion="
        )
    };
    let ((left_moves, left_stores), (right_moves, right_stores)) = if reseated {
        ((1, 1), (1, 1))
    } else {
        ((3, 3), (4, 4))
    };
    assert_eq!(
        observed.bridges,
        vec![
            (
                "node".to_owned(),
                "left".to_owned(),
                bridges(left_moves, left_stores)
            ),
            (
                "node".to_owned(),
                "right".to_owned(),
                bridges(right_moves, right_stores)
            ),
        ]
    );
    // The seam sees an owned argument in its consumer's form, so no glue may
    // stack on the field's wrap. Unseated, no glue is even planned over a field
    // site. **Re-seated, one IS planned** — `deleteNode`'s
    // `((*root).right) as *mut crate::node` for `minValueNode`'s argument, which
    // would be ill-typed against `Option<Box<node>>` — and it is inert only
    // because the field's wrap claims the node first (report 065, routed). So
    // the re-seated branch pins the hazard itself: no planned field glue
    // reaches the emitted tree.
    let field_glues: Vec<&String> = observed
        .seam_edits
        .iter()
        .map(|(_, replacement)| replacement)
        .filter(|replacement| replacement.contains(".left") || replacement.contains(".right"))
        .collect();
    if reseated {
        for glue in &field_glues {
            let glue: String = glue.split_whitespace().collect::<Vec<_>>().join(" ");
            assert!(
                !flat.contains(&glue),
                "a glue planned over an owned field reached the tree: {glue}\n{source}"
            );
        }
    } else {
        assert!(field_glues.is_empty(), "{:?}", observed.seam_edits);
    }
    assert_eq!(
        (emitted_count, reverted),
        (if reseated { 3 } else { 1 }, 0),
        "{source}"
    );
    let common = [
        // the declaration: null = None, ABI preserved (NPO)
        "pub left: Option<Box<node>>,",
        "pub right: Option<Box<node>>,",
        // a fresh allocation is written, never dropped through raw memory
        "core::ptr::write(&raw mut (*temp).left, None);",
        // a Ref-frame walker views the child; R425-2: the recursive walker's
        // two arguments are VIEWS of the children, not moves
        "inorder((*root.unwrap()).left.as_deref());",
        "inorder((*root.unwrap()).right.as_deref());",
        // the null test, and a raw view for a raw-declared walker
        "while !node.is_null() && !((*node).left).is_none() {",
        "node = (*node).left.as_deref_mut().map_or(core::ptr::null_mut(), core::ptr::from_mut);",
        // E5C-3 (report 007): the two-children branch hoists the pure read
        // before the moving argument
        "let __crat_hoist0 = (*temp_1).key;",
    ];
    let shaped: &[&str] = if reseated {
        &[
            // the moved Box goes into the owned formal as itself
            "insert((*node.as_deref_mut().unwrap()).left.take(), key)",
            // R425-2: the `minValueNode` receiver is a raw view of the child
            "minValueNode((*root.as_deref_mut().unwrap()).right.as_deref_mut().map_or(core::ptr::null_mut(), core::ptr::from_mut))",
            // the C free sites, now the owner's drop at exactly those sites
            "drop(root); return temp;",
            "drop(root); return temp_0;",
        ]
    } else {
        &[
            // a raw owning consumer receives the moved Box (receipted raw-move)
            "core::ptr::write(&raw mut (*node).left, core::ptr::NonNull::new(insert((*node).left.take().map_or(core::ptr::null_mut(), Box::into_raw), key)).map(|__p| Box::from_raw(__p.as_ptr())));",
            "if ((*root).left).is_none() {",
            // a move-out into a raw owning local
            "let mut temp = (*root).right.take().map_or(core::ptr::null_mut(), Box::into_raw);",
            // the C free site is untouched
            "free(root as *mut ::std::ffi::c_void); return temp;",
            // R425-2: the `minValueNode` receiver is a raw view of the child
            "minValueNode((*root).right.as_deref_mut().map_or(core::ptr::null_mut(), core::ptr::from_mut))",
        ]
    };
    for needle in common.iter().chain(shaped.iter()) {
        assert!(flat.contains(needle), "missing {needle:?} in\n{source}");
    }
    // R425-2 (era-5c 003) — the E5C-3 emission contract's SECOND clause:
    // the Owning kinds at the traversal / recursive-call arguments are token
    // loads whose callee formals stay `ref`, so they license NO drop. bst's
    // only deallocation sites are `deleteNode`'s two C `free`s; a `Box`
    // dropped at an argument site would free a linked subtree. So: EXACTLY two
    // deallocations, both at the C free sites — `free(root ..)` where `root` is
    // raw, the owner's `drop(root)` where it is re-seated — and no other drop.
    let frees = source
        .matches("free(root as *mut ::std::ffi::c_void);")
        .count();
    let drops_of_root = source.matches("drop(root);").count();
    assert_eq!(
        (frees + drops_of_root, source.matches("drop(").count()),
        (2, drops_of_root),
        "two deallocations, both at the C free sites, and no drop elsewhere\n{source}"
    );
    assert_eq!(
        (frees, drops_of_root),
        if reseated { (0, 2) } else { (2, 0) },
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
    let flat: String = source.split_whitespace().collect::<Vec<_>>().join(" ");
    // **R538-3: a dichotomy on wave-6a's re-seat (`95f485540`).** The pin is
    // the HOIST — the pure `Copy` read taken before the moving argument, and a
    // bare local never hoisted — and that holds on both frames. What the
    // re-seat changes is `deleteNode`'s formal: raw here, `Option<Box<node>>`
    // there (a formal consumed and returned is an owner), so the moved field
    // goes in as the Box itself and one more class delivers. Each branch pins
    // its whole shape; a third formal matches neither and fails.
    let reseated = flat.contains("fn deleteNode(mut root: Option<Box<node>>,");
    assert!(
        reseated || flat.contains("fn deleteNode(mut root: *mut node,"),
        "deleteNode's formal is either raw or the re-seated owner:\n{source}"
    );
    assert_eq!(
        (emitted_count, reverted),
        (if reseated { 3 } else { 2 }, 0),
        "{source}"
    );
    let moved = if reseated {
        "(*root).right.take()"
    } else {
        "(*root).right.take().map_or(core::ptr::null_mut(), Box::into_raw)"
    };
    let bare = if reseated {
        "deleteNode((*root.as_deref_mut().unwrap()).left.take(), key)"
    } else {
        "deleteNode((*root).left.take().map_or(core::ptr::null_mut(), Box::into_raw), key)"
    };
    for needle in [
        format!(
            // R538-3: the hoisted read ABSORBS the preceding assignment of the
            // same read — the binding moves above `(*root).key = (*temp).key;`,
            // so `temp`'s last use precedes the write through the owner (the
            // E0499 wave-6a measured once the owner is a re-seated Box).
            "pub unsafe extern \"C\" fn removeMin(mut root: &mut node) {{ let mut temp: &crate::node = (*root).right.as_deref().unwrap(); let __crat_hoist0 = (*temp).key; (*root).key = (*temp).key; (*root).right = core::ptr::NonNull::new(deleteNode({moved}, __crat_hoist0)).map(|__p| Box::from_raw(__p.as_ptr())); }}"
        ),
        // a bare local read (`key`) is not hoisted — nothing a move invalidates
        bare.to_owned(),
    ] {
        assert!(flat.contains(&needle), "missing {needle:?} in\n{source}");
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
    // **The transfer, either way `h` is delivered** (R494-2). The allocation
    // leaves through `take()` + `Box::into_raw` at the contract deallocator's
    // own call — free timing unmoved, the field `None` afterwards — but WHERE
    // that expression sits is the container formal's business, and the
    // container formal is another family's:
    //
    //   `h: *mut Holder`   the transfer is the call's argument;
    //   `h: &mut Holder`   A9 made it a reference, so the call carries an A5
    //                      raw view and the transfer is HOISTED into the
    //                      view's own binding — which is the whole point of
    //                      the hoist: both the field and the formal deliver
    //                      instead of the program delivering nothing.
    let transfer = "(*h).slot_.take().map_or(core::ptr::null_mut(), |__b| Box::into_raw(__b) as *mut ::std::ffi::c_void)";
    assert!(flat.contains(transfer), "{source}");
    if flat.contains("fn HolderFree(mut m: &mut Mem, mut h: &mut Holder)") {
        assert!(
            flat.contains(&format!("let __crat_a5_raw")) && flat.contains(&format!("{transfer};")),
            "a delivered container hoists the transfer into the A5 view's binding\n{source}"
        );
    } else {
        assert!(
            flat.contains(&format!("CustomFree(m, {transfer});")),
            "a raw container keeps the transfer as the call's argument\n{source}"
        );
    }

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

const OWNED_ARRAY: &str = include_str!("wave6f_fixture_owned_array.rs");

/// Witness 22 (relay 026, build 3) — a written element is TWO families and
/// the census must not read one as the other. An OWNED-element array stores
/// a fresh allocation into every element and releases every element at its
/// own C free (lodepng's `filter::attempt*` ×3, tulip's
/// `smoke::test_ind_name` ×3): it DELIVERS as `[Option<Box<[T]>>; N]`
/// (witness 23). The controls hold, each for its own reason: BORROWED
/// elements (`mutable-elements` — N live `&mut` would need a disjointness
/// argument, R395-2); allocated but never released (`no-release` — the drops
/// sit at C free sites and there is none); released through a call that is
/// not a deallocator (`release-not-a-deallocator` — handing C a view of
/// memory the `Box` still owns would double-free at scope exit).
#[test]
fn w6f_a_written_element_names_its_family() {
    let observed = observe(OWNED_ARRAY);
    let owned = field_row(&observed, "filter", "attempt");
    assert_eq!(
        (owned.2.as_str(), owned.3.as_str()),
        ("applied", "array-opt-box-slice"),
        "{owned:?}"
    );
    for (function, array, reason) in [
        (
            "borrowed_rows",
            "rows",
            "array-local-incomplete:mutable-elements",
        ),
        ("leaked", "scratch", "array-owned-incomplete:no-release"),
        // handed on WHOLE: an owned element is a boxed slice, two words, so
        // the whole-array view's layout claim does not hold for it
        ("whole", "bufs", "array-owned-incomplete:array-use-shape"),
        (
            "registered",
            "kept",
            "array-owned-incomplete:release-not-a-deallocator",
        ),
    ] {
        let row = field_row(&observed, function, array);
        assert_eq!(
            (row.2.as_str(), row.4.as_str()),
            ("held", reason),
            "{row:?}"
        );
    }
}

/// Witness 23 (relay 027, build 3 stage 2) — the owned-element array
/// delivers. Every element owns its allocation as a boxed slice whose
/// length is the allocation's OWN size argument (no fabricated extent); the
/// null test reads the option; a callee delivered as a slice takes the
/// buffer's own slice; an offset read indexes it; and the C free site keeps
/// its call, receiving the allocation back through `take()` +
/// `Box::into_raw` — the free stays exactly where C put it (R395-2) and the
/// element is `None` afterwards, so nothing drops twice.
#[test]
fn w6f_owned_element_array_delivers() {
    let outcome = emitted("owned_array", OWNED_ARRAY);
    let (source, emitted_count, reverted) = emitted_source(&outcome);
    assert_eq!(reverted, 0, "{source}");
    assert!(emitted_count >= 1, "{emitted_count}\n{source}");
    let flat: String = source.split_whitespace().collect::<Vec<_>>().join(" ");
    for needle in [
        "let mut attempt: [Option<Box<[u8]>>; 5] = [const { None }; 5];",
        "attempt[type_1 as usize] = core::ptr::NonNull::new(lodepng_malloc(linebytes) as *mut u8).map(|__p| Box::from_raw(core::ptr::slice_from_raw_parts_mut(__p.as_ptr(), (linebytes) as usize)));",
        "if (attempt[type_1 as usize]).is_none() {",
        "filterScanline(attempt[type_1 as usize].as_deref_mut().unwrap(),",
        "(attempt[type_1 as usize]).as_deref().unwrap()[(0 as isize) as usize]",
        "lodepng_free(attempt[type_1 as usize].take().map_or(core::ptr::null_mut(), |__b| Box::into_raw(__b) as *mut std::ffi::c_void));",
    ] {
        assert!(flat.contains(needle), "missing {needle:?} in\n{source}");
    }
    // The three controls keep their raw arrays in the same tree.
    for untouched in [
        "let mut rows: [*mut u8; 2] = [0 as *mut u8; 2];",
        "let mut scratch: [*mut u8; 2] = [0 as *mut u8; 2];",
        "let mut kept: [*mut u8; 2] = [0 as *mut u8; 2];",
    ] {
        assert!(
            flat.contains(untouched),
            "missing {untouched:?} in\n{source}"
        );
    }
}

const TULIP_ARRAYS: &str = include_str!("wave6f_fixture_tulip_arrays.rs");

/// Witness 21 (relay 024, build 2) — the whole array handed to a callee.
/// `inputs.as_ptr()` on a converted array is the receipted raw VIEW: an
/// `Option<&T>` has the layout, size and ABI of `*const T` (the null-pointer
/// optimisation, `None` = null), so `[Option<&T>; N]` and `[*const T; N]`
/// are the same bytes and the callee reads exactly what C wrote. The cast is
/// the bridge (R130's second tier, receipted `raw-view` per site); the view
/// is SHARED — `as_mut_ptr` belongs to the written-element family and keeps
/// its hold.
#[test]
fn w6f_tulip_array_delivers_through_its_whole_array_view() {
    let observed = observe(TULIP_ARRAYS);
    let row = field_row(&observed, "stress", "inputs");
    assert_eq!(
        (row.2.as_str(), row.3.as_str()),
        ("applied", "array-opt-ref-shared"),
        "{row:?}"
    );
    let outcome = emitted("tulip_arrays", TULIP_ARRAYS);
    let (source, emitted_count, reverted) = emitted_source(&outcome);
    assert_eq!(reverted, 0, "{source}");
    assert!(emitted_count >= 8, "{emitted_count}\n{source}");
    let flat: String = source.split_whitespace().collect::<Vec<_>>().join(" ");
    for needle in [
        "let mut inputs: [Option<&f64>; 4] = [None; 4];",
        "inputs[0 as usize] = Some(data_in);",
        "let mut probe: &f64 = inputs[2 as usize].unwrap();",
        // the view, cast at the seam
        "inputs.as_ptr() as *const *const f64",
    ] {
        let reborrowless = flat.replace("&*", "");
        assert!(
            flat.contains(needle) || reborrowless.contains(&needle.replace("&*", "")),
            "missing {needle:?} in\n{source}"
        );
    }
    // The value-list array beside it is untouched: no view, no retype.
    assert!(
        flat.contains("let mut all_inputs: [*const f64; 1] = [data_in];"),
        "{source}"
    );
}

/// Witness 20 (relay 023 §3, build 1) — the census's eleven
/// `array-local-incomplete:initializer` rows are tulip's element LISTS, the
/// substrate's other spelling of the same array. A list whose elements are
/// all the null literal is the repeat form written out: it is admitted and
/// renders `[None; N]` (build 2 then carries the whole-array view, so this
/// array delivers — witness 21). A list with a VALUE element is a different family (each
/// element is a store whose source must deliver) and holds under its own
/// reason, `initializer-element-source`, instead of the blanket one.
#[test]
fn w6f_tulip_element_list_initializers_split_by_their_elements() {
    let observed = observe(TULIP_ARRAYS);
    let null_list = field_row(&observed, "stress", "inputs");
    assert_eq!(
        (null_list.2.as_str(), null_list.3.as_str()),
        ("applied", "array-opt-ref-shared"),
        "{null_list:?}"
    );
    let value_list = field_row(&observed, "main_0", "all_inputs");
    assert_eq!(
        (value_list.2.as_str(), value_list.4.as_str()),
        ("held", "array-local-incomplete:initializer-element-source"),
        "{value_list:?}"
    );
    // A value list whose elements are BUFFERS (a local array's `as_ptr`, a C
    // string literal) says so: those readers index past the first element and
    // R395-2 never widens a thin reference, while the fat element form is
    // excluded by the whole-array view these arrays are handed on through.
    let buffers = field_row(&observed, "buffers", "inputs");
    assert_eq!(
        (buffers.2.as_str(), buffers.4.as_str()),
        (
            "held",
            "array-local-incomplete:initializer-element-buffer-source"
        ),
        "{buffers:?}"
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
const QUADTREE_ROOT: &str = include_str!("wave6f_fixture_quadtree_root.rs");
const MALLOC_FREE_FIELD: &str = include_str!("wave6f_fixture_malloc_free_field.rs");
const OWNED_SUBFIELD_WRITE: &str = include_str!("wave6f_fixture_owned_subfield_write.rs");

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

/// Witness 19 (relay 003 §2 / R426-2, re-pinned at relay 025) — avl's
/// rotations, the substrate's own text. The FIELD side is this lane's and
/// is stable: under an era-5c-shaped frame both `Node` pointer fields
/// derive and the transaction is `applied` as `opt-box` — the
/// `TerminalRoleC` shape needs no new vocabulary here.
///
/// The owning LOCALS are the native Box family's, and they move: at
/// `8e84dc6d` all eight hold (`box-initializer-unsupported` ×5 — the
/// `malloc` cast and the four rotation locals initialized from an owning
/// field's load; `box-param-caller-unknown` ×3 — the rotation / `insert`
/// fixpoint), while on the batch-10 composition ownership-fields' newer
/// build delivers all FIVE as `Box::new(..)` / `Box::into_raw(..)` and the
/// three parameters hold `box-param-callee-use` instead. So the pin is
/// the DICHOTOMY: while ANY owner is held the transaction is inactive and
/// the struct keeps `*mut Node`; when every owner delivers the struct must
/// carry `Option<Box<Node>>`. That is the tripwire for the Box-first route.
#[test]
fn w6f_avl_rotation_fields_derive_and_follow_their_box_locals() {
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
    let owners = [
        "newNode::node",
        "rightRotate::x",
        "rightRotate::T2",
        "leftRotate::y",
        "leftRotate::T2",
        "rightRotate::y",
        "leftRotate::x",
        "insert::node",
    ];
    // "Held" is read as "does not deliver a Box", not by the native family's
    // reason text: those keys move (at `8e84dc6d` the five loads/`malloc`
    // hold `box-initializer-unsupported` and the three parameters
    // `box-param-caller-unknown`; on the batch-10 composition the five
    // deliver and the three hold `box-param-callee-use` instead).
    let held: Vec<&str> = owners
        .into_iter()
        .filter(|label| !decision_of(&observed, label).starts_with("Box("))
        .collect();
    let (source, _, _) = emitted_source(&outcome);
    let flat: String = source.split_whitespace().collect::<Vec<_>>().join(" ");
    if held.is_empty() {
        // Every owner delivers: the fields must be the owned form.
        assert!(
            flat.contains("pub left: Option<Box<Node>>,"),
            "every Box local delivers, so the field must too\n{source}"
        );
    } else {
        // A held owner withholds its class, so the transaction is inactive
        // and the struct keeps the raw field it came with.
        assert!(flat.contains("pub left: *mut Node,"), "{held:?}\n{source}");
        assert!(!flat.contains("Option<Box<Node>>"), "{held:?}\n{source}");
    }
    // The readers this lane does not own deliver either way.
    assert!(
        flat.contains("fn height(mut N: Option<&Node>) -> i32 {"),
        "{source}"
    );
}

const HEMAN_RAY2: &str = include_str!("wave6f_fixture_heman_ray2.rs");

/// Witness 18 (relay 020 / R427-3, re-pinned at relay 025) — heman's OWN
/// `kmRay2IntersectBox`, the substrate's text. G's transaction is derived
/// and `applied` on the decision side and the three element loads decide
/// `Ref`; what the EMISSION then does is decided by the owners' classes,
/// and that verdict moves with the neighbouring lanes (at `8e84dc6d` the
/// class is withheld — `ray` degrades `SilentCoercion { via:
/// BorrowedIntoRawParam }` behind `kmRay2IntersectLineSegment::intersection`
/// = `KindRaw`; on the batch-10 composition wave-5d2's work has `ray`
/// reading `Ref`, so the class is PLANNED). The witness pins the
/// DICHOTOMY, which is the invariant either way: a withheld owner keeps
/// every line of its input and carries no retype; a planned owner carries
/// the retype and the declared loads. It stays a tripwire — it fails only
/// if an owner is planned and the array does NOT deliver, which is the
/// state that would be a defect of this lane.
#[test]
fn w6f_heman_ray2_array_follows_its_owner_class() {
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
    let withheld = decision_of(&observed, "kmRay2IntersectBox::ray").contains("Degraded");
    let outcome = emitted("heman_ray2", HEMAN_RAY2);
    let (source, _, reverted) = emitted_source(&outcome);
    assert_eq!(reverted, 0, "{source}");
    let flat: String = source.split_whitespace().collect::<Vec<_>>().join(" ");
    if withheld {
        // The withheld owner keeps every line of its input, and its signature.
        for input_text in [
            "let mut points: [*const kmVec2; 4] = [0 as *const kmVec2; 4];",
            "points[0 as i32 as usize] = p1;",
            "let mut this_point = points[i as usize];",
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
    } else {
        // A planned owner delivers the array: the retype, the stores and the
        // declared loads (modulo a composition's reborrow).
        let reborrowless = flat.replace("&*", "");
        for delivered in [
            "let mut points: [Option<&kmVec2>; 4] = [None; 4];",
            "points[0 as i32 as usize] = Some(p1);",
            "let mut this_point: &crate::kmVec2 = points[i as usize].unwrap();",
        ] {
            assert!(
                flat.contains(delivered) || reborrowless.contains(&delivered.replace("&*", "")),
                "the planned owner must deliver: missing {delivered:?} in\n{source}"
            );
        }
    }
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

/// The seam query's answers for a list of `(item name, field index)` asks,
/// read INSIDE the compiler run where `tcx` and the table live. The item is
/// looked up by its last path segment, which is what a fixture spells; a
/// FUNCTION name is a legal ask (that is how the array guard is measured).
fn owning_field_forms(source: &str, asks: &[(&str, usize)]) -> Vec<Option<String>> {
    let asks: Vec<(String, usize)> = asks
        .iter()
        .map(|(name, index)| ((*name).to_owned(), *index))
        .collect();
    ::utils::compilation::run_compiler_on_str(source, move |tcx| {
        let (table, _ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                A5Mode::PreciseReplay,
                Some(WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .unwrap();
        asks.iter()
            .map(|(name, index)| {
                let did = tcx
                    .hir_crate_items(())
                    .free_items()
                    .map(|id| id.owner_id.def_id)
                    .find(|did| {
                        tcx.opt_item_name(did.to_def_id())
                            .is_some_and(|item| item.as_str() == name)
                    })
                    .unwrap_or_else(|| panic!("item {name}"))
                    .to_def_id();
                super::decision::field_reference::owning_field_form(tcx, &table, did, *index)
            })
            .collect()
    })
    .unwrap()
}

/// Witness 24 (relay 032 / R448-5) — **the field-transaction seam answered
/// from a real transaction.** The ownership-fields family holds a moved-out
/// field owner fail-closed (`native-field-load-field-not-owned`) until a
/// producer names the field's delivered form; this is that answer, measured
/// on avl's own text where the transaction is real rather than injected.
///
/// The RED is exactly their R431 witness's premise: with the query answering
/// `None` the owner holds, which is the base behaviour their report 035
/// claim 1 pins. Here it answers `opt-box` for both rotated fields, and
/// `None` everywhere it must stay fail-closed.
#[test]
fn w6f_the_seam_query_answers_an_owning_field_from_its_transaction() {
    let _frame = frame_lock();
    avl_frame();
    let observed = observe(AVL);
    // The transaction really is there and really is owning (witness 19's pin).
    for field in ["left", "right"] {
        let row = field_row(&observed, "Node", field);
        assert_eq!(
            (row.2.as_str(), row.3.as_str()),
            ("applied", "opt-box"),
            "{row:?}"
        );
    }
    // `Node` is `{ key, left, right, height }`: the two OWNING fields answer
    // their delivered form; the two scalars, which carry no transaction at
    // all, answer `None`.
    let answers = owning_field_forms(AVL, &[("Node", 1), ("Node", 2), ("Node", 0), ("Node", 3)]);
    super::test_model_override::clear();
    assert_eq!(
        answers,
        vec![
            Some("opt-box".to_owned()),
            Some("opt-box".to_owned()),
            None,
            None,
        ],
        "{answers:?}"
    );
}

/// The seam query asked with a transaction's OWN key: for each
/// `(struct, field)` receipt identity, the answer a consumer gets when it
/// names exactly the field that transaction owns. This is what makes the
/// fail-closed arms falsifiable — a guessed field index would answer `None`
/// for the wrong reason.
fn owning_field_form_of(source: &str, asks: &[(&str, &str)]) -> Vec<Option<String>> {
    let asks: Vec<(String, String)> = asks
        .iter()
        .map(|(s, f)| ((*s).to_owned(), (*f).to_owned()))
        .collect();
    ::utils::compilation::run_compiler_on_str(source, move |tcx| {
        let (table, _ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                A5Mode::PreciseReplay,
                Some(WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .unwrap();
        asks.iter()
            .map(|(owner, field)| {
                let transaction = table
                    .field_transactions
                    .applied
                    .iter()
                    .find(|t| {
                        t.struct_path
                            .rsplit("::")
                            .next()
                            .unwrap_or(t.struct_path.as_str())
                            == owner
                            && &t.field_name == field
                    })
                    .unwrap_or_else(|| panic!("no applied transaction for {owner}.{field}"));
                super::decision::field_reference::owning_field_form(
                    tcx,
                    &table,
                    transaction.key.struct_did.to_def_id(),
                    transaction.key.field_index,
                )
            })
            .collect()
    })
    .unwrap()
}

/// Witness 25 (relay 032 / R448-5) — the query's fail-closed arms, each asked
/// with the transaction's own key so the refusal cannot be an accident of a
/// guessed index.
///
/// A BORROWED field is delivered and `applied`, and still answers `None`: a
/// `Box` local moved out of a field this family delivers as `Option<&T>`
/// would close memory the container still points into. An ARRAY transaction
/// keys its `FieldKey` on the owning FUNCTION and a local's `HirId`, not on a
/// struct and a field index, so asking with that key must not return its
/// `array-opt-box-slice` form.
#[test]
fn w6f_the_seam_query_is_closed_on_every_form_it_does_not_own() {
    let _frame = frame_lock();
    // hti `_table` is delivered `opt-ref-shared` — a BORROWED field.
    let observed = observe(HT);
    let row = field_row(&observed, "hti", "_table");
    assert_eq!(
        (row.2.as_str(), row.3.as_str()),
        ("applied", "opt-ref-shared"),
        "{row:?}"
    );
    let borrowed = owning_field_form_of(HT, &[("hti", "_table")]);
    assert_eq!(
        borrowed,
        vec![None],
        "a borrowed field never licenses a Box local: {borrowed:?}"
    );
    // `filter`'s array is `array-opt-box-slice`, keyed on the FUNCTION.
    let observed = observe(OWNED_ARRAY);
    let row = field_row(&observed, "filter", "attempt");
    assert_eq!(
        (row.2.as_str(), row.3.as_str()),
        ("applied", "array-opt-box-slice"),
        "{row:?}"
    );
    let array = owning_field_form_of(OWNED_ARRAY, &[("filter", "attempt")]);
    assert_eq!(
        array,
        vec![None],
        "an array transaction is not a struct field: {array:?}"
    );
    // And the owning field answers through the same route, so the three arms
    // are measured against one another rather than against nothing.
    avl_frame();
    let owned = owning_field_form_of(AVL, &[("Node", "left"), ("Node", "right")]);
    super::test_model_override::clear();
    assert_eq!(
        owned,
        vec![Some("opt-box".to_owned()), Some("opt-box".to_owned())],
        "{owned:?}"
    );
}

const INLINE_ARRAY: &str = include_str!("wave6f_fixture_inline_array.rs");

/// Witness 26 (relay 034 / R451-4, **W6F-5**; restated for the composed
/// frame under R217-2(a), relay 036 §1) — the inline array field taken as a
/// pointer.
///
/// **The guards are absolute and hold on every frame.** Five shapes must
/// never become a view, and none of them is a neighbour's to deliver either:
/// two `&mut` views of one array live at once are Stacked-Borrows UB even
/// with correct provenance and the true length (wave-6k 022's
/// counterfactuals, relay 036 §3).
///
/// **The delivery is a DICHOTOMY**, because a neighbour's arm decides it.
/// wave-6a's `slice_local_construction::refuses` clause
/// `root_is_a_reference_candidate` refuses every construction whose root the
/// model settles `Ref` — and its own doc names this market's shape with
/// brotli's own length, `from_raw_parts_mut((*s).arr.as_mut_ptr(), 704)`. On
/// this lane's frame W6F-5 delivers; on a composition carrying that refusal
/// the subject holds and the INPUT text is kept, whole. Half a delivery
/// would be the defect, so the pin is that the two move together.
#[test]
fn w6f_an_inline_array_field_taken_as_a_pointer_delivers_a_slice() {
    use crate::analyses::borrow_ownership::SlotKind;
    let _frame = frame_lock();
    // Everything in this fixture has a root the model settles `Ref`; one
    // function's root is stood in as `Raw` so both renderings are measured in
    // ONE run against one another.
    super::test_model_override::set(
        "w6f-inline-array-frame",
        Vec::new(),
        vec![("raw_root::self_0".to_owned(), SlotKind::Raw)],
    );
    let observed = observe(INLINE_ARRAY);
    let outcome = emitted("inline-array", INLINE_ARRAY);
    super::test_model_override::clear();
    let (source, _, reverted) = emitted_source(&outcome);
    assert_eq!(reverted, 0, "{source}");
    let flat: String = source.split_whitespace().collect::<Vec<_>>().join(" ");

    // The guards, on every frame.
    for (label, why) in [
        (
            "second_touch::last_entropy",
            "the field place is read again",
        ),
        (
            "whole_overwrite::last_entropy",
            "the struct is overwritten whole",
        ),
        ("widen::w", "a shared decay cast to `*mut` would widen `&T`"),
        (
            "escape_after::last_entropy",
            "the root escapes while the view lives",
        ),
        (
            "decay_in_a_loop::last_entropy",
            "inside a loop there is no order between the escape and the decay",
        ),
    ] {
        assert!(
            decision_of(&observed, label).starts_with("Degraded"),
            "{label} must stay out ({why}): {}",
            decision_of(&observed, label)
        );
    }
    // …and the input text of each is kept, not half-rewritten.
    for needle in [
        "(*self_0).last_entropy_[1 as usize] = 2.0f64;",
        "let mut w = ((*ro).last_entropy_).as_ptr() as *mut f64;",
        "observe_splitter(self_0);",
    ] {
        assert!(flat.contains(needle), "missing {needle:?} in\n{source}");
    }

    // The market, and the ordered half of the escape rule beside it.
    // Two groups, because two different things decide them. The REBORROW
    // group shares one gate — wave-6a's `root_is_a_reference_candidate`,
    // which fires exactly on a root the model settles `Ref` — so those three
    // move together or not at all. The CONSTRUCTOR group has a raw root, so
    // that refusal's predicate is false for it and it is independent.
    let reborrow_market = [
        (
            "finish_block::last_entropy",
            "let mut last_entropy: &mut [f64] = &mut ((*self_0).last_entropy_)[..];",
            "let mut last_entropy = ((*self_0).last_entropy_).as_mut_ptr();",
        ),
        (
            "trace3::m",
            "let mut m: &[f32] = &((*pIn).mat)[..];",
            "let mut m = ((*pIn).mat).as_ptr();",
        ),
        (
            // brotli's `StartPosQueuePush` shape: the root is handed to a
            // callee BEFORE the view is taken, so the view is still sound.
            "escape_before::last_entropy",
            "let mut last_entropy: &mut [f64] = &mut ((*self_0).last_entropy_)[..];",
            "let mut last_entropy = ((*self_0).last_entropy_).as_mut_ptr();",
        ),
    ];
    // W6F-5 as built: a RAW root has no reference to reborrow from, so the
    // constructor with its evidence extent is the form.
    let constructor_market = [(
        "raw_root::v",
        "let mut v: &[f64] = core::slice::from_raw_parts(((*self_0).last_entropy_).as_ptr(), 2usize);",
        "let mut v = ((*self_0).last_entropy_).as_ptr();",
    )];

    let mut check = |group: &[(&str, &str, &str)], name: &str| {
        let delivered: Vec<&str> = group
            .iter()
            .filter(|(label, _, _)| decision_of(&observed, label).starts_with("Slice"))
            .map(|(label, _, _)| *label)
            .collect();
        if delivered.len() == group.len() {
            for (_, emitted_form, _) in group {
                assert!(
                    flat.contains(emitted_form),
                    "missing {emitted_form:?} in\n{source}"
                );
            }
        } else {
            assert!(
                delivered.is_empty(),
                "half the {name} market is a defect, not a frame: {delivered:?}\n{source}"
            );
            for (_, _, input_form) in group {
                assert!(
                    flat.contains(input_form),
                    "held, so the input text must be kept: missing {input_form:?} in\n{source}"
                );
            }
            // …and the hold is a NEIGHBOUR'S refusal, not a defect in this
            // rule. The two are distinguishable by the rewriter's own degrade
            // reason: an earlier refusal reaches the residue
            // (`place-read-pointee`), while a broken declaration channel
            // leaves the surface placement unplaceable and walks the
            // SliceConstruction family back to `Core`, which reports
            // `slice-local-construction`. Reading the reason here is
            // deliberate — it is this crate's own vocabulary, not another
            // lane's hold text, and without it this branch would pass for a
            // defect of this rule's own making.
            for (label, _, _) in group {
                let held = decision_of(&observed, label);
                assert!(
                    !held.contains("SliceLocalConstruction"),
                    "{label} is held because THIS rule's declaration channel \
                     failed, not because a neighbour refused: {held}\n{source}"
                );
            }
        }
        !delivered.is_empty()
    };
    let reborrowed = check(&reborrow_market, "reborrow");
    check(&constructor_market, "constructor");

    if reborrowed {
        // Where a constructor is used at all, its extent is the array type's
        // own length; the reborrows carry no extent to fabricate.
        for fabricated in [
            "((*self_0).last_entropy_).as_mut_ptr(), crate::FALLBACK_SLICE_EXTENT",
            "((*self_0).last_entropy_).as_ptr(), crate::FALLBACK_SLICE_EXTENT",
            "((*pIn).mat).as_ptr(), crate::FALLBACK_SLICE_EXTENT",
        ] {
            assert!(
                !flat.contains(fabricated),
                "the length is in the array's own type; nothing may be fabricated\n{source}"
            );
        }
        // And a reborrow never borrows a raw root, which would not compile.
        assert!(
            !flat.contains("let mut v: &[f64] = &((*self_0).last_entropy_)[..];"),
            "a raw root has no reference to reborrow from\n{source}"
        );
    }
}

const MOVED_OUT_FIELD: &str = include_str!("wave6f_fixture_moved_out_field.rs");

/// Witness 27 (relay 038 / R456-5) — ownership-fields 041 §3's fixture: an
/// OWNING struct field whose value is MOVED OUT into a local, the field
/// nulled, and the local freed. Their dry14 dump shows the transaction
/// `applied` with its wraps claiming their spans while **none** of its edits
/// reaches the emitted candidate — `pub buf: *mut u8` survives and the load
/// stays bare. This is the shape every avl / bst / quadtree node field
/// becomes once the model settles it Owning, so it gates the whole
/// CROWN-Box parity market.
#[test]
fn w6f_a_moved_out_owning_field_reaches_the_tree() {
    let _frame = frame_lock();
    use crate::analyses::borrow_ownership::SlotKind;
    // R465-3: the frame override is what makes this witness deterministic on
    // THIS lane's frame, and it is also the thing a composed frame does not
    // need — the model settles `Holder.buf` Owning there by itself (report
    // 037 §1). `CRAT_W6F_NO_FRAME` suppresses it so the two readings are one
    // committed switch apart instead of an uncommitted edit apart.
    if std::env::var("CRAT_W6F_NO_FRAME").is_err() {
        super::test_model_override::set(
            "w6f-moved-out-field-frame",
            vec![("Holder".to_owned(), 0, SlotKind::Owning)],
            Vec::new(),
        );
    }
    let observed = observe(MOVED_OUT_FIELD);
    let outcome = emitted("moved-out-field", MOVED_OUT_FIELD);
    super::test_model_override::clear();
    let row = field_row(&observed, "Holder", "buf");
    assert_eq!(
        (row.2.as_str(), row.3.as_str()),
        ("applied", "opt-box"),
        "{row:?}"
    );
    let (source, _, reverted) = emitted_source(&outcome);
    assert_eq!(reverted, 0, "{source}");
    let flat: String = source.split_whitespace().collect::<Vec<_>>().join(" ");
    // An `applied` transaction whose edits do not reach the tree is the
    // defect: the receipt would claim a conversion the program never got.
    // An `applied` transaction whose edits do not reach the tree would be a
    // receipt claiming a conversion the program never got, so every site is
    // pinned — but HOW the store is spelled is the container's business, and
    // the container is another producer's. Hence a dichotomy on the one
    // observable that decides it (their STOP 1 / relay 045 §1).
    assert!(
        flat.contains("pub buf: Option<Box<u8>>,"),
        "the field declaration never reached the tree\n{source}"
    );
    assert!(
        !flat.contains("pub buf: *mut u8,"),
        "the raw field survived beside an applied transaction\n{source}"
    );
    let container_is_a_box = flat.contains("let mut h: ::std::boxed::Box<crate::Holder> =");
    if container_is_a_box {
        // The composed frame: `h` is a fully INITIALISED `Box`, so the place
        // is valid and the ordinary assignment is right — it drops the old
        // owner, which is addendum 101's waiver. `ptr::write` is the
        // pre-initialisation spelling and would leak here.
        for needle in [
            "(*h).buf = core::ptr::NonNull::new(malloc(64 as u64) as *mut u8).map(|__p| Box::from_raw(__p.as_ptr()));",
            "let mut b: ::std::option::Option<::std::boxed::Box<u8>> = (*h).buf.take();",
            "(*h).buf = None;",
        ] {
            assert!(flat.contains(needle), "missing {needle:?} in\n{source}");
        }
        assert!(
            !flat.contains("core::ptr::write(&raw mut (*h).buf"),
            "an initialised Box needs no pre-initialisation store\n{source}"
        );
        // The C frees become drops AT THE SAME SITES (R425-2 / §28): the
        // owner is a Box either side of the move, so nothing is freed twice
        // and nothing leaks.
        for needle in ["::std::mem::drop(b)", "::std::mem::drop(h)"] {
            assert!(flat.contains(needle), "missing {needle:?} in\n{source}");
        }
        // The `extern "C"` declaration is not a call site: count the calls.
        assert_eq!(
            flat.matches("free(b").count() + flat.matches("free(h").count(),
            0,
            "{source}"
        );
    } else {
        // This lane's frame: `h` is `malloc`ed memory, so the place may be
        // uninitialised and the store must never drop what is there.
        for needle in [
            "core::ptr::write(&raw mut (*h).buf, core::ptr::NonNull::new(malloc(64 as u64) as *mut u8).map(|__p| Box::from_raw(__p.as_ptr())));",
            "let mut b = (*h).buf.take().map_or(core::ptr::null_mut(), Box::into_raw);",
            "core::ptr::write(&raw mut (*h).buf, None);",
        ] {
            assert!(flat.contains(needle), "missing {needle:?} in\n{source}");
        }
        // The C frees stay where the input put them and no Rust drop joins
        // them: the move hands the allocation back as a raw pointer.
        assert_eq!(flat.matches("free(").count(), 3, "{source}");
        assert!(
            !flat.contains("drop("),
            "no Rust drop may join the C frees\n{source}"
        );
    }
}

/// The receipt at a named revert state, read inside the compiler run.
/// Returns `(status, revert_status)` per `(struct, field)` ask, once with an
/// EMPTY revert set and once with the named owners' classes reverted.
fn receipt_at_reverts(
    source: &str,
    asks: &[(&str, &str)],
    reverted_owners: &[&str],
) -> (Vec<(String, String)>, Vec<(String, String)>) {
    let asks: Vec<(String, String)> = asks
        .iter()
        .map(|(s, f)| ((*s).to_owned(), (*f).to_owned()))
        .collect();
    let owners: Vec<String> = reverted_owners.iter().map(|o| (*o).to_owned()).collect();
    ::utils::compilation::run_compiler_on_str(source, move |tcx| {
        let (table, _ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                A5Mode::PreciseReplay,
                Some(WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .unwrap();
        let read = |receipt: &str| -> Vec<(String, String)> {
            asks.iter()
                .map(|(s, f)| {
                    let row = receipt
                        .lines()
                        .skip(1)
                        .map(|line| line.split('\t').collect::<Vec<_>>())
                        .find(|cells| cells[0].ends_with(s.as_str()) && cells[1] == f)
                        .unwrap_or_else(|| panic!("no row for {s}.{f} in\n{receipt}"));
                    (row[2].to_owned(), row[10].to_owned())
                })
                .collect()
        };
        let mut set = std::collections::BTreeSet::new();
        for owner in &owners {
            let did = tcx
                .hir_body_owners()
                .find(|did| tcx.def_path_str(did.to_def_id()).ends_with(owner.as_str()))
                .unwrap_or_else(|| panic!("owner {owner}"));
            set.insert(super::bridge_receipt::SignatureClassId::of(did));
        }
        (
            read(&table.field_transactions.receipt_tsv(tcx)),
            read(&table.field_transactions.receipt_tsv_at(tcx, &set)),
        )
    })
    .unwrap()
}

/// Witness 28 (relay 042 / R461-5) — the receipt says what the TREE got.
///
/// `status` is PLAN-time and keeps its vocabulary, because every consumer
/// means plan time by it. Beside it, the additive `revert_status` column is
/// written from the FINAL revert set: a transaction whose owner class is
/// reverted is `withdrawn`, because `field_reference_ast::{apply,
/// apply_wraps, apply_hoists}` all iterate `active(&reverts.fns)` and the
/// struct declaration goes inactive with it (report 039 / R460-11). Without
/// this column a post-revert census row reads `applied` for a conversion the
/// program never received — which is how two lanes read one table in
/// opposite directions for three reports.
#[test]
fn w6f_the_receipt_says_what_the_tree_got() {
    let _frame = frame_lock();
    use crate::analyses::borrow_ownership::SlotKind;
    super::test_model_override::set(
        "w6f-moved-out-field-frame",
        vec![("Holder".to_owned(), 0, SlotKind::Owning)],
        Vec::new(),
    );
    let (plan_time, after) = receipt_at_reverts(MOVED_OUT_FIELD, &[("Holder", "buf")], &["run"]);
    super::test_model_override::clear();
    assert_eq!(
        plan_time,
        vec![("applied".to_owned(), "active".to_owned())],
        "nothing is reverted at plan time"
    );
    assert_eq!(
        after,
        vec![("applied".to_owned(), "withdrawn".to_owned())],
        "`run` is this transaction's only owner: reverting it takes the field with it"
    );

    // …and the column reads `active()`'s OWN predicate, not a looser one:
    // a transaction is withdrawn by its DEPENDENT owners, while an owner of
    // only value-independent sites keeps its edits under any revert set.
    //
    // **Re-premised (R538-3).** This read avl's `newNode` as the non-dependent
    // owner. Since ownership-fields' `e780815a8`, `newNode` is a SEAM CONSUMER
    // (its Box literal takes `Node.left`'s delivered form) and joins the key
    // by registration — the ruled direction. The split now lives on lodepng's
    // `LodePNGBitReader.data`, a REFERENCE field: no seam reads a reference
    // field's form, so its non-dependent owners (`ensureBits9`, which carries
    // an element edit, and the mention-only `advanceBits`) stay non-dependent
    // under any registration. The avl case is kept, stating the new fact.
    let (owners, dependent) = transaction_owner_split(LODEPNG, "LodePNGBitReader", "data");
    for non_dependent in ["ensureBits9", "advanceBits"] {
        assert!(
            owners.iter().any(|o| o.ends_with(non_dependent))
                && !dependent.iter().any(|o| o.ends_with(non_dependent)),
            "the fixture must keep {non_dependent} non-dependent for this to be falsifiable: \
             {owners:?} / {dependent:?}"
        );
        let (_, after) =
            receipt_at_reverts(LODEPNG, &[("LodePNGBitReader", "data")], &[non_dependent]);
        assert_eq!(
            after,
            vec![("applied".to_owned(), "active".to_owned())],
            "a non-dependent owner's revert ({non_dependent}) does not withdraw the transaction"
        );
    }
    let (_, after_dependent) = receipt_at_reverts(
        LODEPNG,
        &[("LodePNGBitReader", "data")],
        &["LodePNGBitReader_init"],
    );
    assert_eq!(
        after_dependent,
        vec![("applied".to_owned(), "withdrawn".to_owned())],
        "a dependent owner's revert does"
    );

    // avl, stated as it now is: `newNode` is a registered seam consumer, so
    // its revert withdraws `Node.left` — the atomicity `e780815a8` builds.
    avl_frame();
    let (_, avl_dependent) = transaction_owner_split(AVL, "Node", "left");
    super::test_model_override::clear();
    assert!(
        avl_dependent.iter().any(|o| o.ends_with("newNode")),
        "avl's newNode is in the key as a seam consumer: {avl_dependent:?}"
    );
    avl_frame();
    let (_, after_consumer) = receipt_at_reverts(AVL, &[("Node", "left")], &["newNode"]);
    super::test_model_override::clear();
    assert_eq!(
        after_consumer,
        vec![("applied".to_owned(), "withdrawn".to_owned())],
        "a seam consumer's revert takes the transaction with it"
    );
}

/// `(struct, field) -> (owners, dependent owners)` as path suffixes.
fn transaction_owner_split(
    source: &str,
    struct_name: &str,
    field: &str,
) -> (Vec<String>, Vec<String>) {
    let struct_name = struct_name.to_owned();
    let field = field.to_owned();
    ::utils::compilation::run_compiler_on_str(source, move |tcx| {
        let (table, _ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                A5Mode::PreciseReplay,
                Some(WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .unwrap();
        let t = table
            .field_transactions
            .applied
            .iter()
            .find(|t| t.struct_path.ends_with(struct_name.as_str()) && t.field_name == field)
            .unwrap_or_else(|| panic!("no applied transaction for {struct_name}.{field}"));
        let name = |o: &rustc_hir::def_id::LocalDefId| tcx.def_path_str(o.to_def_id());
        (
            t.owners.iter().map(name).collect::<Vec<_>>(),
            t.dependent_owners.iter().map(name).collect::<Vec<_>>(),
        )
    })
    .unwrap()
}

/// Witness 29 (relay 047 / R469-1) — **the refresh must expand the raw
/// revert set before it writes the column.**
///
/// `batch1314` died on heman with `owner_reverted_but_reads_active:
/// kmRay2IntersectBox`: the column said `active` while `final-reverts` listed
/// the owner. The cause is not `receipt_tsv_at`, which is correct given a
/// set — it is WHICH set reaches it. `apply` / `apply_wraps` / `apply_hoists`
/// run against `reverts.fns`, built from `effective_withheld_classes`, which
/// adds the held classes, the PARTITION closure and this lane's own
/// field-transaction owner closure. The refresh was handed the RAW
/// `reverted`, so a partition-reverted owner never appeared in it.
///
/// This exercises the refresh ITSELF, not its parts: the raw set names one
/// owner, and the column must still read `withdrawn` because the closure
/// carries the transaction. Handing the raw set straight through — the bug —
/// makes it read `active`.
#[test]
fn w6f_the_refresh_expands_the_revert_set() {
    let _frame = frame_lock();
    // The raw set is EMPTY and the class is reverted only through the atom
    // expansion. A refresh that reads the raw set sees nothing to withdraw;
    // the AST layer, which runs against the effective set, withholds the
    // transaction. The column must agree with the AST layer.
    avl_frame();
    let expanded = refreshed_revert_status(AVL, "Node", "left", &[], Some("rightRotate"));
    super::test_model_override::clear();
    assert_eq!(
        expanded, "withdrawn",
        "the refresh expands the raw set before it writes the column"
    );

    // …and the expansion is not a blanket: a class that reaches neither the
    // raw set nor any closure leaves the transaction active.
    avl_frame();
    let untouched = refreshed_revert_status(AVL, "Node", "left", &[], Some("max"));
    super::test_model_override::clear();
    assert_eq!(
        untouched, "active",
        "an unrelated class's revert does not withdraw the transaction"
    );

    // **The dichotomy report 053 owes the note** — re-premised (R538-3). A
    // non-dependent owner's revert leaves the transaction active, exactly as
    // `active()` and `field_reference_ast` treat it: main's
    // `owner-reverted-but-reads-active` shape, through the production refresh.
    // avl's `newNode` carried this until `e780815a8` registered it as a seam
    // consumer; lodepng's `LodePNGBitReader.data` is a REFERENCE field no seam
    // reads, so `ensureBits9` stays a non-dependent owner of it.
    let non_dependent =
        refreshed_revert_status(LODEPNG, "LodePNGBitReader", "data", &["ensureBits9"], None);
    assert_eq!(
        non_dependent, "active",
        "a non-dependent owner's revert does not withdraw the transaction — \
         the withdrawal key is `dependent_owners`, which the receipt now prints"
    );
    // …and the consumer's case, through the same production refresh.
    avl_frame();
    let consumer = refreshed_revert_status(AVL, "Node", "left", &["newNode"], None);
    super::test_model_override::clear();
    assert_eq!(
        consumer, "withdrawn",
        "a registered seam consumer's revert withdraws the transaction"
    );
}

/// Run the production refresh over a decision table and read the column back
/// out of the artifact it writes.
fn refreshed_revert_status(
    source: &str,
    struct_name: &str,
    field: &str,
    reverted_owners: &[&str],
    atom_owner: Option<&str>,
) -> String {
    let struct_name = struct_name.to_owned();
    let field = field.to_owned();
    let owners: Vec<String> = reverted_owners.iter().map(|o| (*o).to_owned()).collect();
    let atom_owner = atom_owner.map(str::to_owned);
    ::utils::compilation::run_compiler_on_str(source, move |tcx| {
        let (table, _ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                A5Mode::PreciseReplay,
                Some(WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .unwrap();
        let mut raw = std::collections::BTreeSet::new();
        for owner in &owners {
            let did = tcx
                .hir_body_owners()
                .find(|did| tcx.def_path_str(did.to_def_id()).ends_with(owner.as_str()))
                .unwrap_or_else(|| panic!("owner {owner}"));
            raw.insert(super::bridge_receipt::SignatureClassId::of(did));
        }
        // The plan carries one owner set per field transaction — built HERE
        // exactly as `plan::of` builds it (`owner_sets()`), so this witness
        // cannot pass against a closure production never constructs.
        let mut plan = super::plan::Plan::default();
        plan.field_transaction_owners = table
            .field_transactions
            .owner_sets()
            .into_iter()
            .map(|owners| {
                owners
                    .into_iter()
                    .map(super::bridge_receipt::SignatureClassId::of)
                    .collect()
            })
            .collect();
        // The atom lever is a production one: `effective_reverted_classes`
        // expands a reverted cursor-base atom into its owner classes, so a
        // refresh handed the RAW set sees an empty revert and the correct one
        // sees the owner. That is R469-1's bug in one step.
        let mut atoms = std::collections::BTreeSet::new();
        if let Some(atom) = atom_owner.as_ref() {
            let did = tcx
                .hir_body_owners()
                .find(|did| tcx.def_path_str(did.to_def_id()).ends_with(atom.as_str()))
                .unwrap_or_else(|| panic!("atom owner {atom}"));
            plan.cursor_base_atom_owners.insert(
                "w6f-atom".to_owned(),
                std::iter::once(super::bridge_receipt::SignatureClassId::of(did)).collect(),
            );
            atoms.insert("w6f-atom".to_owned());
        }
        let mut artifacts = super::RawBoundaryArtifacts::default();
        super::refresh_field_transaction_revert_status(
            &mut artifacts,
            tcx,
            &table,
            &plan,
            &raw,
            &atoms,
        );
        artifacts
            .field_transactions
            .lines()
            .skip(1)
            .map(|line| line.split('\t').collect::<Vec<_>>())
            .find(|cells| cells[0].ends_with(struct_name.as_str()) && cells[1] == field)
            .unwrap_or_else(|| panic!("no row for {struct_name}.{field}"))[10]
            .to_owned()
    })
    .unwrap()
}

/// `(struct, field) -> the owners that receive an expression edit`, as path
/// suffixes. The set the transaction's TEXT actually lands in.
fn transaction_edit_owners(source: &str, struct_name: &str, field: &str) -> Vec<String> {
    let struct_name = struct_name.to_owned();
    let field = field.to_owned();
    ::utils::compilation::run_compiler_on_str(source, move |tcx| {
        let (table, _ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                A5Mode::PreciseReplay,
                Some(WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .unwrap();
        let t = table
            .field_transactions
            .applied
            .iter()
            .find(|t| t.struct_path.ends_with(struct_name.as_str()) && t.field_name == field)
            .unwrap_or_else(|| panic!("no applied transaction for {struct_name}.{field}"));
        let mut owners: Vec<String> = t
            .expression_edits
            .iter()
            .map(|e| tcx.def_path_str(e.owner.to_def_id()))
            .collect();
        owners.sort();
        owners.dedup();
        owners
    })
    .unwrap()
}

/// Witness 30 (relay 055) — **the receipt publishes the set the withdrawal is
/// keyed on.**
///
/// `owners` is `sites ∪ mentions`: every function whose signature so much as
/// names the struct is in it, whether or not it touches the field. The
/// withdrawal — `active()`, and with it `field_reference_ast::{apply,
/// apply_wraps, apply_hoists}` — is keyed on `dependent_owners`, a strict
/// subset. A reader joining a revert set against the printed `owners` gets a
/// disagreement that is not one: that is main's `owner-reverted-but-reads-
/// active` note on lodepng `LodePNGBitReader.data`, whose reverted owner
/// `inflateHuffmanBlock` touches `(*reader).bp` and `.bitsize` and never
/// `data`. The receipt now prints the dependent set as its own ADDITIVE last
/// column, so the join can be made correctly instead of argued about.
#[test]
fn w6f_the_receipt_publishes_the_withdrawal_key() {
    let _frame = frame_lock();
    let (owners, dependent) = transaction_owner_split(LODEPNG, "LodePNGBitReader", "data");
    assert!(
        owners.iter().any(|o| o.ends_with("advanceBits"))
            && !dependent.iter().any(|o| o.ends_with("advanceBits")),
        "the fixture must keep a mention-only owner — the lodepng note's shape: {owners:?} / {dependent:?}"
    );
    let row = field_receipt_row(LODEPNG, "LodePNGBitReader", "data");
    assert_eq!(
        row.len(),
        12,
        "the receipt carries the additive `dependent_owners` column: {row:?}"
    );
    let printed = row[11].clone();
    let expected = dependent
        .iter()
        .map(String::as_str)
        .collect::<Vec<_>>()
        .join(",");
    assert_eq!(
        printed, expected,
        "the column IS `dependent_owners`, in the receipt's own order"
    );
    assert!(
        !printed.contains("advanceBits"),
        "a mention-only owner is not in the withdrawal key: {printed}"
    );
    assert!(
        row[5].contains("advanceBits"),
        "…while `owners` still carries it, which is what a reader was joining on: {}",
        row[5]
    );
}

/// Witness 31 (relay 055) — **the withdrawal key is narrower than the edit
/// set, and that gap is now pinned rather than latent.**
///
/// `ast_transform.rs` inserts a transaction's expression edits under
/// `active(&reverts.fns)` and says "the plan closes the revert set over
/// them" — but the plan's closure (`Plan::field_transaction_owners`) is built
/// from `owner_sets()`, which is `dependent_owners`. Measured here: lodepng's
/// `data` is edited in four functions and depends on ONE, and avl's
/// `Node.left` is edited in seven and depends on six. So an owner can carry
/// this transaction's text and still not be able to withdraw it. This test
/// states the gap exactly; it does not bless it (report 053 STOP 1).
#[test]
fn w6f_the_edit_set_is_wider_than_the_withdrawal_key() {
    let _frame = frame_lock();
    let (_, dependent) = transaction_owner_split(LODEPNG, "LodePNGBitReader", "data");
    let edited = transaction_edit_owners(LODEPNG, "LodePNGBitReader", "data");
    assert_eq!(dependent.len(), 1, "{dependent:?}");
    assert_eq!(edited.len(), 4, "{edited:?}");
    let uncovered: Vec<&String> = edited
        .iter()
        .filter(|o| !dependent.iter().any(|d| d == *o))
        .collect();
    assert_eq!(
        uncovered.len(),
        3,
        "three functions carry the field's text and cannot withdraw it: {uncovered:?}"
    );

    // **Re-premised (R538-3).** On avl the gap is now CLOSED: `newNode` writes
    // the field (`owned-field-raw-store`) and, since `e780815a8`, is also a
    // registered seam consumer, so every owner that carries avl's text can
    // withdraw it. The gap survives on lodepng's REFERENCE field above — the
    // case report 054 measured safe (the revert leaves the span-keyed text).
    avl_frame();
    let (_, avl_dependent) = transaction_owner_split(AVL, "Node", "left");
    super::test_model_override::clear();
    avl_frame();
    let avl_edited = transaction_edit_owners(AVL, "Node", "left");
    super::test_model_override::clear();
    assert!(
        avl_edited.iter().any(|o| o.ends_with("newNode")),
        "avl's `newNode` writes the field: {avl_edited:?}"
    );
    assert!(
        avl_edited
            .iter()
            .all(|o| avl_dependent.iter().any(|d| d == o)),
        "…and on avl every edited owner is now in the key: {avl_edited:?} / {avl_dependent:?}"
    );
}

/// The receipt row for `(struct, field)`, split into cells.
fn field_receipt_row(source: &str, struct_name: &str, field: &str) -> Vec<String> {
    let struct_name = struct_name.to_owned();
    let field = field.to_owned();
    ::utils::compilation::run_compiler_on_str(source, move |tcx| {
        let (table, _ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                A5Mode::PreciseReplay,
                Some(WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .unwrap();
        table
            .field_transactions
            .receipt_tsv(tcx)
            .lines()
            .skip(1)
            .map(|line| line.split('\t').map(str::to_owned).collect::<Vec<String>>())
            .find(|cells| cells[0].ends_with(struct_name.as_str()) && cells[1] == field)
            .unwrap_or_else(|| panic!("no row for {struct_name}.{field}"))
    })
    .unwrap()
}

/// Witness 32 (relay 056 / R501-7) — **report 053 STOP 1, answered: a
/// non-dependent owner's revert reverts that owner's own signature and leaves
/// the transaction's text exactly where it was.**
///
/// The instance is the note's own row: lodepng `LodePNGBitReader.data`
/// delivers `opt-slice-shared`, is edited in four functions and depends on ONE
/// (`LodePNGBitReader_init`). The seat ruled the question before the
/// withdrawal key may be widened: when an owner that carries the text but
/// cannot withdraw it is reverted, does the body show the CONVERTED form (the
/// revert does not restore input bytes) or the RAW form (a tree type-broken
/// against its own declaration)?
///
/// Measured here, three ways: it is the **converted** form. Reverting
/// `ensureBits9` changes exactly its own signature back to `*mut`; the field
/// reads in its body keep `((*reader).data).unwrap()[..]`, which type-checks
/// against the converted declaration through a raw pointer, and the round
/// verifies clean. Reverting the mention-only `advanceBits` — the note's exact
/// shape — likewise touches only that signature and its caller's bridge.
/// Reverting the dependent owner withdraws the whole transaction, declaration
/// included. **So the narrow key is safe and what was wrong is the comment in
/// `ast_transform.rs` that says the plan closes over "its owners".**
#[test]
fn w6f_a_non_dependent_owners_revert_leaves_the_text() {
    let _frame = frame_lock();
    let run = |force: &str| -> (String, usize, usize) {
        if !force.is_empty() {
            // SAFETY: the frame lock serializes the witnesses that set env.
            unsafe { std::env::set_var("CRAT_W6F_FORCE_REVERT", force) };
        }
        let outcome = emitted_with("w6f-054", LODEPNG, &|_| {});
        unsafe { std::env::remove_var("CRAT_W6F_FORCE_REVERT") };
        let (source, emitted_count, reverted_count) = emitted_source(&outcome);
        (source.to_owned(), emitted_count, reverted_count)
    };

    let (base, base_emitted, base_reverted) = run("");
    assert_eq!(
        (base_reverted, base.contains("pub data: Option<&'a [u8]>")),
        (0, true)
    );
    assert!(base.contains("fn ensureBits9(mut reader: &mut LodePNGBitReader"));

    // The non-dependent EDITED owner: its own signature goes back, the
    // transaction's text stays, and the tree still verifies.
    let (edited, edited_emitted, edited_reverted) = run("ensureBits9");
    assert_eq!(edited_reverted, 1, "exactly the forced class reverted");
    assert_eq!(
        edited_emitted,
        base_emitted - 1,
        "and nothing else was lost with it"
    );
    assert!(
        edited.contains("pub data: Option<&'a [u8]>"),
        "the declaration stays converted: the transaction is still active"
    );
    assert!(
        edited.contains("fn ensureBits9(mut reader: *mut LodePNGBitReader"),
        "the reverted owner's own signature is restored"
    );
    let body = edited.split("fn ensureBits9").nth(1).unwrap_or_default();
    let body = &body[..body
        .find("unsafe extern \"C\" fn peekBits")
        .unwrap_or(body.len())];
    assert!(
        body.contains("((*reader).data).unwrap()["),
        "…while the field transaction's text is still there — the revert did \
         NOT restore this function's input bytes: {body}"
    );
    assert!(
        !body.contains("((*reader).data).offset("),
        "…and the raw form is NOT what the body shows: {body}"
    );

    // The mention-only owner — main's note's exact shape.
    let (mention, _, mention_reverted) = run("advanceBits");
    assert_eq!(mention_reverted, 1);
    assert!(
        mention.contains("pub data: Option<&'a [u8]>")
            && mention.contains("fn advanceBits(mut reader: *mut LodePNGBitReader")
            && mention.contains("advanceBits(core::ptr::from_mut(&mut *reader)"),
        "only that signature and its caller's bridge move"
    );

    // The DEPENDENT owner: the whole transaction withdraws, declaration first.
    let (dependent, _, _) = run("LodePNGBitReader_init");
    assert!(
        dependent.contains("pub data: *const u8") && !dependent.contains("Option<&'a [u8]>"),
        "a dependent owner's revert takes the declaration with it"
    );
}

/// Witness 33 (relay 059 / R518-3) — **the second wall behind
/// `quadtree_new::tree`, named and pinned.**
///
/// The CROWN unit `quadtree_new::tree` needs `tree->root` to deliver as an
/// OWNED field: `(*tree).root = quadtree_node_with_bounds()` stores a
/// certified constructor result into the field, and A1 declines the
/// certificate while the field is not owned (`return-certificate-struct-field`).
///
/// era-5c 034b has the first wall: `quadtree::quadtree::field0@d0` is
/// **own-UNSAT** at L01⁵ with a 33-clause core. This witness asks the question
/// behind it — *if the arm matrix flips the model, does the field deliver?* —
/// by standing the override in for the matrix's verdict. It does **not**: the
/// field is then held `argument-consumer-model-raw:quadtree_node_free::node`,
/// because the destructor it is handed to has a model-Raw formal. That formal
/// is itself one of the 61 (`quadtree_node_free::node#1`, era-5c's column), so
/// both walls are upstream of this lane.
///
/// **A RED here is news, not a regression**: it means one of the two walls
/// moved and the unit should be re-costed.
#[test]
fn w6f_quadtree_root_is_held_by_its_consumers_model() {
    let _frame = frame_lock();
    use crate::analyses::borrow_ownership::SlotKind;
    let probe = |kind: SlotKind| -> String {
        super::test_model_override::set(
            "w6f-quadtree-root-frame",
            vec![("quadtree".to_owned(), 0, kind)],
            Vec::new(),
        );
        let observed = observe(QUADTREE_ROOT);
        super::test_model_override::clear();
        observed
            .fields
            .iter()
            .find(|(st, f, ..)| st.ends_with("quadtree") && f == "root")
            .map(|(_, _, status, _, cause)| format!("{status}:{cause}"))
            .unwrap_or_else(|| "<no row>".to_owned())
    };
    assert_eq!(
        probe(SlotKind::Owning),
        "held:argument-consumer-model-raw:quadtree_node_free::node:kind-raw",
        "own-SAT alone does not deliver the field: the destructor's formal is \
         model-Raw, and that formal is era-5c's row in the 61"
    );
    assert_eq!(
        probe(SlotKind::Ref),
        "held:store-source-raw-expression",
        "and the reference form is blocked too — the store's source is a call \
         result, not a subject"
    );
}

/// **Relay 059 / R518-3 probe** — if the analysis ever calls `quadtree.root`
/// Owning, does anything ELSE hold the field? The model override stands in for
/// the arm matrix's verdict, so the answer separates "the analysis is the only
/// wall" from "there is a second one waiting behind it".
#[test]
#[ignore = "relay 059 probe: run with --ignored --nocapture"]
fn w6f_probe_quadtree_root_as_an_owned_field() {
    let _frame = frame_lock();
    use crate::analyses::borrow_ownership::SlotKind;
    for kind in [SlotKind::Owning, SlotKind::Ref] {
        super::test_model_override::set(
            "w6f-quadtree-root-frame",
            vec![("quadtree".to_owned(), 0, kind)],
            Vec::new(),
        );
        let observed = observe(QUADTREE_ROOT);
        super::test_model_override::clear();
        println!("PROBE-059 model={kind:?}");
        for (st, field, status, form, cause) in &observed.fields {
            println!("  ROW {st}.{field} status={status} form={form} cause={cause}");
        }
        if observed.fields.is_empty() {
            println!("  ROW <none>");
        }
    }
}

/// Witness 34 (relay 061 / R523-3) — **the sixth arm's key is the
/// transaction's dependent owners, not the edit's owner.**
///
/// `field_reference_ast` has seventeen `failures.push` sites across its three
/// visitors, and every one becomes an `Err` that degrades the whole program —
/// the defect main's floor fixes on five arms, of which `field:wrap` is the
/// sixth (bst wrote nothing at L01⁵ for exactly this). An arm needs a class to
/// register with `record_graft_held`, and the natural choice — the edit's own
/// owner — is measurably wrong: reverting a non-dependent owner leaves the
/// transaction active and its declaration converted (witness 32), so a site
/// holding its INPUT text would be a raw expression against a converted field
/// type.
///
/// `hold_classes_for_edit` answers with the set that takes the declaration:
/// the transaction's DEPENDENT owners. On lodepng, `ensureBits9` carries a
/// `field-element` edit and is NOT a dependent owner, so asking at its span
/// must return `LodePNGBitReader_init` — and never `ensureBits9`.
#[test]
fn w6f_a_held_edit_withdraws_the_transaction_not_its_owner() {
    let _frame = frame_lock();
    let (named, owner_named) = ::utils::compilation::run_compiler_on_str(LODEPNG, |tcx| {
        let (table, _ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                A5Mode::PreciseReplay,
                Some(WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .unwrap();
        let t = table
            .field_transactions
            .applied
            .iter()
            .find(|t| t.struct_path.ends_with("LodePNGBitReader") && t.field_name == "data")
            .expect("the lodepng transaction");
        // An edit owned by `ensureBits9` — a non-dependent owner.
        let edit = t
            .expression_edits
            .iter()
            .find(|e| {
                tcx.def_path_str(e.owner.to_def_id())
                    .ends_with("ensureBits9")
            })
            .expect("ensureBits9 carries an edit");
        let span = (edit.span.lo().0, edit.span.hi().0);
        let held = table.field_transactions.hold_classes_for_edit(span);
        let name_of = |class: &super::bridge_receipt::SignatureClassId| -> String {
            tcx.hir_body_owners()
                .find(|did| super::bridge_receipt::SignatureClassId::of(*did) == *class)
                .map(|did| tcx.def_path_str(did.to_def_id()))
                .unwrap_or_else(|| "<unknown>".to_owned())
        };
        let mut named: Vec<String> = held.iter().map(name_of).collect();
        named.sort();
        (named, tcx.def_path_str(edit.owner.to_def_id()))
    })
    .unwrap();
    assert!(
        owner_named.ends_with("ensureBits9"),
        "the fixture must keep the non-dependent edited owner: {owner_named}"
    );
    assert_eq!(
        named,
        vec!["LodePNGBitReader_init".to_owned()],
        "holding an edit withdraws the transaction through its dependent owner"
    );
    assert!(
        !named.iter().any(|n| n.ends_with("ensureBits9")),
        "…and never the edit's own owner, which cannot withdraw it: {named:?}"
    );
}

/// Witness 35 (relay 064 / R528-2) — **defect B of report 059 is reachable in
/// the commonest C owned-field idiom, not merely representable.**
///
/// `s->buf = malloc(n); if (!s->buf) …; free(s->buf);` — every site is a store
/// of a call result, a NULL test, or a cast into the deallocator, none of which
/// is a `dependent_owners` kind, and no function stores a parameter into the
/// field. So the transaction is APPLIED (`opt-box`), all three of its edits
/// are WRAPS, and its withdrawal key is EMPTY. Two consequences follow, and
/// this witness pins the fact both rest on:
///
/// * the sixth arm (`49adca944`) registers `dependent_owners` when a wrap's
///   claim is refused; on this transaction that loop registers NOTHING, writes
///   no receipt, still balances `placed + held`, and leaves the transaction
///   active with one site un-wrapped — a silent half-composition;
/// * `FieldTransactions::active` is vacuously true for an empty key, so no
///   revert can ever withdraw this transaction.
///
/// A RED here is news: it means the dependent set is no longer empty on the
/// commonest shape, and the arm's fallback question changes with it.
#[test]
fn w6f_malloc_free_field_has_an_empty_withdrawal_key() {
    let _frame = frame_lock();
    use crate::analyses::borrow_ownership::SlotKind;
    super::test_model_override::set(
        "w6f-malloc-free-field-frame",
        vec![("holder".to_owned(), 0, SlotKind::Owning)],
        Vec::new(),
    );
    let (form, dependent, edits) =
        ::utils::compilation::run_compiler_on_str(MALLOC_FREE_FIELD, |tcx| {
            let (table, _ctx) = super::decide_table_with_ctx_config(
                tcx,
                Some((
                    A5Mode::PreciseReplay,
                    Some(WholeProgramAttestation::FrozenBenchmarkGraph),
                )),
            )
            .unwrap();
            let t = table
                .field_transactions
                .applied
                .iter()
                .find(|t| t.struct_path.ends_with("holder") && t.field_name == "buf")
                .expect("the malloc/free field is an applied transaction");
            let mut edits: Vec<(String, bool)> = t
                .expression_edits
                .iter()
                .map(|e| (e.kind.to_owned(), e.wrap))
                .collect();
            edits.sort();
            (
                t.delivered_form_key().to_owned(),
                t.dependent_owners.len(),
                edits,
            )
        })
        .unwrap();
    super::test_model_override::clear();
    assert_eq!(form, "opt-box", "the transaction delivers");
    assert_eq!(
        dependent, 0,
        "…and its withdrawal key is EMPTY: no revert can withdraw it, and a \
         held wrap has no class to register"
    );
    assert_eq!(
        edits,
        vec![
            ("owned-field-dealloc-transfer".to_owned(), true),
            ("owned-field-is-null".to_owned(), true),
            ("owned-field-store".to_owned(), true),
        ],
        "every edit it owns is a WRAP — each one a site the sixth arm can hold"
    );
}

/// Witness 36 (R531-7, wave-6a 077 §1) — **a write one projection below an
/// owned field's deref takes the MUTABLE view.**
///
/// `(*(*t).entries).key = 3` rendered `(*(*t).entries.as_deref().unwrap()).key
/// = 3` — E0594, assignment through `&` — and the program failed to emit
/// ("2 errors attributed to no rewritten function"). The deref site's
/// `written` flag asked only whether the DEREF was an assignment's left side;
/// here its parent is the `.key` projection. A place is written when it is the
/// left side of `=` or of a compound assignment, or the operand of `&mut`,
/// after climbing any field / index projections. The read in `table_get` keeps
/// the shared view — that is the control that the fix is not "always mut".
#[test]
fn w6f_a_write_below_an_owned_field_deref_takes_the_mutable_view() {
    let _frame = frame_lock();
    use crate::analyses::borrow_ownership::SlotKind;
    let set = || {
        super::test_model_override::set(
            "w6f-owned-subfield-write-frame",
            vec![("table".to_owned(), 0, SlotKind::Owning)],
            Vec::new(),
        )
    };
    set();
    let observed = observe(OWNED_SUBFIELD_WRITE);
    let row = field_row(&observed, "table", "entries");
    assert_eq!(
        (row.2.as_str(), row.3.as_str()),
        ("applied", "opt-box"),
        "the owned field delivers: {row:?}"
    );
    let outcome = emitted("owned-subfield-write", OWNED_SUBFIELD_WRITE);
    super::test_model_override::clear();
    let (source, emitted_count, reverted) = emitted_source(&outcome);
    // CODE only: the fixture's doc comment quotes the E0594 rendering verbatim,
    // and a check that reads comments passes or fails on prose.
    let flat: String = source
        .lines()
        .filter(|line| !line.trim_start().starts_with("//"))
        .flat_map(str::split_whitespace)
        .collect::<Vec<_>>()
        .join(" ");
    for needle in [
        "(*(*t).entries.as_deref_mut().unwrap()).key = 3",
        "(*(*t).entries.as_deref_mut().unwrap()).value += 1",
        "return (*(*t).entries.as_deref().unwrap()).key;",
    ] {
        assert!(flat.contains(needle), "missing {needle:?} in\n{source}");
    }
    assert!(
        !flat.contains("(*(*t).entries.as_deref().unwrap()).key = 3"),
        "the E0594 rendering is gone"
    );
    assert_eq!(reverted, 0, "the tree compiles: nothing reverted\n{source}");
    assert!(emitted_count > 0, "{source}");
}

/// Claim every expression whose span is one of `spans` for an incumbent
/// claimant, so the field-transaction wraps that follow are REFUSED — the
/// collision the sixth arm exists for, constructed rather than waited for.
struct IncumbentClaims<'a> {
    spans: &'a rustc_hash::FxHashSet<(u32, u32)>,
    guard: &'a mut super::ast_transform::Composition,
    claimed: usize,
}

impl rustc_ast::mut_visit::MutVisitor for IncumbentClaims<'_> {
    fn visit_expr(&mut self, e: &mut rustc_ast::Expr) {
        rustc_ast::mut_visit::walk_expr(self, e);
        if self.spans.contains(&(e.span.lo().0, e.span.hi().0))
            && self.guard.claim(e.id, e.span, "w6f-test:incumbent")
        {
            self.claimed += 1;
        }
    }
}

/// Run `apply_wraps` on `source` with every wrap node of `(struct, field)`
/// already claimed by an incumbent. Returns the result, how many nodes the
/// incumbent took, and the classes the round registered as held.
fn wraps_under_incumbent(
    source: &str,
    struct_name: &str,
    field: &str,
) -> (Result<(), String>, usize, usize) {
    let struct_name = struct_name.to_owned();
    let field = field.to_owned();
    ::utils::compilation::run_compiler_on_str(source, move |tcx| {
        // The expanded AST FIRST: deciding the table lowers the crate and
        // steals the resolver's copy of it.
        let mut krate = ::utils::ast::expanded_ast(tcx);
        let (table, _ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                A5Mode::PreciseReplay,
                Some(WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .unwrap();
        let t = table
            .field_transactions
            .applied
            .iter()
            .find(|t| t.struct_path.ends_with(struct_name.as_str()) && t.field_name == field)
            .unwrap_or_else(|| panic!("no applied transaction for {struct_name}.{field}"));
        let spans: rustc_hash::FxHashSet<(u32, u32)> = t
            .expression_edits
            .iter()
            .filter(|e| e.wrap)
            .map(|e| (e.span.lo().0, e.span.hi().0))
            .collect();
        let mut guard = super::ast_transform::Composition::default();
        let mut incumbent = IncumbentClaims {
            spans: &spans,
            guard: &mut guard,
            claimed: 0,
        };
        rustc_ast::mut_visit::MutVisitor::visit_crate(&mut incumbent, &mut krate);
        let claimed = incumbent.claimed;
        super::ast_transform::reset_graft_held();
        let result = super::field_reference_ast::apply_wraps(
            &table,
            &super::ast_transform::RevertSet::default(),
            &mut krate,
            &mut guard,
        );
        (
            result,
            claimed,
            super::ast_transform::graft_held_classes().len(),
        )
    })
    .unwrap()
}

/// Witness 37 (R531-7, wave-6f 061 defect B) — **a refused wrap on a
/// transaction with NO withdrawal key fails loud; one WITH a key yields.**
///
/// The sixth arm holds a refused `field:wrap` by registering the transaction's
/// `dependent_owners`, so the next round withdraws it whole. On the commonest
/// owned-field idiom that set is EMPTY (witness 35): the loop registered
/// nothing, wrote no receipt, still balanced `placed + held`, and `apply_wraps`
/// returned `Ok` — the transaction shipped half-wrapped, silently. No key can
/// withdraw it (`active` is vacuously true for an empty key), so the one sound
/// answer is the one the file had before the arm: a failure the program sees,
/// `wrap-claim-refused-no-key:<span>`.
///
/// Both halves are driven here by an incumbent that claims every wrap node
/// first: the empty-key transaction must fail loud, and avl's `Node.left` —
/// six dependent owners — must still YIELD, holding its classes and returning
/// `Ok`, so the branch cannot be mistaken for undoing the arm.
#[test]
fn w6f_a_refused_wrap_with_no_withdrawal_key_fails_loud() {
    let _frame = frame_lock();
    use crate::analyses::borrow_ownership::SlotKind;
    super::test_model_override::set(
        "w6f-malloc-free-field-frame",
        vec![("holder".to_owned(), 0, SlotKind::Owning)],
        Vec::new(),
    );
    let (no_key, no_key_claimed, no_key_held) =
        wraps_under_incumbent(MALLOC_FREE_FIELD, "holder", "buf");
    super::test_model_override::clear();
    assert!(
        no_key_claimed > 0,
        "the incumbent must take a wrap node for this to test anything"
    );
    let why = no_key
        .expect_err("an empty withdrawal key cannot hold: the refusal must reach the program");
    assert!(
        why.contains("wrap-claim-refused-no-key:"),
        "the failure names the missing key, not a generic refusal: {why}"
    );
    assert_eq!(no_key_held, 0, "nothing was registered as held");

    avl_frame();
    let (keyed, keyed_claimed, keyed_held) = wraps_under_incumbent(AVL, "Node", "left");
    super::test_model_override::clear();
    assert!(
        keyed_claimed > 0,
        "the incumbent must take a wrap node on avl too"
    );
    assert_eq!(
        keyed,
        Ok(()),
        "a transaction WITH a withdrawal key still yields — the branch is not the arm undone"
    );
    assert!(
        keyed_held > 0,
        "…and it registers its dependent owners as held"
    );
}

/// Witness 38 (R533-3, relay 066) — **a field transaction withdraws
/// atomically: a registered seam consumer is part of its withdrawal key.**
///
/// bst at L01⁶ (measured live on `l01p6`'s head, report 063): `insert::node`
/// degrades, `insert` is withheld, and the closure withdraws the `node.left` /
/// `node.right` transactions — declarations back to `*mut node`. But
/// ownership-fields' plan for `newNode::temp` had rendered
/// `Box::new(node { left: None, right: None })` from the seam's plan-time
/// answer, and `newNode` is not a dependent owner (its only sites are null
/// stores), so that literal survived: `E0308 expected *mut node, found
/// Option<_>`, every class reverted.
///
/// On the bst shape (`left`/`right` Owning by the frame): BEFORE registration
/// `newNode` can neither withdraw the transaction nor be pulled into the
/// closure when `insert` is withheld — the half-application's precondition.
/// AFTER `register_seam_consumer(node, left|right, newNode)` both hold, so a
/// consumer's edit and the transaction's edits ship together or not at all.
#[test]
fn w6f_a_seam_consumer_withdraws_with_its_transaction() {
    let _frame = frame_lock();
    bst_frame();
    let (before, after, unknown) = ::utils::compilation::run_compiler_on_str(BST, |tcx| {
        let (mut table, _ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                A5Mode::PreciseReplay,
                Some(WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .unwrap();
        let fn_named = |name: &str| {
            tcx.hir_body_owners()
                .find(|did| tcx.def_path_str(did.to_def_id()).ends_with(name))
                .unwrap_or_else(|| panic!("fn {name}"))
        };
        let (new_node, insert) = (fn_named("newNode"), fn_named("insert"));
        let node = table
            .field_transactions
            .applied
            .iter()
            .find(|t| t.struct_path.ends_with("node") && t.field_name == "left")
            .expect("the bst frame applies node.left")
            .key
            .struct_did
            .to_def_id();
        // What the round would withhold, and whether the transactions stay.
        let observe = |table: &super::decision::DecisionTable| -> (usize, bool) {
            let one: rustc_hash::FxHashSet<_> = std::iter::once(new_node).collect();
            let active_under_new_node = table.field_transactions.active(&one).count();
            let mut plan = super::plan::Plan::default();
            plan.field_transaction_owners = table
                .field_transactions
                .owner_sets()
                .into_iter()
                .map(|owners| {
                    owners
                        .into_iter()
                        .map(super::bridge_receipt::SignatureClassId::of)
                        .collect()
                })
                .collect();
            let raw =
                std::iter::once(super::bridge_receipt::SignatureClassId::of(insert)).collect();
            let effective =
                super::effective_withheld_classes(&plan, &raw, &std::collections::BTreeSet::new());
            (
                active_under_new_node,
                effective.contains(&super::bridge_receipt::SignatureClassId::of(new_node)),
            )
        };
        let before = observe(&table);
        for field_index in [1, 2] {
            assert!(
                table
                    .field_transactions
                    .register_seam_consumer(node, field_index, new_node),
                "a transaction owns node field {field_index}"
            );
        }
        let after = observe(&table);
        let unknown = table
            .field_transactions
            .register_seam_consumer(node, 0, new_node);
        (before, after, unknown)
    })
    .unwrap();
    super::test_model_override::clear();
    assert_eq!(
        before,
        (2, false),
        "the half-application's precondition: newNode's revert leaves both \
         transactions active, and withholding insert does not pull newNode in"
    );
    assert_eq!(
        after,
        (0, true),
        "a registered consumer withdraws the transactions, and is withdrawn with them"
    );
    assert!(
        !unknown,
        "no transaction owns node.key: nothing is registered"
    );
}

/// Witness 39 (R538-3) — **the hoist absorbs ONLY the preceding assignment
/// of the same read, through a pure place.** The value argument holds for
/// exactly that shape: `P = R` stores `R`'s own value if `P` is `R`'s place
/// and touches nothing `R` reads otherwise, and a pure `P` has no effect to
/// observe. Each control breaks one condition and must leave the order alone.
#[test]
fn w6f_the_hoist_absorbs_only_the_same_read_through_a_pure_place() {
    let _frame = frame_lock();
    let cases = ::utils::compilation::run_compiler_on_str("fn main() {}", |_tcx| {
        let order = |previous: &str, read: &str, address_taken: &[&str]| -> bool {
            let mut statements: thin_vec::ThinVec<rustc_ast::Stmt> = thin_vec::ThinVec::new();
            statements.push(::utils::ast::parse_stmt(previous.to_owned()));
            statements.push(::utils::ast::parse_stmt(format!(
                "let __crat_hoist0 = {read};"
            )));
            let generated: rustc_hash::FxHashSet<String> =
                std::iter::once("__crat_hoist0".to_owned()).collect();
            let address_taken: rustc_hash::FxHashSet<String> = address_taken
                .iter()
                .map(|name| (*name).to_owned())
                .collect();
            super::field_reference_ast::absorb_preceding_same_read(
                &mut statements,
                &generated,
                &address_taken,
            );
            matches!(statements[0].kind, rustc_ast::StmtKind::Let(_))
        };
        vec![
            (
                "same read, pure place",
                order("(*root).key = (*t).key;", "(*t).key", &[]),
            ),
            (
                "a different value",
                order("(*root).key = (*u).key;", "(*t).key", &[]),
            ),
            (
                "a compound assignment",
                order("(*root).key += (*t).key;", "(*t).key", &[]),
            ),
            (
                "a place that calls",
                order("(*pick(root)).key = (*t).key;", "(*t).key", &[]),
            ),
            // The write lands in a local the read goes through: `p` moves on.
            (
                "the write is the read's own local",
                order("p = (*p).next;", "(*p).next", &[]),
            ),
            // A write through memory can reach `t` only through its address.
            (
                "the read's local is address-taken",
                order("(*root).key = (*t).key;", "(*t).key", &["t"]),
            ),
            // The read goes through memory the write may reach.
            (
                "the read derefs through memory",
                order("(*root).key = (*(*a).b).key;", "(*(*a).b).key", &[]),
            ),
        ]
    })
    .unwrap();
    assert_eq!(
        cases,
        vec![
            ("same read, pure place", true),
            ("a different value", false),
            ("a compound assignment", false),
            ("a place that calls", false),
            ("the write is the read's own local", false),
            ("the read's local is address-taken", false),
            ("the read derefs through memory", false),
        ]
    );
}

/// Witness 40 (R538-3): the names the absorption treats as reachable through
/// memory — an `&`/`&raw` operand's root, a method receiver's (autoref), any
/// name a closure mentions — and NOT a root behind a deref (`&mut (*p).f`
/// takes the pointee's address, not `p`'s).
#[test]
fn w6f_the_absorption_reads_address_taken_names_crate_wide() {
    let _frame = frame_lock();
    let names = ::utils::compilation::run_compiler_on_str("fn main() {}", |_tcx| {
        let krate = ::utils::ast::parse_crate(
            "unsafe fn f(p: *mut S, mut a: [i32; 2], mut x: i32, y: i32, z: i32) {\n\
             let q = &mut x; let r = a.as_mut_ptr(); let c = || y + 1;\n\
             let s = &mut (*p).f; let t = z; }"
                .to_owned(),
        );
        let mut names: Vec<String> = super::field_reference_ast::address_taken_names(&krate)
            .into_iter()
            .collect();
        names.sort();
        names
    })
    .unwrap();
    assert_eq!(names, ["a", "x", "y"]);
}
