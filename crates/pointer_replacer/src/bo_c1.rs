//! C1-lite corpus runner for the experimental BO (borrow_ownership) analysis.
//!
//! Harness and test-only diagnostic hooks: production analysis semantics stay
//! untouched. Runs BO exactly as
//! `tests::borrow_ownership_coherence::assert_ownership_parity` constructs it
//! (tests.rs `collect_program` → `CrateSlots::build` → `CrateCtxt::new` →
//! `KindSolver::new` → `emit_crate_ownership_constraints` → per-fn
//! `add_coherence` → fixpoint with `is_mutable = true`) over the CROWN/Laertes
//! benchmark programs in `benchmarks/rs-crown/`, and reports per program: wall-clock,
//! CEGAR rounds + commits, Ref/Raw/Owning counts, leaked sources, and
//! decline/timeout/oom/panic classification. Also runs the production borrow
//! baseline (`demote_pointers_iterative_with_fields` from all-Ref, the same
//! independent driver `assert_borrow_parity` uses) for the BO-vs-prod Ref delta.
//!
//! §NB5-M — NATIVE COUNTERS (mirror retired). The BO fork's
//! `borrow_ownership::borrow_verify::verify_to_fixpoint_counting` exposes the round/commit/leak
//! counters directly (`RoundStats`); `verify_to_fixpoint` is its model-only wrapper. The fork is
//! NOT under the `analyses/**` freeze, so the old "mirror over instrumentation" tradeoff (a counter
//! would break the frozen diff audit) never applied here. The former verbatim MIRROR of the loop
//! (`mirror::verify_to_fixpoint_counting`) is DELETED — its parity was proven at the NB5-M gate
//! (native == mirror, byte-identical to the NB5-Z baseline on all 19 accepts, both profiles) before
//! retirement. Wrapper-thinness (no logic added to the wrapper that would diverge the sweep's
//! counters from what the suite verifies) is now guarded by `verify_to_fixpoint_is_thin_wrapper`.
//!
//! Entry points (all `#[ignore]`d except the guards):
//!   worker:      CRAT_BOC1_INPUT=<crate-root.rs> [CRAT_BOC1_MODE=bo|prod]
//!                cargo test -p pointer_replacer --release bo_c1::boc1_run_one \
//!                  -- --exact --ignored --nocapture
//!   orchestrator: cargo test -p pointer_replacer --release bo_c1::boc1_corpus \
//!                  -- --exact --ignored --nocapture
//!                env: CRAT_BOC1_PROGRAMS=a,b,c  CRAT_BOC1_TIMEOUT_SECS=900
//!                     CRAT_BOC1_PROD_TIMEOUT_SECS=900  CRAT_BOC1_PROD=0
//!                     CRAT_BOC1_MEM_MB=8192  CRAT_BOC1_OUT=<dir>

use rustc_hir::{ItemKind, OwnerNode};
use rustc_middle::ty::TyCtxt;

use self::ownership_diagnostic_package::{
    AssumeSite, BoxDecisionEvidence, FunctionPrecisionRecord, NecessityEvidence,
    ProductionPrecisionEvidence,
};
use crate::{analyses::borrow_ownership::solver::CORE_LABEL_FAMILIES, utils::rustc::RustProgram};

/// Copy of tests.rs `borrow_ownership_coherence::collect_program` (kept local so
/// tests.rs stays untouched): every top-level fn/struct item, in HIR owner order.
fn collect_program(tcx: TyCtxt<'_>) -> RustProgram<'_> {
    let mut functions = Vec::new();
    let mut structs = Vec::new();
    for maybe_owner in tcx.hir_crate(()).owners.iter() {
        let Some(owner) = maybe_owner.as_owner() else {
            continue;
        };
        let OwnerNode::Item(item) = owner.node() else {
            continue;
        };
        match item.kind {
            ItemKind::Fn { .. } => functions.push(item.owner_id.def_id),
            ItemKind::Struct(..) => structs.push(item.owner_id.def_id),
            _ => {}
        }
    }

    RustProgram {
        tcx,
        functions,
        structs,
    }
}

/// Ordered key=value row. Generic on purpose (crude harness): the worker emits
/// whatever metrics its mode produced; the orchestrator/table render `-` for
/// missing keys. Keys and values must be space-free (see `sanitize`).
mod report {
    #[derive(Clone, Debug, Default, PartialEq)]
    pub struct Row(pub Vec<(String, String)>);

    pub const SENTINEL: &str = "BOC1 ";

    impl Row {
        pub fn get(&self, key: &str) -> Option<&str> {
            self.0
                .iter()
                .find(|(k, _)| k == key)
                .map(|(_, v)| v.as_str())
        }

        /// Insert or replace. Values are sanitized to keep the KV line parseable.
        pub fn set(&mut self, key: &str, value: impl ToString) {
            let value = sanitize(&value.to_string());
            match self.0.iter_mut().find(|(k, _)| k == key) {
                Some((_, v)) => *v = value,
                None => self.0.push((key.to_string(), value)),
            }
        }
    }

    /// Space/quote/newline-free so one row is exactly one whitespace-split line.
    pub fn sanitize(v: &str) -> String {
        let mut s: String = v
            .chars()
            .map(|c| {
                if c.is_whitespace() || c == '"' || c == '=' {
                    '_'
                } else {
                    c
                }
            })
            .collect();
        s.truncate(120);
        s
    }

    pub fn to_kv_line(row: &Row) -> String {
        let body: Vec<String> = row.0.iter().map(|(k, v)| format!("{k}={v}")).collect();
        format!("{SENTINEL}{}", body.join(" "))
    }

    pub fn parse_kv_line(line: &str) -> Option<Row> {
        let body = line.trim().strip_prefix(SENTINEL)?;
        let mut row = Row::default();
        for tok in body.split_whitespace() {
            let (k, v) = tok.split_once('=')?;
            row.0.push((k.to_string(), v.to_string()));
        }
        Some(row)
    }

    /// One JSON object per row; values that parse as finite numbers are unquoted.
    pub fn to_json_line(row: &Row) -> String {
        let body: Vec<String> = row
            .0
            .iter()
            .map(|(k, v)| {
                let numeric = v.parse::<f64>().map(|x| x.is_finite()).unwrap_or(false);
                if numeric {
                    format!("\"{k}\":{v}")
                } else {
                    format!("\"{k}\":\"{v}\"")
                }
            })
            .collect();
        format!("{{{}}}", body.join(","))
    }

    pub fn render_markdown(rows: &[Row], cols: &[&str]) -> String {
        let mut out = String::new();
        out.push_str(&format!("| {} |\n", cols.join(" | ")));
        out.push_str(&format!("|{}\n", "---|".repeat(cols.len())));
        for row in rows {
            let cells: Vec<&str> = cols.iter().map(|c| row.get(c).unwrap_or("-")).collect();
            out.push_str(&format!("| {} |\n", cells.join(" | ")));
        }
        out
    }

    /// Header = union of keys in first-appearance order; missing cells empty.
    pub fn render_csv(rows: &[Row]) -> String {
        let mut cols: Vec<String> = Vec::new();
        for row in rows {
            for (k, _) in &row.0 {
                if !cols.iter().any(|c| c == k) {
                    cols.push(k.clone());
                }
            }
        }
        let mut out = String::new();
        out.push_str(&cols.join(","));
        out.push('\n');
        for row in rows {
            let cells: Vec<&str> = cols.iter().map(|c| row.get(c).unwrap_or("")).collect();
            out.push_str(&cells.join(","));
            out.push('\n');
        }
        out
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        fn sample() -> Row {
            let mut r = Row::default();
            r.set("program", "bst");
            r.set("mode", "bo");
            r.set("status", "ok");
            r.set("rounds", 3usize);
            r.set("t_fixpoint_s", format!("{:.3}", 0.5f64));
            r
        }

        #[test]
        fn boc1_kv_roundtrip() {
            let row = sample();
            let line = to_kv_line(&row);
            assert!(line.starts_with(SENTINEL));
            assert_eq!(parse_kv_line(&line).expect("parse"), row);
            // Sanitizer keeps hostile values single-token (so the line stays parseable).
            let mut hostile = Row::default();
            hostile.set("err", "two words \"quoted\" a=b");
            let line = to_kv_line(&hostile);
            let back = parse_kv_line(&line).expect("parse sanitized");
            assert_eq!(back.0.len(), 1);
            assert!(!back.get("err").unwrap().contains(' '));
            // Non-sentinel and malformed lines are rejected, not misparsed.
            assert_eq!(parse_kv_line("running 1 test"), None);
            assert_eq!(parse_kv_line("BOC1 novalue"), None);
        }

        #[test]
        fn boc1_report_format() {
            let full = sample();
            let mut sparse = Row::default();
            sparse.set("program", "brotli");
            sparse.set("mode", "bo");
            sparse.set("status", "timeout");
            let md = render_markdown(
                &[full.clone(), sparse.clone()],
                &["program", "status", "rounds"],
            );
            assert!(md.contains("| bst | ok | 3 |"));
            assert!(
                md.contains("| brotli | timeout | - |"),
                "missing cells render `-`:\n{md}"
            );
            let json = to_json_line(&full);
            assert!(json.contains("\"rounds\":3"), "numbers unquoted: {json}");
            assert!(json.contains("\"status\":\"ok\""), "strings quoted: {json}");
            let csv = render_csv(&[full, sparse]);
            let mut lines = csv.lines();
            assert_eq!(
                lines.next(),
                Some("program,mode,status,rounds,t_fixpoint_s")
            );
            assert_eq!(lines.next(), Some("bst,bo,ok,3,0.500"));
            assert_eq!(lines.next(), Some("brotli,bo,timeout,,"));
        }
    }
}

// Compile the registered inventory walker itself into this measurement harness.
// This deliberately avoids a copied/reimplemented definition of the 2,414-row
// official universe.
#[allow(dead_code)]
mod crown_artifact_walker {
    include!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tools/crown_artifact_inventory/src/lib.rs"
    ));
}

mod crown_projection {
    use std::{
        collections::{BTreeMap, BTreeSet},
        ffi::OsStr,
        fs,
        path::{Path, PathBuf},
    };

    use rustc_hash::{FxHashMap, FxHashSet};
    use rustc_index::bit_set::DenseBitSet;
    use rustc_middle::{
        mir::{Local, VarDebugInfoContents},
        ty::TyCtxt,
    };
    use rustc_span::def_id::LocalDefId;

    use super::{
        crown_artifact_walker::{
            OfficialEvaluation, analyze_json_claims, analyze_named_rust_sources,
            parse_official_evaluation,
        },
        report,
    };
    use crate::{
        analyses::{
            borrow_ownership::{
                SlotKind, crate_slots::CrateSlots, slots::SlotOwner, solver::SlotRef,
            },
            mir_variable_grouping::SourceVarGroups,
        },
        utils::rustc::RustProgram,
    };

    pub const MODEL_LABEL: &str = "model-level projection, pre-rewriter UPPER BOUND — not realized conversion; emission arrives with the BO rewriter.";
    pub const LEGACY_LABEL: &str =
        "legacy decision-layer PREDICTED, pre-transform UPPER BOUND; not realized conversion";
    pub const CROWN_LABEL: &str = "CROWN realized, emitted-output official metric";

    pub fn audit_text(value: impl ToString) -> String {
        value.to_string().replace('\0', "\\0")
    }

    pub fn csv_cell(value: impl ToString) -> String {
        let value = audit_text(value);
        if value.contains([',', '"', '\n']) {
            format!("\"{}\"", value.replace('"', "\"\""))
        } else {
            value
        }
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum MappingCompleteness {
        Empty,
        Partial,
        Complete,
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum ModelKind {
        Raw,
        Ref,
        Owning,
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum LegacyDecisionKind {
        Ref,
        OptRef,
        Slice,
        SliceCursor,
        Box,
        OptBox,
        BoxedSlice,
        OptBoxedSlice,
        Raw,
        Other,
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum LegacyBackingKind {
        BoxFamily,
        RefSlice,
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct BoFullScopeCounts {
        pub program: String,
        pub slots_total: usize,
        pub n_ref: usize,
        pub n_own: usize,
        pub n_raw: usize,
        pub n_ref_d0: usize,
        pub n_own_d0: usize,
        pub n_raw_d0: usize,
    }

    impl BoFullScopeCounts {
        pub fn d0_local_slots(&self) -> usize {
            self.n_ref_d0 + self.n_own_d0 + self.n_raw_d0
        }
    }

    pub const BO_FULL_SCOPE_CSV_HEADER: &str = "program,profile,scope_row,universe_definition,slots_total,n_ref,n_own,n_raw,raw_share_percent,partition_identity\n";

    #[derive(Clone, Debug, Default, PartialEq, Eq)]
    pub struct LegacyFullScopeHistogram {
        pub ref_false: usize,
        pub ref_true: usize,
        pub opt_ref_false: usize,
        pub opt_ref_true: usize,
        pub slice_false: usize,
        pub slice_true: usize,
        pub slice_cursor_false: usize,
        pub slice_cursor_true: usize,
        pub r#box: usize,
        pub opt_box: usize,
        pub boxed_slice: usize,
        pub opt_boxed_slice: usize,
        pub raw_false: usize,
        pub raw_true: usize,
        pub none: usize,
    }

    impl LegacyFullScopeHistogram {
        pub fn ref_count(&self) -> usize {
            self.ref_false + self.ref_true
        }

        pub fn opt_ref_count(&self) -> usize {
            self.opt_ref_false + self.opt_ref_true
        }

        pub fn slice_count(&self) -> usize {
            self.slice_false + self.slice_true
        }

        pub fn slice_cursor_count(&self) -> usize {
            self.slice_cursor_false + self.slice_cursor_true
        }

        pub fn box_family_count(&self) -> usize {
            self.r#box + self.opt_box + self.boxed_slice + self.opt_boxed_slice
        }

        pub fn subjects_total(&self) -> usize {
            self.ref_count()
                + self.opt_ref_count()
                + self.slice_count()
                + self.slice_cursor_count()
                + self.box_family_count()
                + self.raw_false
                + self.raw_true
                + self.none
        }

        pub fn add_assign(&mut self, other: &Self) {
            self.ref_false += other.ref_false;
            self.ref_true += other.ref_true;
            self.opt_ref_false += other.opt_ref_false;
            self.opt_ref_true += other.opt_ref_true;
            self.slice_false += other.slice_false;
            self.slice_true += other.slice_true;
            self.slice_cursor_false += other.slice_cursor_false;
            self.slice_cursor_true += other.slice_cursor_true;
            self.r#box += other.r#box;
            self.opt_box += other.opt_box;
            self.boxed_slice += other.boxed_slice;
            self.opt_boxed_slice += other.opt_boxed_slice;
            self.raw_false += other.raw_false;
            self.raw_true += other.raw_true;
            self.none += other.none;
        }
    }

    pub const LEGACY_FULL_SCOPE_CSV_HEADER: &str = "program,measurement_status,universe_definition,subjects_total,Ref,OptRef,Slice,SliceCursor,Box,OptBox,BoxedSlice,OptBoxedSlice,Raw_false,Raw_true,None,safe_total,Box_family_total,raw_total,partition_identity\n";

    pub fn bo_full_scope_csv_rows(
        profile: &str,
        counts: &BoFullScopeCounts,
    ) -> Result<String, String> {
        let mut output = String::new();
        for (scope_row, universe, slots_total, n_ref, n_own, n_raw) in [
            (
                "all slots",
                "BO local + field slots at all pointer depths",
                counts.slots_total,
                counts.n_ref,
                counts.n_own,
                counts.n_raw,
            ),
            (
                "d0 local slots",
                "BO depth-0 local slots only; fields excluded",
                counts.d0_local_slots(),
                counts.n_ref_d0,
                counts.n_own_d0,
                counts.n_raw_d0,
            ),
        ] {
            if n_ref + n_own + n_raw != slots_total {
                return Err(format!(
                    "{} {profile} {scope_row}: kind partition does not reconcile",
                    counts.program
                ));
            }
            let raw_share = if slots_total == 0 {
                "0.00".to_owned()
            } else {
                format!("{:.2}", n_raw as f64 * 100.0 / slots_total as f64)
            };
            let row = [
                counts.program.clone(),
                profile.to_owned(),
                scope_row.to_owned(),
                universe.to_owned(),
                slots_total.to_string(),
                n_ref.to_string(),
                n_own.to_string(),
                n_raw.to_string(),
                raw_share,
                "PASS: n_ref + n_own + n_raw = slots_total".to_owned(),
            ];
            output.push_str(&row.into_iter().map(csv_cell).collect::<Vec<_>>().join(","));
            output.push('\n');
        }
        Ok(output)
    }

    pub fn legacy_full_scope_csv_row(
        program: &str,
        status: &str,
        counts: Option<&LegacyFullScopeHistogram>,
    ) -> Result<String, String> {
        let mut row = vec![
            program.to_owned(),
            status.to_owned(),
            "all legacy pre-transform decision subjects; final decision kind".to_owned(),
        ];
        if let Some(counts) = counts {
            let safe_total = counts.ref_count()
                + counts.opt_ref_count()
                + counts.slice_count()
                + counts.slice_cursor_count()
                + counts.box_family_count();
            let raw_total = counts.raw_false + counts.raw_true;
            if safe_total + raw_total + counts.none != counts.subjects_total() {
                return Err(format!(
                    "{program}: legacy kind partition does not reconcile"
                ));
            }
            row.extend([
                counts.subjects_total().to_string(),
                counts.ref_count().to_string(),
                counts.opt_ref_count().to_string(),
                counts.slice_count().to_string(),
                counts.slice_cursor_count().to_string(),
                counts.r#box.to_string(),
                counts.opt_box.to_string(),
                counts.boxed_slice.to_string(),
                counts.opt_boxed_slice.to_string(),
                counts.raw_false.to_string(),
                counts.raw_true.to_string(),
                counts.none.to_string(),
                safe_total.to_string(),
                counts.box_family_count().to_string(),
                raw_total.to_string(),
                "PASS: Σ final kinds + None = subjects_total".to_owned(),
            ]);
        } else {
            row.extend(std::iter::repeat_n(String::new(), 16));
        }
        Ok(format!(
            "{}\n",
            row.into_iter().map(csv_cell).collect::<Vec<_>>().join(",")
        ))
    }

    impl LegacyDecisionKind {
        fn parse(value: &str) -> Self {
            if value.starts_with("OptRef(") {
                Self::OptRef
            } else if value.starts_with("Ref(") {
                Self::Ref
            } else if value.starts_with("SliceCursor(") {
                Self::SliceCursor
            } else if value.starts_with("Slice(") {
                Self::Slice
            } else if value.starts_with("Raw(") {
                Self::Raw
            } else {
                match value {
                    "Box" => Self::Box,
                    "OptBox" => Self::OptBox,
                    "BoxedSlice" => Self::BoxedSlice,
                    "OptBoxedSlice" => Self::OptBoxedSlice,
                    _ => Self::Other,
                }
            }
        }

        fn is_safe(self) -> bool {
            matches!(
                self,
                Self::Ref
                    | Self::OptRef
                    | Self::Slice
                    | Self::SliceCursor
                    | Self::Box
                    | Self::OptBox
                    | Self::BoxedSlice
                    | Self::OptBoxedSlice
            )
        }
    }

    pub fn classify_legacy_safe_backing(
        kinds: &[LegacyDecisionKind],
    ) -> Result<LegacyBackingKind, String> {
        if classify_legacy_subjects(MappingCompleteness::Complete, kinds)
            != ProjectionOutcome::Eliminated
        {
            return Err("legacy backing classification requires a non-empty safe group".to_owned());
        }
        if kinds.iter().any(|kind| {
            matches!(
                kind,
                LegacyDecisionKind::Box
                    | LegacyDecisionKind::OptBox
                    | LegacyDecisionKind::BoxedSlice
                    | LegacyDecisionKind::OptBoxedSlice
            )
        }) {
            Ok(LegacyBackingKind::BoxFamily)
        } else {
            Ok(LegacyBackingKind::RefSlice)
        }
    }

    pub fn parse_bo_full_scope_counts(input: &str) -> Result<BoFullScopeCounts, String> {
        let lines = input
            .lines()
            .filter(|line| line.starts_with("BOC1 "))
            .collect::<Vec<_>>();
        let [line] = lines.as_slice() else {
            return Err(format!(
                "expected exactly one BOC1 result row, found {}",
                lines.len()
            ));
        };
        let row = report::parse_kv_line(line).ok_or_else(|| "malformed BOC1 row".to_owned())?;
        let mut fields = BTreeSet::new();
        for (key, _) in &row.0 {
            if !fields.insert(key) {
                return Err(format!("duplicate BOC1 field {key}"));
            }
        }
        let required = |key: &str| row.get(key).ok_or_else(|| format!("BOC1 row lacks {key}"));
        if required("mode")? != "bo" || required("status")? != "ok" {
            return Err("BOC1 full-scope row must be mode=bo status=ok".to_owned());
        }
        let parse = |key: &str| {
            required(key)?
                .parse::<usize>()
                .map_err(|_| format!("BOC1 {key} is not an integer"))
        };
        let counts = BoFullScopeCounts {
            program: required("program")?.to_owned(),
            slots_total: parse("slots_total")?,
            n_ref: parse("n_ref")?,
            n_own: parse("n_own")?,
            n_raw: parse("n_raw")?,
            n_ref_d0: parse("n_ref_d0")?,
            n_own_d0: parse("n_own_d0")?,
            n_raw_d0: parse("n_raw_d0")?,
        };
        if counts.n_ref + counts.n_own + counts.n_raw != counts.slots_total {
            return Err("BOC1 n_ref + n_own + n_raw != slots_total".to_owned());
        }
        if counts.d0_local_slots() > counts.slots_total {
            return Err("BOC1 d0 local-slot partition exceeds slots_total".to_owned());
        }
        if counts.n_ref_d0 > counts.n_ref
            || counts.n_own_d0 > counts.n_own
            || counts.n_raw_d0 > counts.n_raw
        {
            return Err("BOC1 d0 kind count exceeds its all-scope count".to_owned());
        }
        Ok(counts)
    }

    pub fn parse_legacy_full_scope_histogram(
        input: &str,
    ) -> Result<LegacyFullScopeHistogram, String> {
        let mut counts = LegacyFullScopeHistogram::default();
        for line in input
            .lines()
            .filter(|line| line.starts_with("[pointer-decision] subject="))
        {
            let value = line
                .split_whitespace()
                .find_map(|field| field.strip_prefix("final="))
                .ok_or_else(|| format!("pointer decision lacks final kind: {line}"))?;
            match value {
                "Ref(false)" => counts.ref_false += 1,
                "Ref(true)" => counts.ref_true += 1,
                "OptRef(false)" => counts.opt_ref_false += 1,
                "OptRef(true)" => counts.opt_ref_true += 1,
                "Slice(false)" => counts.slice_false += 1,
                "Slice(true)" => counts.slice_true += 1,
                "SliceCursor(false)" => counts.slice_cursor_false += 1,
                "SliceCursor(true)" => counts.slice_cursor_true += 1,
                "Box" => counts.r#box += 1,
                "OptBox" => counts.opt_box += 1,
                "BoxedSlice" => counts.boxed_slice += 1,
                "OptBoxedSlice" => counts.opt_boxed_slice += 1,
                "Raw(false)" => counts.raw_false += 1,
                "Raw(true)" => counts.raw_true += 1,
                "None" => counts.none += 1,
                _ => return Err(format!("unknown final decision kind {value}")),
            }
        }
        Ok(counts)
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum ProjectionOutcome {
        RefBacked,
        OwningBacked,
        Eliminated,
        Remaining,
        Unmapped,
    }

    impl ProjectionOutcome {
        pub fn as_str(self) -> &'static str {
            match self {
                Self::RefBacked => "predicted-eliminated-ref-backed",
                Self::OwningBacked => "predicted-eliminated-owning-backed",
                Self::Eliminated => "predicted-eliminated",
                Self::Remaining => "predicted-remaining",
                Self::Unmapped => "unmapped-counted-remaining",
            }
        }
    }

    impl MappingCompleteness {
        pub fn as_str(self) -> &'static str {
            match self {
                Self::Empty => "empty",
                Self::Partial => "partial",
                Self::Complete => "complete",
            }
        }
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum CrownRealizedKind {
        Reference,
        Box,
        Remaining,
    }

    impl CrownRealizedKind {
        pub fn as_str(self) -> &'static str {
            match self {
                Self::Reference => "realized-reference",
                Self::Box => "realized-Box",
                Self::Remaining => "realized-remaining",
            }
        }
    }

    #[derive(Clone, Debug)]
    pub struct OfficialProgram {
        pub evaluation: OfficialEvaluation,
        pub universe: BTreeSet<String>,
        pub crown_kinds: BTreeMap<String, CrownRealizedKind>,
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct ModelEvidence {
        pub declaration_key: String,
        pub completeness: MappingCompleteness,
        pub outcome: ProjectionOutcome,
        pub mapped_mir_locals: usize,
        pub mapped_slots: usize,
        pub raw_slots: usize,
        pub ref_slots: usize,
        pub owning_slots: usize,
        pub slot_keys: Vec<String>,
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct LegacyEvidence {
        pub declaration_key: String,
        pub completeness: MappingCompleteness,
        pub outcome: ProjectionOutcome,
        pub mapped_subjects: usize,
        pub kinds: Vec<LegacyDecisionKind>,
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct LegacyDecisionRecord {
        pub declaration_key: Option<String>,
        pub kind: LegacyDecisionKind,
    }

    pub fn classify_model_slots(
        completeness: MappingCompleteness,
        kinds: &[ModelKind],
    ) -> ProjectionOutcome {
        if completeness != MappingCompleteness::Complete || kinds.is_empty() {
            ProjectionOutcome::Unmapped
        } else if kinds.contains(&ModelKind::Raw) {
            ProjectionOutcome::Remaining
        } else if kinds.contains(&ModelKind::Owning) {
            ProjectionOutcome::OwningBacked
        } else {
            ProjectionOutcome::RefBacked
        }
    }

    pub fn classify_legacy_subjects(
        completeness: MappingCompleteness,
        kinds: &[LegacyDecisionKind],
    ) -> ProjectionOutcome {
        if completeness != MappingCompleteness::Complete || kinds.is_empty() {
            ProjectionOutcome::Unmapped
        } else if kinds.iter().all(|kind| kind.is_safe()) {
            ProjectionOutcome::Eliminated
        } else {
            ProjectionOutcome::Remaining
        }
    }

    pub fn parse_legacy_decisions(input: &str) -> Result<Vec<LegacyDecisionRecord>, String> {
        input
            .lines()
            .filter(|line| line.starts_with("[pointer-decision] subject="))
            .map(|line| {
                let field = |prefix: &str| {
                    line.split_whitespace()
                        .find_map(|part| part.strip_prefix(prefix))
                };
                let kind = field("final=")
                    .map(LegacyDecisionKind::parse)
                    .ok_or_else(|| format!("pointer decision lacks final kind: {line}"))?;
                let declaration_key = if line.starts_with("[pointer-decision] subject=local ")
                    || line.starts_with("[pointer-decision] subject=param ")
                {
                    match (field("fn="), field("name=")) {
                        (Some(function), Some(name)) => Some(format!("{function}::{name}")),
                        _ => {
                            return Err(format!("pointer decision lacks function/name: {line}"));
                        }
                    }
                } else if line.starts_with("[pointer-decision] subject=return ")
                    || line.starts_with("[pointer-decision] subject=field ")
                {
                    None
                } else {
                    return Err(format!("unrecognized pointer-decision subject: {line}"));
                };
                Ok(LegacyDecisionRecord {
                    declaration_key,
                    kind,
                })
            })
            .collect()
    }

    pub fn load_official_program(
        artifact_root: &Path,
        program: &str,
    ) -> Result<OfficialProgram, String> {
        let evaluations = parse_official_evaluation(
            &fs::read_to_string(artifact_root.join("evaluation.tsv"))
                .map_err(|error| format!("read evaluation.tsv: {error}"))?,
        )?;
        let evaluation = evaluations
            .get(program)
            .cloned()
            .ok_or_else(|| format!("evaluation.tsv lacks {program}"))?;
        let program_root = artifact_root.join(program);
        let analysis_root = program_root.join("analysis_results");
        let read_json = |name: &str| {
            fs::read_to_string(analysis_root.join(format!("{name}.json")))
                .map_err(|error| format!("{program}: read {name}.json: {error}"))
        };
        let claims = analyze_json_claims(
            &read_json("ownership")?,
            &read_json("statistics")?,
            &read_json("mutability")?,
            &read_json("fatness")?,
        )
        .map_err(|error| format!("{program}: {error}"))?;
        if claims.fn_d0_mut_ptr != evaluation.declaration_before {
            return Err(format!(
                "{program}: official universe {} != evaluation BEFORE {}",
                claims.fn_d0_mut_ptr, evaluation.declaration_before
            ));
        }

        let mut files = Vec::new();
        collect_rust_files(&program_root, &mut files)
            .map_err(|error| format!("{program}: discover emitted Rust: {error}"))?;
        files.sort();
        let mut sources = Vec::new();
        for path in &files {
            sources.push((
                rust_module_path(&program_root, path),
                fs::read_to_string(path).map_err(|error| format!("{}: {error}", path.display()))?,
            ));
        }
        let source_refs: Vec<_> = sources
            .iter()
            .map(|(module, source)| (module.as_str(), source.as_str()))
            .collect();
        let emitted = analyze_named_rust_sources(&source_refs)
            .map_err(|error| format!("{program}: parse emitted Rust: {error}"))?;
        let reference_keys = emitted
            .reference_function_slot_keys
            .intersection(&claims.fn_d0_mut_ptr_keys)
            .cloned()
            .collect::<BTreeSet<_>>();
        let box_keys = emitted
            .box_function_slot_keys
            .intersection(&claims.fn_d0_mut_ptr_keys)
            .cloned()
            .collect::<BTreeSet<_>>();
        if let Some(key) = reference_keys.intersection(&box_keys).next() {
            return Err(format!(
                "{program}: emitted reference/Box classifications overlap at {key}"
            ));
        }
        let eliminated = reference_keys.len() + box_keys.len();
        if claims.fn_d0_mut_ptr_keys.len().checked_sub(eliminated)
            != Some(evaluation.declaration_after as usize)
        {
            return Err(format!(
                "{program}: emitted safe-form intersection {eliminated} does not reproduce AFTER {}",
                evaluation.declaration_after
            ));
        }
        let crown_kinds = claims
            .fn_d0_mut_ptr_keys
            .iter()
            .map(|key| {
                let kind = if reference_keys.contains(key) {
                    CrownRealizedKind::Reference
                } else if box_keys.contains(key) {
                    CrownRealizedKind::Box
                } else {
                    CrownRealizedKind::Remaining
                };
                (key.clone(), kind)
            })
            .collect();
        Ok(OfficialProgram {
            evaluation,
            universe: claims.fn_d0_mut_ptr_keys,
            crown_kinds,
        })
    }

    fn collect_rust_files(dir: &Path, files: &mut Vec<PathBuf>) -> std::io::Result<()> {
        for entry in fs::read_dir(dir)? {
            let entry = entry?;
            let path = entry.path();
            if entry.file_type()?.is_dir() {
                if entry.file_name() != OsStr::new("target")
                    && entry.file_name() != OsStr::new("analysis_results")
                {
                    collect_rust_files(&path, files)?;
                }
            } else if path.extension() == Some(OsStr::new("rs")) {
                files.push(path);
            }
        }
        Ok(())
    }

    fn rust_module_path(root: &Path, path: &Path) -> String {
        path.strip_prefix(root)
            .unwrap_or(path)
            .with_extension("")
            .iter()
            .map(|component| component.to_string_lossy().replace('-', "_"))
            .collect::<Vec<_>>()
            .join("::")
    }

    fn source_group(
        groups: &SourceVarGroups,
        did: LocalDefId,
        root: Local,
        domain_size: usize,
    ) -> Vec<Local> {
        let mut without_root = DenseBitSet::new_filled(domain_size);
        without_root.remove(root);
        let processed = groups
            .postprocess_non_null_locals(FxHashMap::from_iter([(did, without_root)]))
            .remove(&did)
            .unwrap_or_else(|| DenseBitSet::new_empty(domain_size));
        (0..domain_size)
            .map(Local::from_usize)
            .filter(|local| !processed.contains(*local))
            .collect()
    }

    pub fn project_model_for_universe(
        tcx: TyCtxt<'_>,
        program: &RustProgram<'_>,
        slots: &CrateSlots,
        model: &FxHashMap<SlotRef, SlotKind>,
        universe: &BTreeSet<String>,
    ) -> BTreeMap<String, ModelEvidence> {
        let groups = SourceVarGroups::new(program);
        let mut roots: BTreeMap<String, Vec<(LocalDefId, Local)>> = BTreeMap::new();
        for &did in &program.functions {
            let body = tcx.mir_drops_elaborated_and_const_checked(did).borrow();
            for info in &body.var_debug_info {
                let VarDebugInfoContents::Place(place) = &info.value else {
                    continue;
                };
                let Some(local) = place.as_local() else {
                    continue;
                };
                let key = format!("{}::{}", tcx.def_path_str(did), info.name);
                if universe.contains(&key) {
                    let entry = roots.entry(key).or_default();
                    if !entry.contains(&(did, local)) {
                        entry.push((did, local));
                    }
                }
            }
        }

        universe
            .iter()
            .map(|key| {
                let debug_roots = roots.get(key).cloned().unwrap_or_default();
                let mut mapped_locals = FxHashSet::default();
                for (did, root) in &debug_roots {
                    let body = tcx.mir_drops_elaborated_and_const_checked(*did).borrow();
                    for local in source_group(&groups, *did, *root, body.local_decls.len()) {
                        mapped_locals.insert((*did, local));
                    }
                }
                let mut slot_refs = FxHashSet::default();
                let mut missing = false;
                for (did, local) in &mapped_locals {
                    match slots
                        .fn_local_slots
                        .get(did)
                        .and_then(|universe| universe.slot_for_local_depth(*local, 0))
                    {
                        Some(slot) => {
                            slot_refs.insert(SlotRef::Local(*did, slot));
                        }
                        None => missing = true,
                    }
                }
                let mut kinds = Vec::new();
                let mut slot_keys = Vec::new();
                for slot_ref in &slot_refs {
                    let SlotRef::Local(did, slot_id) = slot_ref else {
                        unreachable!("declaration mapping produces only local slots");
                    };
                    let universe = &slots.fn_local_slots[did];
                    let SlotOwner::Local(local) = universe.slot(*slot_id).owner else {
                        unreachable!("local slot universe yielded non-local owner");
                    };
                    slot_keys.push(format!("{}::_{}@d0", tcx.def_path_str(*did), local.index()));
                    match model.get(slot_ref) {
                        Some(SlotKind::Raw) => kinds.push(ModelKind::Raw),
                        Some(SlotKind::Ref) => kinds.push(ModelKind::Ref),
                        Some(SlotKind::Owning) => kinds.push(ModelKind::Owning),
                        None => missing = true,
                    }
                }
                slot_keys.sort();
                let completeness = if debug_roots.is_empty() || mapped_locals.is_empty() {
                    MappingCompleteness::Empty
                } else if missing || slot_refs.is_empty() {
                    MappingCompleteness::Partial
                } else {
                    MappingCompleteness::Complete
                };
                let outcome = classify_model_slots(completeness, &kinds);
                let evidence = ModelEvidence {
                    declaration_key: key.clone(),
                    completeness,
                    outcome,
                    mapped_mir_locals: mapped_locals.len(),
                    mapped_slots: slot_refs.len(),
                    raw_slots: kinds.iter().filter(|kind| **kind == ModelKind::Raw).count(),
                    ref_slots: kinds.iter().filter(|kind| **kind == ModelKind::Ref).count(),
                    owning_slots: kinds
                        .iter()
                        .filter(|kind| **kind == ModelKind::Owning)
                        .count(),
                    slot_keys,
                };
                (key.clone(), evidence)
            })
            .collect()
    }

    pub fn project_legacy_for_universe(
        universe: &BTreeSet<String>,
        records: &[LegacyDecisionRecord],
    ) -> BTreeMap<String, LegacyEvidence> {
        let mut by_key: BTreeMap<String, Vec<LegacyDecisionKind>> = BTreeMap::new();
        for record in records {
            if let Some(key) = &record.declaration_key
                && universe.contains(key)
            {
                by_key.entry(key.clone()).or_default().push(record.kind);
            }
        }
        universe
            .iter()
            .map(|key| {
                let kinds = by_key.get(key).cloned().unwrap_or_default();
                let completeness = if kinds.is_empty() {
                    MappingCompleteness::Empty
                } else {
                    MappingCompleteness::Complete
                };
                (
                    key.clone(),
                    LegacyEvidence {
                        declaration_key: key.clone(),
                        completeness,
                        outcome: classify_legacy_subjects(completeness, &kinds),
                        mapped_subjects: kinds.len(),
                        kinds,
                    },
                )
            })
            .collect()
    }

    pub fn write_model_snapshot(path: &Path, records: &BTreeMap<String, ModelEvidence>) {
        let mut out = String::from(
            "declaration_key\tmapping\toutcome\tmapped_mir_locals\tmapped_slots\traw_slots\tref_slots\towning_slots\tslot_keys\n",
        );
        for record in records.values() {
            out.push_str(&format!(
                "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
                record.declaration_key,
                record.completeness.as_str(),
                record.outcome.as_str(),
                record.mapped_mir_locals,
                record.mapped_slots,
                record.raw_slots,
                record.ref_slots,
                record.owning_slots,
                record.slot_keys.join(";"),
            ));
        }
        fs::write(path, out).unwrap_or_else(|error| {
            panic!("write projection snapshot {}: {error}", path.display())
        });
    }

    pub fn read_model_snapshot(path: &Path) -> Result<BTreeMap<String, ModelEvidence>, String> {
        let source =
            fs::read_to_string(path).map_err(|error| format!("{}: {error}", path.display()))?;
        let mut lines = source.lines();
        if lines.next()
            != Some(
                "declaration_key\tmapping\toutcome\tmapped_mir_locals\tmapped_slots\traw_slots\tref_slots\towning_slots\tslot_keys",
            )
        {
            return Err(format!(
                "{}: unexpected model snapshot header",
                path.display()
            ));
        }
        let mut records = BTreeMap::new();
        for (index, line) in lines.enumerate() {
            let fields = line.split('\t').collect::<Vec<_>>();
            if fields.len() != 9 {
                return Err(format!(
                    "{}:{}: expected 9 fields",
                    path.display(),
                    index + 2
                ));
            }
            let completeness = match fields[1] {
                "empty" => MappingCompleteness::Empty,
                "partial" => MappingCompleteness::Partial,
                "complete" => MappingCompleteness::Complete,
                value => return Err(format!("{}: unknown mapping {value}", path.display())),
            };
            let outcome = match fields[2] {
                "predicted-eliminated-ref-backed" => ProjectionOutcome::RefBacked,
                "predicted-eliminated-owning-backed" => ProjectionOutcome::OwningBacked,
                "predicted-remaining" => ProjectionOutcome::Remaining,
                "unmapped-counted-remaining" => ProjectionOutcome::Unmapped,
                value => return Err(format!("{}: unknown outcome {value}", path.display())),
            };
            let parse = |field: usize| {
                fields[field].parse::<usize>().map_err(|_| {
                    format!(
                        "{}:{}: field {} is not an integer",
                        path.display(),
                        index + 2,
                        field + 1
                    )
                })
            };
            let record = ModelEvidence {
                declaration_key: fields[0].to_owned(),
                completeness,
                outcome,
                mapped_mir_locals: parse(3)?,
                mapped_slots: parse(4)?,
                raw_slots: parse(5)?,
                ref_slots: parse(6)?,
                owning_slots: parse(7)?,
                slot_keys: if fields[8].is_empty() {
                    Vec::new()
                } else {
                    fields[8].split(';').map(str::to_owned).collect()
                },
            };
            if records
                .insert(record.declaration_key.clone(), record)
                .is_some()
            {
                return Err(format!(
                    "{}:{}: duplicate declaration",
                    path.display(),
                    index + 2
                ));
            }
        }
        Ok(records)
    }

    pub fn write_legacy_snapshot(path: &Path, records: &BTreeMap<String, LegacyEvidence>) {
        let mut out =
            String::from("declaration_key\tmapping\toutcome\tmapped_subjects\tfinal_kinds\n");
        for record in records.values() {
            out.push_str(&format!(
                "{}\t{}\t{}\t{}\t{}\n",
                record.declaration_key,
                record.completeness.as_str(),
                record.outcome.as_str(),
                record.mapped_subjects,
                record
                    .kinds
                    .iter()
                    .map(|kind| format!("{kind:?}"))
                    .collect::<Vec<_>>()
                    .join(";"),
            ));
        }
        fs::write(path, out)
            .unwrap_or_else(|error| panic!("write legacy snapshot {}: {error}", path.display()));
    }

    pub fn read_legacy_snapshot(path: &Path) -> Result<BTreeMap<String, LegacyEvidence>, String> {
        let source =
            fs::read_to_string(path).map_err(|error| format!("{}: {error}", path.display()))?;
        let mut lines = source.lines();
        if lines.next() != Some("declaration_key\tmapping\toutcome\tmapped_subjects\tfinal_kinds") {
            return Err(format!(
                "{}: unexpected legacy snapshot header",
                path.display()
            ));
        }
        let mut records = BTreeMap::new();
        for (index, line) in lines.enumerate() {
            let fields = line.split('\t').collect::<Vec<_>>();
            if fields.len() != 5 {
                return Err(format!(
                    "{}:{}: expected 5 fields",
                    path.display(),
                    index + 2
                ));
            }
            let completeness = match fields[1] {
                "empty" => MappingCompleteness::Empty,
                "complete" => MappingCompleteness::Complete,
                value => return Err(format!("{}: unknown mapping {value}", path.display())),
            };
            let outcome = match fields[2] {
                "predicted-eliminated" => ProjectionOutcome::Eliminated,
                "predicted-remaining" => ProjectionOutcome::Remaining,
                "unmapped-counted-remaining" => ProjectionOutcome::Unmapped,
                value => return Err(format!("{}: unknown outcome {value}", path.display())),
            };
            let kinds = if fields[4].is_empty() {
                Vec::new()
            } else {
                fields[4]
                    .split(';')
                    .map(|value| match value {
                        "Ref" => Ok(LegacyDecisionKind::Ref),
                        "OptRef" => Ok(LegacyDecisionKind::OptRef),
                        "Slice" => Ok(LegacyDecisionKind::Slice),
                        "SliceCursor" => Ok(LegacyDecisionKind::SliceCursor),
                        "Box" => Ok(LegacyDecisionKind::Box),
                        "OptBox" => Ok(LegacyDecisionKind::OptBox),
                        "BoxedSlice" => Ok(LegacyDecisionKind::BoxedSlice),
                        "OptBoxedSlice" => Ok(LegacyDecisionKind::OptBoxedSlice),
                        "Raw" => Ok(LegacyDecisionKind::Raw),
                        "Other" => Ok(LegacyDecisionKind::Other),
                        _ => Err(format!("{}: unknown legacy kind {value}", path.display())),
                    })
                    .collect::<Result<Vec<_>, _>>()?
            };
            let record = LegacyEvidence {
                declaration_key: fields[0].to_owned(),
                completeness,
                outcome,
                mapped_subjects: fields[3].parse().map_err(|_| {
                    format!(
                        "{}:{}: mapped_subjects is not an integer",
                        path.display(),
                        index + 2
                    )
                })?,
                kinds,
            };
            if records
                .insert(record.declaration_key.clone(), record)
                .is_some()
            {
                return Err(format!(
                    "{}:{}: duplicate declaration",
                    path.display(),
                    index + 2
                ));
            }
        }
        Ok(records)
    }

    pub fn maybe_write_model_snapshot(
        tcx: TyCtxt<'_>,
        program: &RustProgram<'_>,
        slots: &CrateSlots,
        model: &FxHashMap<SlotRef, SlotKind>,
    ) -> Option<usize> {
        let path = std::env::var_os("CRAT_BOC1_PROJECTION_SNAPSHOT").map(PathBuf::from)?;
        let artifact_root = PathBuf::from(
            std::env::var_os("CRAT_BOC1_CROWN_ARTIFACT")
                .expect("projection worker requires CRAT_BOC1_CROWN_ARTIFACT"),
        );
        let name =
            std::env::var("CRAT_BOC1_NAME").expect("projection worker requires CRAT_BOC1_NAME");
        let official = load_official_program(&artifact_root, &name)
            .unwrap_or_else(|error| panic!("load official projection universe: {error}"));
        let records = project_model_for_universe(tcx, program, slots, model, &official.universe);
        assert_eq!(
            records.len(),
            official.evaluation.declaration_before as usize,
            "{name}: projection snapshot must partition the official BEFORE universe"
        );
        write_model_snapshot(&path, &records);
        Some(records.len())
    }
}

/// Measurement-only comparison surface for the registered PRIMARY ownership-yield evaluation.
///
/// This module owns canonical report records and their deterministic comparison/serialization.
/// It never changes either ownership analysis; the corpus workers only export their existing
/// solidified results through this surface when the measurement flag is enabled.
mod ownership_yield {
    use std::{
        collections::{BTreeMap, BTreeSet},
        fs,
        path::Path,
    };

    use crate::analyses::borrow_ownership::SlotKind;

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum OwnerClass {
        Local,
        Field,
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct SlotRecord {
        pub key: String,
        pub owner: OwnerClass,
        pub depth: u8,
        pub owning: bool,
        pub forced_output: bool,
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct ModelKindRecord {
        pub key: String,
        pub owner: OwnerClass,
        pub depth: u8,
        pub kind: SlotKind,
    }

    #[derive(Clone, Debug, Default, PartialEq, Eq)]
    pub struct SideCounts {
        pub local_owning_by_depth: BTreeMap<u8, usize>,
        pub field_owning_by_depth: BTreeMap<u8, usize>,
        pub total_owning: usize,
    }

    #[derive(Clone, Debug, Default, PartialEq, Eq)]
    pub struct Comparison {
        pub bo: SideCounts,
        pub production: SideCounts,
        pub production_forced_output: usize,
        pub production_without_forced: usize,
        pub bo_only_owning: Vec<String>,
        pub production_only_owning: Vec<String>,
        pub bo_universe_only: Vec<String>,
        pub production_universe_only: Vec<String>,
    }

    #[derive(Clone, Debug, PartialEq)]
    pub struct ProgramSummary {
        pub program: String,
        pub bo_status: String,
        pub production_status: String,
        pub bo_wall_s: f64,
        pub production_wall_s: Option<f64>,
        pub production_andersen_s: Option<f64>,
        pub production_output_params_s: Option<f64>,
        pub production_ownership_s: Option<f64>,
        pub production_solidify_s: Option<f64>,
        pub production_cap_s: u64,
        pub production_failure: Option<String>,
        pub bo: SideCounts,
        pub comparison: Option<Comparison>,
    }

    fn indexed<'a>(
        records: &'a [SlotRecord],
        side: &str,
    ) -> Result<BTreeMap<&'a str, &'a SlotRecord>, String> {
        let mut indexed = BTreeMap::new();
        for record in records {
            if indexed.insert(record.key.as_str(), record).is_some() {
                return Err(format!("duplicate {side} canonical key: {}", record.key));
            }
        }
        Ok(indexed)
    }

    fn counts(records: &[SlotRecord]) -> SideCounts {
        let mut counts = SideCounts::default();
        for record in records.iter().filter(|record| record.owning) {
            let by_depth = match record.owner {
                OwnerClass::Local => &mut counts.local_owning_by_depth,
                OwnerClass::Field => &mut counts.field_owning_by_depth,
            };
            *by_depth.entry(record.depth).or_default() += 1;
            counts.total_owning += 1;
        }
        counts
    }

    pub fn side_counts(records: &[SlotRecord]) -> SideCounts {
        counts(records)
    }

    pub fn enabled() -> bool {
        const ENV: &str = "CRAT_BOC1_OWNERSHIP_YIELD";
        match std::env::var(ENV).as_deref() {
            Err(std::env::VarError::NotPresent) | Ok("0") => false,
            Ok("1") => true,
            Ok(other) => panic!("{ENV} must be 0 or 1, got {other:?}"),
            Err(error) => panic!("{ENV} is not valid Unicode: {error}"),
        }
    }

    pub fn write_worker_snapshot(records: &[SlotRecord]) -> Result<(), String> {
        let path = std::env::var("CRAT_BOC1_YIELD_SNAPSHOT")
            .map_err(|error| format!("CRAT_BOC1_YIELD_SNAPSHOT: {error}"))?;
        fs::write(&path, snapshot_tsv(records))
            .map_err(|error| format!("write ownership-yield snapshot {path}: {error}"))
    }

    pub fn read_worker_snapshot(path: &Path) -> Result<Vec<SlotRecord>, String> {
        let input = fs::read_to_string(path).map_err(|error| {
            format!("read ownership-yield snapshot {}: {error}", path.display())
        })?;
        parse_snapshot_tsv(&input)
    }

    pub fn compare(bo: &[SlotRecord], production: &[SlotRecord]) -> Result<Comparison, String> {
        let bo_index = indexed(bo, "BO")?;
        let production_index = indexed(production, "production")?;

        if let Some(record) = bo.iter().find(|record| record.forced_output) {
            return Err(format!(
                "BO record cannot be forced-output classified: {}",
                record.key
            ));
        }
        if let Some(record) = production
            .iter()
            .find(|record| record.forced_output && !record.owning)
        {
            return Err(format!(
                "production forced-output record is not Owning: {}",
                record.key
            ));
        }

        for (&key, bo_record) in &bo_index {
            let Some(production_record) = production_index.get(key) else {
                continue;
            };
            if (bo_record.owner, bo_record.depth)
                != (production_record.owner, production_record.depth)
            {
                return Err(format!(
                    "canonical key metadata mismatch for {key}: BO={:?}@d{} production={:?}@d{}",
                    bo_record.owner,
                    bo_record.depth,
                    production_record.owner,
                    production_record.depth
                ));
            }
        }

        let keys: BTreeSet<&str> = bo_index
            .keys()
            .chain(production_index.keys())
            .copied()
            .collect();
        let mut bo_only_owning = Vec::new();
        let mut production_only_owning = Vec::new();
        for key in keys {
            let bo_owning = bo_index.get(key).is_some_and(|record| record.owning);
            let production_owning = production_index
                .get(key)
                .is_some_and(|record| record.owning);
            match (bo_owning, production_owning) {
                (true, false) => bo_only_owning.push(key.to_string()),
                (false, true) => production_only_owning.push(key.to_string()),
                _ => {}
            }
        }

        let production_forced_output = production
            .iter()
            .filter(|record| record.forced_output)
            .count();
        let production_counts = counts(production);
        Ok(Comparison {
            bo: counts(bo),
            production_without_forced: production_counts
                .total_owning
                .checked_sub(production_forced_output)
                .ok_or_else(|| {
                    "production forced-output count exceeds total Owning count".to_string()
                })?,
            production: production_counts,
            production_forced_output,
            bo_only_owning,
            production_only_owning,
            bo_universe_only: bo_index
                .keys()
                .filter(|key| !production_index.contains_key(**key))
                .map(|key| (*key).to_string())
                .collect(),
            production_universe_only: production_index
                .keys()
                .filter(|key| !bo_index.contains_key(**key))
                .map(|key| (*key).to_string())
                .collect(),
        })
    }

    fn hex_encode(input: &str) -> String {
        input
            .as_bytes()
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect()
    }

    fn hex_decode(input: &str) -> Result<String, String> {
        if !input.len().is_multiple_of(2) {
            return Err("odd-length hex key".to_string());
        }
        let bytes = input
            .as_bytes()
            .chunks_exact(2)
            .map(|pair| {
                let pair =
                    std::str::from_utf8(pair).map_err(|error| format!("hex key UTF-8: {error}"))?;
                u8::from_str_radix(pair, 16).map_err(|error| format!("hex key byte: {error}"))
            })
            .collect::<Result<Vec<_>, _>>()?;
        String::from_utf8(bytes).map_err(|error| format!("decoded key UTF-8: {error}"))
    }

    pub fn snapshot_tsv(records: &[SlotRecord]) -> String {
        let mut records = records.to_vec();
        records.sort_by(|left, right| left.key.cmp(&right.key));
        let mut out = String::from("key_hex\towner\tdepth\towning\tforced_output\n");
        for record in records {
            let owner = match record.owner {
                OwnerClass::Local => "local",
                OwnerClass::Field => "field",
            };
            out.push_str(&format!(
                "{}\t{owner}\t{}\t{}\t{}\n",
                hex_encode(&record.key),
                record.depth,
                u8::from(record.owning),
                u8::from(record.forced_output)
            ));
        }
        out
    }

    pub fn parse_snapshot_tsv(input: &str) -> Result<Vec<SlotRecord>, String> {
        let mut records = input
            .lines()
            .skip(1)
            .enumerate()
            .filter(|(_, line)| !line.trim().is_empty())
            .map(|(index, line)| {
                let fields = line.split('\t').collect::<Vec<_>>();
                if fields.len() != 5 {
                    return Err(format!(
                        "snapshot line {} has {} fields, expected 5",
                        index + 2,
                        fields.len()
                    ));
                }
                let owner = match fields[1] {
                    "local" => OwnerClass::Local,
                    "field" => OwnerClass::Field,
                    other => {
                        return Err(format!("snapshot line {} owner: {other}", index + 2));
                    }
                };
                let parse_bool = |value: &str, name: &str| match value {
                    "0" => Ok(false),
                    "1" => Ok(true),
                    other => Err(format!("snapshot line {} {name}: {other}", index + 2)),
                };
                Ok(SlotRecord {
                    key: hex_decode(fields[0])?,
                    owner,
                    depth: fields[2]
                        .parse()
                        .map_err(|error| format!("snapshot line {} depth: {error}", index + 2))?,
                    owning: parse_bool(fields[3], "owning")?,
                    forced_output: parse_bool(fields[4], "forced_output")?,
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        indexed(&records, "snapshot")?;
        records.sort_by(|left, right| left.key.cmp(&right.key));
        Ok(records)
    }

    pub fn model_kind_snapshot_tsv(records: &[ModelKindRecord]) -> String {
        let mut records = records.to_vec();
        records.sort_by(|left, right| left.key.cmp(&right.key));
        let mut out = String::from("key_hex\towner\tdepth\tkind\n");
        for record in records {
            let owner = match record.owner {
                OwnerClass::Local => "local",
                OwnerClass::Field => "field",
            };
            let kind = match record.kind {
                SlotKind::Raw => "raw",
                SlotKind::Ref => "ref",
                SlotKind::Owning => "owning",
            };
            out.push_str(&format!(
                "{}\t{owner}\t{}\t{kind}\n",
                hex_encode(&record.key),
                record.depth,
            ));
        }
        out
    }

    pub fn parse_model_kind_snapshot_tsv(input: &str) -> Result<Vec<ModelKindRecord>, String> {
        let mut records = input
            .lines()
            .skip(1)
            .enumerate()
            .filter(|(_, line)| !line.trim().is_empty())
            .map(|(index, line)| {
                let fields = line.split('\t').collect::<Vec<_>>();
                if fields.len() != 4 {
                    return Err(format!(
                        "model-kind snapshot line {} has {} fields, expected 4",
                        index + 2,
                        fields.len()
                    ));
                }
                let owner = match fields[1] {
                    "local" => OwnerClass::Local,
                    "field" => OwnerClass::Field,
                    other => {
                        return Err(format!(
                            "model-kind snapshot line {} owner: {other}",
                            index + 2
                        ));
                    }
                };
                let kind = match fields[3] {
                    "raw" => SlotKind::Raw,
                    "ref" => SlotKind::Ref,
                    "owning" => SlotKind::Owning,
                    other => {
                        return Err(format!(
                            "model-kind snapshot line {} kind: {other}",
                            index + 2
                        ));
                    }
                };
                Ok(ModelKindRecord {
                    key: hex_decode(fields[0])?,
                    owner,
                    depth: fields[2].parse().map_err(|error| {
                        format!("model-kind snapshot line {} depth: {error}", index + 2)
                    })?,
                    kind,
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        let mut keys = BTreeSet::new();
        if let Some(record) = records.iter().find(|record| !keys.insert(&record.key)) {
            return Err(format!(
                "duplicate model-kind snapshot canonical key: {}",
                record.key
            ));
        }
        records.sort_by(|left, right| left.key.cmp(&right.key));
        Ok(records)
    }

    pub fn write_model_kind_snapshot(
        path: &Path,
        records: &[ModelKindRecord],
    ) -> Result<(), String> {
        fs::write(path, model_kind_snapshot_tsv(records))
            .map_err(|error| format!("write model-kind snapshot {}: {error}", path.display()))
    }

    fn depth(counts: &BTreeMap<u8, usize>, exact: u8) -> usize {
        counts.get(&exact).copied().unwrap_or(0)
    }

    fn depth_3_plus(counts: &BTreeMap<u8, usize>) -> usize {
        counts
            .iter()
            .filter(|(depth, _)| **depth >= 3)
            .map(|(_, count)| count)
            .sum()
    }

    fn csv_cell(value: &str) -> String {
        if value.chars().any(|ch| matches!(ch, ',' | '"' | '\n')) {
            format!("\"{}\"", value.replace('"', "\"\""))
        } else {
            value.to_string()
        }
    }

    fn opt_f64(value: Option<f64>) -> String {
        value.map(|value| format!("{value:.3}")).unwrap_or_default()
    }

    pub fn render_summary_csv(rows: &[ProgramSummary]) -> String {
        let mut out = String::from(
            "program,bo_status,production_status,bo_wall_s,production_wall_s,\
             production_cap_s,production_andersen_s,production_output_params_s,\
             production_ownership_s,production_solidify_s,bo_local_own_d0,\
             bo_local_own_d1,bo_local_own_d2,bo_local_own_d3_plus,bo_field_own,\
             bo_total_own,production_local_own_d0,production_local_own_d1,\
             production_local_own_d2,production_local_own_d3_plus,\
             production_field_own,production_total_own,production_forced_output,\
             production_total_without_forced,bo_only_owning,production_only_owning,\
             bo_universe_only,production_universe_only,note\n",
        );
        for row in rows {
            let comparison = row.comparison.as_ref();
            let bo = &row.bo;
            let production = comparison.map(|comparison| &comparison.production);
            let note = row
                .production_failure
                .as_ref()
                .map(|reason| {
                    format!(
                        "production: failed ({reason}, cap {}s)",
                        row.production_cap_s
                    )
                })
                .unwrap_or_default();
            let cells = [
                csv_cell(&row.program),
                csv_cell(&row.bo_status),
                csv_cell(&row.production_status),
                format!("{:.3}", row.bo_wall_s),
                opt_f64(row.production_wall_s),
                row.production_cap_s.to_string(),
                opt_f64(row.production_andersen_s),
                opt_f64(row.production_output_params_s),
                opt_f64(row.production_ownership_s),
                opt_f64(row.production_solidify_s),
                depth(&bo.local_owning_by_depth, 0).to_string(),
                depth(&bo.local_owning_by_depth, 1).to_string(),
                depth(&bo.local_owning_by_depth, 2).to_string(),
                depth_3_plus(&bo.local_owning_by_depth).to_string(),
                bo.field_owning_by_depth.values().sum::<usize>().to_string(),
                bo.total_owning.to_string(),
                production
                    .map(|counts| depth(&counts.local_owning_by_depth, 0))
                    .unwrap_or(0)
                    .to_string(),
                production
                    .map(|counts| depth(&counts.local_owning_by_depth, 1))
                    .unwrap_or(0)
                    .to_string(),
                production
                    .map(|counts| depth(&counts.local_owning_by_depth, 2))
                    .unwrap_or(0)
                    .to_string(),
                production
                    .map(|counts| depth_3_plus(&counts.local_owning_by_depth))
                    .unwrap_or(0)
                    .to_string(),
                production
                    .map(|counts| counts.field_owning_by_depth.values().sum())
                    .unwrap_or(0usize)
                    .to_string(),
                production
                    .map(|counts| counts.total_owning)
                    .unwrap_or(0)
                    .to_string(),
                comparison
                    .map(|comparison| comparison.production_forced_output)
                    .unwrap_or(0)
                    .to_string(),
                comparison
                    .map(|comparison| comparison.production_without_forced)
                    .unwrap_or(0)
                    .to_string(),
                comparison
                    .map(|comparison| comparison.bo_only_owning.len())
                    .unwrap_or(0)
                    .to_string(),
                comparison
                    .map(|comparison| comparison.production_only_owning.len())
                    .unwrap_or(0)
                    .to_string(),
                comparison
                    .map(|comparison| comparison.bo_universe_only.len())
                    .unwrap_or(0)
                    .to_string(),
                comparison
                    .map(|comparison| comparison.production_universe_only.len())
                    .unwrap_or(0)
                    .to_string(),
                csv_cell(&note),
            ];
            out.push_str(&cells.join(","));
            out.push('\n');
        }
        out
    }

    pub fn render_deltas_tsv(rows: &[ProgramSummary]) -> String {
        let mut out = String::from("program\tclassification\tkey_hex\tkey\n");
        for row in rows {
            let Some(comparison) = &row.comparison else {
                continue;
            };
            for (classification, keys) in [
                ("bo_only_owning", &comparison.bo_only_owning),
                ("production_only_owning", &comparison.production_only_owning),
                ("bo_universe_only", &comparison.bo_universe_only),
                (
                    "production_universe_only",
                    &comparison.production_universe_only,
                ),
            ] {
                for key in keys {
                    out.push_str(&format!(
                        "{}\t{classification}\t{}\t{}\n",
                        row.program,
                        hex_encode(key),
                        key
                    ));
                }
            }
        }
        out
    }

    fn counts_label(counts: &BTreeMap<u8, usize>) -> String {
        if counts.is_empty() {
            return "—".to_string();
        }
        counts
            .iter()
            .map(|(depth, count)| format!("d{depth}:{count}"))
            .collect::<Vec<_>>()
            .join("/")
    }

    fn sample(keys: &[String]) -> String {
        if keys.is_empty() {
            return "—".to_string();
        }
        keys.iter()
            .take(5)
            .cloned()
            .collect::<Vec<_>>()
            .join("<br>")
    }

    pub fn render_markdown(rows: &[ProgramSummary]) -> String {
        let mut out = String::from(
            "# PRIMARY ownership yield: production vs BO\n\n\
             Forced output-parameter subtraction is set arithmetic over structurally forced \
             depth-0 production keys, not a counterfactual re-solve.\n\n\
             ## Counts and timing\n\n\
             | program | BO locals by depth | BO fields by depth | BO total | BO wall s | \
             production status | production locals by depth | production fields by depth | \
             production total | forced output | production without forced | production wall s | \
             Andersen s | output-param s | ownership solve s | solidify s |\n\
             |---|---:|---:|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|\n",
        );
        for row in rows {
            let (
                production_locals,
                production_fields,
                production_total,
                production_forced,
                production_without_forced,
            ) = row
                .comparison
                .as_ref()
                .map(|comparison| {
                    (
                        counts_label(&comparison.production.local_owning_by_depth),
                        counts_label(&comparison.production.field_owning_by_depth),
                        comparison.production.total_owning.to_string(),
                        comparison.production_forced_output.to_string(),
                        comparison.production_without_forced.to_string(),
                    )
                })
                .unwrap_or_else(|| {
                    (
                        "—".to_string(),
                        "—".to_string(),
                        "—".to_string(),
                        "—".to_string(),
                        "—".to_string(),
                    )
                });
            let production_status = row
                .production_failure
                .as_ref()
                .map(|reason| format!("failed ({reason}, cap {}s)", row.production_cap_s))
                .unwrap_or_else(|| row.production_status.clone());
            out.push_str(&format!(
                "| {} | {} | {} | {} | {:.3} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} |\n",
                row.program,
                counts_label(&row.bo.local_owning_by_depth),
                counts_label(&row.bo.field_owning_by_depth),
                row.bo.total_owning,
                row.bo_wall_s,
                production_status,
                production_locals,
                production_fields,
                production_total,
                production_forced,
                production_without_forced,
                opt_f64(row.production_wall_s),
                opt_f64(row.production_andersen_s),
                opt_f64(row.production_output_params_s),
                opt_f64(row.production_ownership_s),
                opt_f64(row.production_solidify_s),
            ));
        }
        out.push_str(
            "\n## Delta and universe samples\n\n\
             Full sorted sets are in `ownership-yield-deltas.tsv`; samples are capped at five keys \
             per direction and program.\n\n\
             | program | BO-only Owning | production-only Owning | BO-universe-only | \
             production-universe-only |\n\
             |---|---|---|---|---|\n",
        );
        for row in rows {
            if let Some(comparison) = &row.comparison {
                out.push_str(&format!(
                    "| {} | {} | {} | {} | {} |\n",
                    row.program,
                    sample(&comparison.bo_only_owning),
                    sample(&comparison.production_only_owning),
                    sample(&comparison.bo_universe_only),
                    sample(&comparison.production_universe_only),
                ));
            } else {
                let reason = row.production_failure.as_deref().unwrap_or("unknown");
                out.push_str(&format!(
                    "| {} | excluded: production failed ({reason}) | excluded | excluded | excluded |\n",
                    row.program
                ));
            }
        }
        out
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        fn slot(
            key: &str,
            owner: OwnerClass,
            depth: u8,
            owning: bool,
            forced_output: bool,
        ) -> SlotRecord {
            SlotRecord {
                key: key.to_string(),
                owner,
                depth,
                owning,
                forced_output,
            }
        }

        #[test]
        fn ownership_yield_compares_exact_keys_depths_and_forced_entries() {
            let bo = vec![
                slot("crate::f::_1@d0", OwnerClass::Local, 0, true, false),
                slot("crate::S::field0@d1", OwnerClass::Field, 1, true, false),
                slot("crate::f::_9@d0", OwnerClass::Local, 0, false, false),
            ];
            let production = vec![
                slot("crate::f::_1@d0", OwnerClass::Local, 0, true, true),
                slot("crate::g::_2@d1", OwnerClass::Local, 1, true, false),
                slot("crate::g::_7@d3", OwnerClass::Local, 3, false, false),
            ];

            let got = compare(&bo, &production).expect("comparison");
            assert_eq!(got.bo.local_owning_by_depth, BTreeMap::from([(0, 1)]));
            assert_eq!(got.bo.field_owning_by_depth, BTreeMap::from([(1, 1)]));
            assert_eq!(
                got.production.local_owning_by_depth,
                BTreeMap::from([(0, 1), (1, 1)])
            );
            assert_eq!(got.bo.total_owning, 2);
            assert_eq!(got.production.total_owning, 2);
            assert_eq!(got.production_forced_output, 1);
            assert_eq!(
                got.production_without_forced, 1,
                "set subtraction is structural, not a counterfactual re-solve"
            );
            assert_eq!(got.bo_only_owning, ["crate::S::field0@d1"]);
            assert_eq!(got.production_only_owning, ["crate::g::_2@d1"]);
            assert_eq!(
                got.bo_universe_only,
                ["crate::S::field0@d1", "crate::f::_9@d0"]
            );
            assert_eq!(
                got.production_universe_only,
                ["crate::g::_2@d1", "crate::g::_7@d3"]
            );
        }

        #[test]
        fn ownership_yield_rejects_duplicate_canonical_keys() {
            let duplicate = vec![
                slot("crate::f::_1@d0", OwnerClass::Local, 0, true, false),
                slot("crate::f::_1@d0", OwnerClass::Local, 0, false, false),
            ];
            let err = compare(&duplicate, &[]).expect_err("duplicate key must fail");
            assert!(err.contains("duplicate BO canonical key"), "{err}");
        }

        #[test]
        fn ownership_yield_snapshot_is_byte_stable_and_round_trips() {
            let left = vec![
                slot("z::_2@d1", OwnerClass::Local, 1, false, false),
                slot("a::field0@d0", OwnerClass::Field, 0, true, false),
            ];
            let right = vec![left[1].clone(), left[0].clone()];
            let encoded = snapshot_tsv(&left);
            assert_eq!(encoded, snapshot_tsv(&right));
            assert!(encoded.ends_with('\n'));
            assert_eq!(parse_snapshot_tsv(&encoded).expect("parse"), right);
        }

        #[test]
        fn ownership_yield_model_kind_snapshot_is_byte_stable_and_round_trips() {
            let left = vec![
                ModelKindRecord {
                    key: "z::_2@d1".to_string(),
                    owner: OwnerClass::Local,
                    depth: 1,
                    kind: SlotKind::Raw,
                },
                ModelKindRecord {
                    key: "a::field0@d0".to_string(),
                    owner: OwnerClass::Field,
                    depth: 0,
                    kind: SlotKind::Owning,
                },
                ModelKindRecord {
                    key: "m::_1@d0".to_string(),
                    owner: OwnerClass::Local,
                    depth: 0,
                    kind: SlotKind::Ref,
                },
            ];
            let right = vec![left[1].clone(), left[2].clone(), left[0].clone()];
            let encoded = model_kind_snapshot_tsv(&left);
            assert_eq!(encoded, model_kind_snapshot_tsv(&right));
            assert!(encoded.ends_with('\n'));
            assert_eq!(
                parse_model_kind_snapshot_tsv(&encoded).expect("parse"),
                right
            );
        }

        #[test]
        fn ownership_yield_summary_preserves_production_failure_and_cap() {
            let csv = render_summary_csv(&[ProgramSummary {
                program: "brotli".to_string(),
                bo_status: "ok".to_string(),
                production_status: "timeout".to_string(),
                bo_wall_s: 551.9,
                production_wall_s: Some(1800.2),
                production_andersen_s: None,
                production_output_params_s: None,
                production_ownership_s: None,
                production_solidify_s: None,
                production_cap_s: 1800,
                production_failure: Some("timeout".to_string()),
                bo: SideCounts::default(),
                comparison: None,
            }]);
            assert!(csv.contains("brotli,ok,timeout"));
            assert!(csv.contains("1800"));
            assert!(
                csv.contains("production: failed (timeout, cap 1800s)"),
                "{csv}"
            );
        }
    }
}

/// Measurement-only contracts for the three-part ownership diagnostic package.
///
/// The RED commit deliberately provides inert answers so each test below
/// compiles and fails at assertion level. GREEN binds these contracts to the
/// diagnostic workers without changing BO or production semantics.
pub(crate) mod ownership_diagnostic_package {
    use std::{
        cell::{Cell, RefCell},
        collections::{BTreeMap, BTreeSet},
        fs,
        path::Path,
    };

    use serde::{Deserialize, Serialize};

    use super::ownership_yield::OwnerClass;
    pub(crate) use crate::analyses::borrow_ownership::solver::OwnAssumeSite as AssumeSite;

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum HardConstraintDecision {
        Assert,
        Suppress,
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct FilterProbe {
        pub decision: HardConstraintDecision,
        pub label_evaluated: bool,
        pub tracking_markers: usize,
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
    pub enum CausalBucket {
        JointNoSingleFamilyNecessity,
        SoleOwnAssume,
        Other,
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum RemovalFilter {
        Family(&'static str),
        FamilyPair([&'static str; 2]),
        OwnAssumeSite(AssumeSite),
    }

    pub const PAIRWISE_REMOVAL_FAMILIES: [&str; 5] = [
        "own-equal",
        "own-assume",
        "own-linear",
        "kind-equate",
        "link-own",
    ];

    pub fn pairwise_removal_pairs() -> Vec<[&'static str; 2]> {
        let mut pairs = Vec::with_capacity(10);
        for (index, &first) in PAIRWISE_REMOVAL_FAMILIES.iter().enumerate() {
            for &second in &PAIRWISE_REMOVAL_FAMILIES[index + 1..] {
                pairs.push([first, second]);
            }
        }
        pairs
    }

    #[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
    pub struct FamilyPair {
        pub first: String,
        pub second: String,
    }

    impl FamilyPair {
        pub fn new(pair: [&str; 2]) -> Self {
            Self {
                first: pair[0].to_string(),
                second: pair[1].to_string(),
            }
        }

        pub fn label(&self) -> String {
            format!("{}+{}", self.first, self.second)
        }
    }

    #[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
    pub struct PairRemovalOutcome {
        pub pair: FamilyPair,
        pub result_is_sat: bool,
    }

    impl PairRemovalOutcome {
        pub fn new(pair: [&str; 2], result_is_sat: bool) -> Self {
            Self {
                pair: FamilyPair::new(pair),
                result_is_sat,
            }
        }
    }

    #[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
    pub struct PairRemovalEvidence {
        pub outcomes: Vec<PairRemovalOutcome>,
        pub minimal_sat_pairs: BTreeSet<FamilyPair>,
    }

    impl PairRemovalEvidence {
        pub fn no_pair(&self) -> bool {
            self.minimal_sat_pairs.is_empty()
        }
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct PairRemovalSummary {
        pub selector_csv: String,
        pub frequency_csv: String,
        pub program_csv: String,
        pub no_pair_csv: String,
        pub pair_frequency: BTreeMap<FamilyPair, usize>,
        pub joint_rows: usize,
        pub recovered_rows: usize,
        pub no_pair_rows: usize,
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
    pub enum PrecisionClass {
        Full,
        Degraded,
        Dummy,
    }

    #[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
    pub struct BoxDecisionCounts {
        pub locals: usize,
        pub params: usize,
        pub returns: usize,
        pub fields: usize,
        pub d0_locals: usize,
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum RetryStatus {
        CompleteFirstPass,
        CompleteAfterRetry,
        ResourceDeferred,
    }

    pub const ASSUME_SITES: &[AssumeSite] = &[
        AssumeSite::OpaqueCallArg,
        AssumeSite::LibcRule,
        AssumeSite::LocalWrapper,
        AssumeSite::SsaTransfer,
        AssumeSite::TemporaryFinalization,
        AssumeSite::CastOrDepth,
        AssumeSite::OtherInternal,
    ];

    pub const ENV: &str = "CRAT_BOC1_OWNERSHIP_DIAGNOSTIC_PACKAGE";
    pub const PAIRWISE_ENV: &str = "CRAT_BOC1_PAIRWISE_FAMILY_REMOVAL";
    pub const SNAPSHOT_ONLY_ENV: &str = "CRAT_BOC1_PROD_BOX_SNAPSHOT_ONLY";

    pub fn enabled() -> bool {
        match std::env::var(ENV).as_deref() {
            Err(std::env::VarError::NotPresent) | Ok("0") => false,
            Ok("1") => true,
            Ok(other) => panic!("{ENV} must be 0 or 1, got {other:?}"),
            Err(error) => panic!("{ENV} is not valid Unicode: {error}"),
        }
    }

    pub fn snapshot_only_enabled() -> bool {
        match std::env::var(SNAPSHOT_ONLY_ENV).as_deref() {
            Err(std::env::VarError::NotPresent) | Ok("0") => false,
            Ok("1") => true,
            Ok(other) => panic!("{SNAPSHOT_ONLY_ENV} must be 0 or 1, got {other:?}"),
            Err(error) => panic!("{SNAPSHOT_ONLY_ENV} is not valid Unicode: {error}"),
        }
    }

    pub fn pairwise_enabled() -> bool {
        match std::env::var(PAIRWISE_ENV).as_deref() {
            Err(std::env::VarError::NotPresent) | Ok("0") => false,
            Ok("1") => true,
            Ok(other) => panic!("{PAIRWISE_ENV} must be 0 or 1, got {other:?}"),
            Err(error) => panic!("{PAIRWISE_ENV} is not valid Unicode: {error}"),
        }
    }

    #[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
    pub struct NecessityEvidence {
        pub program: String,
        pub selector_key: String,
        pub selector_index: usize,
        pub epoch: usize,
        pub raw_families: BTreeSet<String>,
        pub necessary_families: BTreeSet<String>,
        pub own_assume_necessary_sites: BTreeSet<String>,
        pub causal_bucket: CausalBucket,
        #[serde(default)]
        pub pair_removal: Option<PairRemovalEvidence>,
    }

    #[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
    pub struct FunctionPrecisionRecord {
        pub program: String,
        pub function: String,
        pub required_precision: u8,
        pub final_precision: u8,
        pub class: PrecisionClass,
        pub owning_locals: usize,
    }

    #[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
    pub struct ProductionPrecisionEvidence {
        pub program: String,
        pub functions: Vec<FunctionPrecisionRecord>,
        pub field_owning_not_applicable: usize,
        pub total_owning: usize,
    }

    #[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
    pub struct BoxDecisionEvidence {
        pub program: String,
        pub counts: BoxDecisionCounts,
    }

    thread_local! {
        static REMOVAL_FILTER: RefCell<Option<RemovalFilter>> = const { RefCell::new(None) };
    }

    pub fn with_removal_filter<T>(filter: RemovalFilter, f: impl FnOnce() -> T) -> T {
        struct Restore(Option<RemovalFilter>);
        impl Drop for Restore {
            fn drop(&mut self) {
                REMOVAL_FILTER.with(|slot| {
                    slot.replace(self.0.take());
                });
            }
        }
        let _restore = Restore(REMOVAL_FILTER.with(|slot| slot.replace(Some(filter))));
        f()
    }

    pub fn removal_filter_active() -> bool {
        REMOVAL_FILTER.with(|slot| slot.borrow().is_some())
    }

    pub fn suppresses_label(label: impl FnOnce() -> String) -> bool {
        let filter = REMOVAL_FILTER.with(|slot| *slot.borrow());
        let Some(filter) = filter else {
            return false;
        };
        let label = label();
        let family = crate::analyses::borrow_ownership::solver::core_label_family(&label)
            .unwrap_or_else(|| panic!("unrecognized hard-constraint family: {label}"));
        match filter {
            RemovalFilter::Family(suppressed) => family == suppressed,
            RemovalFilter::FamilyPair(suppressed) => suppressed.contains(&family),
            RemovalFilter::OwnAssumeSite(site) => {
                family == "own-assume"
                    && crate::analyses::borrow_ownership::solver::current_own_assume_site() == site
            }
        }
    }

    pub fn inactive_filter_probe(label: impl FnOnce() -> String) -> FilterProbe {
        debug_assert!(!removal_filter_active());
        let label_evaluated = Cell::new(false);
        let decision = if removal_filter_active() {
            let suppressed = suppresses_label(|| {
                label_evaluated.set(true);
                label()
            });
            if suppressed {
                HardConstraintDecision::Suppress
            } else {
                HardConstraintDecision::Assert
            }
        } else {
            HardConstraintDecision::Assert
        };
        FilterProbe {
            decision,
            label_evaluated: label_evaluated.get(),
            tracking_markers: 0,
        }
    }

    pub fn active_filter_probe(
        family: &'static str,
        label: impl FnOnce() -> String,
    ) -> FilterProbe {
        with_removal_filter(RemovalFilter::Family(family), || {
            let label_evaluated = Cell::new(false);
            let suppressed = suppresses_label(|| {
                label_evaluated.set(true);
                label()
            });
            FilterProbe {
                decision: if suppressed {
                    HardConstraintDecision::Suppress
                } else {
                    HardConstraintDecision::Assert
                },
                label_evaluated: label_evaluated.get(),
                tracking_markers: 0,
            }
        })
    }

    pub fn replay_matches_official(expected: &[usize], actual: &[usize]) -> bool {
        expected == actual
    }

    pub fn removal_is_necessary(result_is_sat: bool) -> bool {
        result_is_sat
    }

    pub fn completed_pair_removal_evidence(
        outcomes: Vec<PairRemovalOutcome>,
    ) -> PairRemovalEvidence {
        assert_eq!(
            outcomes.len(),
            10,
            "completed joint row must contain exactly ten pair-removal outcomes"
        );
        let actual_pairs = outcomes
            .iter()
            .map(|outcome| outcome.pair.clone())
            .collect::<BTreeSet<_>>();
        let expected_pairs = pairwise_removal_pairs()
            .into_iter()
            .map(FamilyPair::new)
            .collect::<BTreeSet<_>>();
        assert_eq!(
            actual_pairs, expected_pairs,
            "completed joint row must contain the ten canonical distinct family pairs"
        );
        let minimal_sat_pairs = outcomes
            .iter()
            .filter(|outcome| outcome.result_is_sat)
            .map(|outcome| outcome.pair.clone())
            .collect::<BTreeSet<_>>();
        PairRemovalEvidence {
            outcomes,
            minimal_sat_pairs,
        }
    }

    pub fn summarize_pair_removals(
        records: &[NecessityEvidence],
        programs: &[&str],
    ) -> PairRemovalSummary {
        let canonical_pairs = pairwise_removal_pairs()
            .into_iter()
            .map(FamilyPair::new)
            .collect::<Vec<_>>();
        let mut pair_frequency = canonical_pairs
            .iter()
            .cloned()
            .map(|pair| (pair, 0usize))
            .collect::<BTreeMap<_, _>>();
        let mut by_program = programs
            .iter()
            .map(|program| (*program, (0usize, pair_frequency.clone(), 0usize)))
            .collect::<BTreeMap<_, _>>();
        let mut selector_csv = String::from(
            "program,selector_key,selector_index,epoch,minimal_pairs,minimal_pair_count,no_pair\n",
        );
        let mut no_pair_csv = String::from("program,selector_key,selector_index,epoch\n");
        let mut joint_rows = 0usize;
        let mut recovered_rows = 0usize;
        let mut no_pair_rows = 0usize;

        for record in records {
            let is_joint = record.causal_bucket == CausalBucket::JointNoSingleFamilyNecessity;
            if !is_joint {
                assert!(
                    record.pair_removal.is_none(),
                    "singleton-necessary row contains pair-removal evidence"
                );
                continue;
            }
            let pair_removal = record
                .pair_removal
                .as_ref()
                .expect("joint row lacks completed pair-removal evidence");
            let program = by_program
                .get_mut(record.program.as_str())
                .unwrap_or_else(|| {
                    panic!("pair-removal row has unknown program {}", record.program)
                });
            joint_rows += 1;
            program.0 += 1;
            recovered_rows += usize::from(!pair_removal.minimal_sat_pairs.is_empty());
            no_pair_rows += usize::from(pair_removal.no_pair());
            program.2 += usize::from(pair_removal.no_pair());
            for pair in &pair_removal.minimal_sat_pairs {
                *pair_frequency
                    .get_mut(pair)
                    .expect("noncanonical minimal family pair") += 1;
                *program
                    .1
                    .get_mut(pair)
                    .expect("noncanonical per-program family pair") += 1;
            }
            let minimal_pairs = pair_removal
                .minimal_sat_pairs
                .iter()
                .map(FamilyPair::label)
                .collect::<Vec<_>>()
                .join(";");
            selector_csv.push_str(&format!(
                "{},{},{},{},{minimal_pairs},{},{}\n",
                record.program,
                record.selector_key,
                record.selector_index,
                record.epoch,
                pair_removal.minimal_sat_pairs.len(),
                pair_removal.no_pair(),
            ));
            if pair_removal.no_pair() {
                no_pair_csv.push_str(&format!(
                    "{},{},{},{}\n",
                    record.program, record.selector_key, record.selector_index, record.epoch
                ));
            }
        }

        let mut frequency_csv = String::from("family_a,family_b,unblocked_rows\n");
        for pair in &canonical_pairs {
            frequency_csv.push_str(&format!(
                "{},{},{}\n",
                pair.first, pair.second, pair_frequency[pair]
            ));
        }
        let pair_headers = canonical_pairs
            .iter()
            .map(FamilyPair::label)
            .collect::<Vec<_>>()
            .join(",");
        let mut program_csv = format!("program,joint_rows,{pair_headers},no_pair\n");
        for program in programs {
            let (program_joint, frequencies, program_no_pair) = &by_program[program];
            program_csv.push_str(&format!("{program},{program_joint}"));
            for pair in &canonical_pairs {
                program_csv.push_str(&format!(",{}", frequencies[pair]));
            }
            program_csv.push_str(&format!(",{program_no_pair}\n"));
        }

        PairRemovalSummary {
            selector_csv,
            frequency_csv,
            program_csv,
            no_pair_csv,
            pair_frequency,
            joint_rows,
            recovered_rows,
            no_pair_rows,
        }
    }

    pub fn dominant_pair_summary(
        pair_frequency: &BTreeMap<FamilyPair, usize>,
        coverage_complete: bool,
    ) -> Option<(BTreeSet<FamilyPair>, usize)> {
        if !coverage_complete {
            return None;
        }
        let dominant_count = pair_frequency.values().copied().max().unwrap_or(0);
        let dominant_pairs = if dominant_count == 0 {
            BTreeSet::new()
        } else {
            pair_frequency
                .iter()
                .filter(|(_, count)| **count == dominant_count)
                .map(|(pair, _)| pair.clone())
                .collect()
        };
        Some((dominant_pairs, dominant_count))
    }

    pub fn causal_bucket(necessary_families: &[&str]) -> CausalBucket {
        match necessary_families {
            [] => CausalBucket::JointNoSingleFamilyNecessity,
            ["own-assume"] => CausalBucket::SoleOwnAssume,
            _ => CausalBucket::Other,
        }
    }

    pub fn read_family_matrix(path: &Path) -> Result<BTreeMap<String, BTreeSet<String>>, String> {
        let input = fs::read_to_string(path)
            .map_err(|error| format!("read family matrix {}: {error}", path.display()))?;
        let mut lines = input.lines();
        let header = lines
            .next()
            .ok_or_else(|| "family matrix is empty".to_string())?;
        if !header.starts_with("program,selector_key,phase,raw_families,") {
            return Err(format!("unrecognized family matrix header: {header}"));
        }
        let mut matrix = BTreeMap::new();
        for (line_index, line) in lines.enumerate() {
            if line.trim().is_empty() {
                continue;
            }
            let fields = line.split(',').collect::<Vec<_>>();
            if fields.len() != 9 {
                return Err(format!(
                    "family matrix line {} has {} fields, expected 9",
                    line_index + 2,
                    fields.len()
                ));
            }
            let key = fields[1].to_string();
            let families = fields[3]
                .split('+')
                .filter(|family| !family.is_empty())
                .map(str::to_string)
                .collect::<BTreeSet<_>>();
            if matrix.insert(key.clone(), families).is_some() {
                return Err(format!("duplicate family-matrix selector key: {key}"));
            }
        }
        Ok(matrix)
    }

    pub fn write_json<T: Serialize>(path: &Path, value: &T) -> Result<(), String> {
        let encoded = serde_json::to_string_pretty(value)
            .map_err(|error| format!("encode {}: {error}", path.display()))?;
        fs::write(path, format!("{encoded}\n"))
            .map_err(|error| format!("write {}: {error}", path.display()))
    }

    pub fn read_json<T: for<'de> Deserialize<'de>>(path: &Path) -> Result<T, String> {
        let encoded = fs::read_to_string(path)
            .map_err(|error| format!("read {}: {error}", path.display()))?;
        serde_json::from_str(&encoded).map_err(|error| format!("parse {}: {error}", path.display()))
    }

    pub fn classify_assume_site(label: &str) -> AssumeSite {
        [
            AssumeSite::OpaqueCallArg,
            AssumeSite::LibcRule,
            AssumeSite::LocalWrapper,
            AssumeSite::SsaTransfer,
            AssumeSite::TemporaryFinalization,
            AssumeSite::CastOrDepth,
            AssumeSite::OtherInternal,
        ]
        .into_iter()
        .find(|site| label.contains(&format!("[{}]", site.as_str())))
        .unwrap_or(AssumeSite::OtherInternal)
    }

    pub fn precision_class(final_precision: u8, required_precision: u8) -> PrecisionClass {
        if final_precision == 0 {
            PrecisionClass::Dummy
        } else if final_precision < required_precision {
            PrecisionClass::Degraded
        } else {
            PrecisionClass::Full
        }
    }

    pub fn owning_precision_function(owner: OwnerClass) -> Option<&'static str> {
        match owner {
            OwnerClass::Local => Some("function"),
            OwnerClass::Field => None,
        }
    }

    pub fn parse_pointer_diagnostics(input: &str) -> Result<BoxDecisionCounts, String> {
        let mut counts = BoxDecisionCounts::default();
        for line in input
            .lines()
            .filter(|line| line.starts_with("[pointer-decision] subject="))
        {
            let final_kind = line
                .split_whitespace()
                .find_map(|field| field.strip_prefix("final="))
                .ok_or_else(|| format!("pointer decision lacks final kind: {line}"))?;
            if !matches!(
                final_kind,
                "Box" | "OptBox" | "BoxedSlice" | "OptBoxedSlice"
            ) {
                continue;
            }
            if line.contains("subject=local ") {
                counts.locals += 1;
                counts.d0_locals += 1;
            } else if line.contains("subject=param ") {
                counts.params += 1;
            } else if line.contains("subject=return ") {
                counts.returns += 1;
            } else if line.contains("subject=field ") {
                counts.fields += 1;
            } else {
                return Err(format!("unrecognized pointer-decision subject: {line}"));
            }
        }
        Ok(counts)
    }

    pub fn retry_status(first: &str, retry: Option<&str>) -> RetryStatus {
        match (first, retry) {
            ("ok", _) => RetryStatus::CompleteFirstPass,
            ("timeout" | "oom-kill", Some("ok")) => RetryStatus::CompleteAfterRetry,
            ("timeout" | "oom-kill", Some("timeout" | "oom-kill") | None) => {
                RetryStatus::ResourceDeferred
            }
            (other, _) => panic!("correctness failure is not a retry status: {other}"),
        }
    }

    #[cfg(test)]
    mod tests {
        use std::cell::Cell;

        use super::*;

        #[test]
        fn diagnostic_package_inactive_filter_is_byte_path_inert() {
            let called = Cell::new(false);
            let got = inactive_filter_probe(|| {
                called.set(true);
                "own-linear(x+y=z)".to_string()
            });
            assert_eq!(
                (got.decision, got.label_evaluated, called.get()),
                (HardConstraintDecision::Assert, false, false)
            );
        }

        #[test]
        fn diagnostic_package_active_filter_is_untracked() {
            let got = active_filter_probe("own-linear", || "own-linear(x+y=z)".to_string());
            assert_eq!(
                (got.decision, got.label_evaluated, got.tracking_markers),
                (HardConstraintDecision::Suppress, true, 0)
            );
        }

        #[test]
        fn diagnostic_package_pair_removal_universe_is_canonical_and_complete() {
            assert_eq!(
                PAIRWISE_REMOVAL_FAMILIES,
                [
                    "own-equal",
                    "own-assume",
                    "own-linear",
                    "kind-equate",
                    "link-own",
                ]
            );
            assert_eq!(
                pairwise_removal_pairs(),
                vec![
                    ["own-equal", "own-assume"],
                    ["own-equal", "own-linear"],
                    ["own-equal", "kind-equate"],
                    ["own-equal", "link-own"],
                    ["own-assume", "own-linear"],
                    ["own-assume", "kind-equate"],
                    ["own-assume", "link-own"],
                    ["own-linear", "kind-equate"],
                    ["own-linear", "link-own"],
                    ["kind-equate", "link-own"],
                ]
            );
            assert_eq!(
                pairwise_removal_pairs()
                    .into_iter()
                    .collect::<BTreeSet<_>>()
                    .len(),
                10
            );
        }

        #[test]
        fn diagnostic_package_pair_filter_suppresses_either_family_untracked() {
            with_removal_filter(RemovalFilter::FamilyPair(["own-equal", "link-own"]), || {
                assert!(suppresses_label(|| "own-equal(x=y)".to_string()));
                assert!(suppresses_label(|| "link-own(x=y)".to_string()));
                assert!(!suppresses_label(|| "own-linear(x+y=z)".to_string()));
            });
            assert!(!removal_filter_active());
        }

        #[test]
        fn diagnostic_package_pair_evidence_requires_all_ten_outcomes() {
            let outcomes = pairwise_removal_pairs()
                .into_iter()
                .map(|pair| PairRemovalOutcome::new(pair, pair == ["own-equal", "link-own"]))
                .collect();
            let evidence = completed_pair_removal_evidence(outcomes);
            assert_eq!(
                evidence.minimal_sat_pairs,
                BTreeSet::from([FamilyPair::new(["own-equal", "link-own"])])
            );
            assert!(!evidence.no_pair());
            assert!(
                serde_json::to_value(&evidence)
                    .expect("serialize pair evidence")
                    .get("no_pair")
                    .is_none(),
                "no-pair status must be derived from the SAT-pair set"
            );

            let no_pair = completed_pair_removal_evidence(
                pairwise_removal_pairs()
                    .into_iter()
                    .map(|pair| PairRemovalOutcome::new(pair, false))
                    .collect(),
            );
            assert!(no_pair.minimal_sat_pairs.is_empty());
            assert!(no_pair.no_pair());

            assert!(
                std::panic::catch_unwind(|| {
                    completed_pair_removal_evidence(
                        pairwise_removal_pairs()[..9]
                            .iter()
                            .copied()
                            .map(|pair| PairRemovalOutcome::new(pair, false))
                            .collect(),
                    )
                })
                .is_err()
            );

            assert!(
                std::panic::catch_unwind(|| {
                    let mut outcomes = pairwise_removal_pairs()
                        .into_iter()
                        .map(|pair| PairRemovalOutcome::new(pair, false))
                        .collect::<Vec<_>>();
                    outcomes[9] = outcomes[8].clone();
                    completed_pair_removal_evidence(outcomes)
                })
                .is_err()
            );
        }

        #[test]
        fn diagnostic_package_pair_summary_covers_frequency_programs_and_no_pair() {
            let pair = ["own-equal", "kind-equate"];
            let joint_record =
                |program: &str, selector_index: usize, sat_pair: Option<[&str; 2]>| {
                    NecessityEvidence {
                        program: program.to_string(),
                        selector_key: format!("{program}/source:{selector_index}"),
                        selector_index,
                        epoch: 0,
                        raw_families: BTreeSet::new(),
                        necessary_families: BTreeSet::new(),
                        own_assume_necessary_sites: BTreeSet::new(),
                        causal_bucket: CausalBucket::JointNoSingleFamilyNecessity,
                        pair_removal: Some(completed_pair_removal_evidence(
                            pairwise_removal_pairs()
                                .into_iter()
                                .map(|candidate| {
                                    PairRemovalOutcome::new(candidate, Some(candidate) == sat_pair)
                                })
                                .collect(),
                        )),
                    }
                };
            let records = vec![
                joint_record("lil", 5, Some(pair)),
                joint_record("buffer", 1, None),
            ];
            let summary = summarize_pair_removals(&records, &["buffer", "lil", "zero"]);

            assert_eq!(
                (
                    summary.joint_rows,
                    summary.recovered_rows,
                    summary.no_pair_rows
                ),
                (2, 1, 1)
            );
            assert_eq!(
                summary.pair_frequency[&FamilyPair::new(pair)],
                1,
                "the SAT pair must count once"
            );
            assert_eq!(summary.pair_frequency.len(), 10);
            assert!(
                summary
                    .selector_csv
                    .contains("lil,lil/source:5,5,0,own-equal+kind-equate,1,false")
            );
            assert!(summary.no_pair_csv.contains("buffer,buffer/source:1,1,0"));
            assert!(summary.program_csv.contains("zero,0,0,0,0,0,0,0,0,0,0,0,0"));
        }

        #[test]
        fn diagnostic_package_pair_dominance_requires_complete_coverage() {
            let frequencies = pairwise_removal_pairs()
                .into_iter()
                .map(|pair| (FamilyPair::new(pair), 0usize))
                .collect::<BTreeMap<_, _>>();
            assert_eq!(dominant_pair_summary(&frequencies, false), None);
            assert_eq!(
                dominant_pair_summary(&frequencies, true),
                Some((BTreeSet::new(), 0))
            );

            let mut tied = frequencies;
            tied.insert(FamilyPair::new(["own-equal", "own-assume"]), 63);
            tied.insert(FamilyPair::new(["own-equal", "kind-equate"]), 63);
            assert_eq!(
                dominant_pair_summary(&tied, true),
                Some((
                    BTreeSet::from([
                        FamilyPair::new(["own-equal", "own-assume"]),
                        FamilyPair::new(["own-equal", "kind-equate"]),
                    ]),
                    63,
                ))
            );
        }

        #[test]
        fn diagnostic_package_replay_requires_exact_selector_sets() {
            assert!(replay_matches_official(&[0, 2, 7], &[0, 2, 7]));
        }

        #[test]
        fn diagnostic_package_sat_removal_is_necessary_and_all_false_is_joint() {
            assert_eq!(
                (
                    removal_is_necessary(true),
                    causal_bucket(&[]),
                    causal_bucket(&["own-assume"])
                ),
                (
                    true,
                    CausalBucket::JointNoSingleFamilyNecessity,
                    CausalBucket::SoleOwnAssume
                )
            );
        }

        #[test]
        fn diagnostic_package_tags_assume_provenance() {
            assert_eq!(
                [
                    classify_assume_site("own-assume[opaque-call-arg](v1=false)"),
                    classify_assume_site("own-assume[libc-rule](v2=false)"),
                    classify_assume_site("own-assume[local-wrapper](v3=false)"),
                ],
                [
                    AssumeSite::OpaqueCallArg,
                    AssumeSite::LibcRule,
                    AssumeSite::LocalWrapper,
                ]
            );
        }

        #[test]
        fn diagnostic_package_precision_has_full_degraded_dummy_trichotomy() {
            assert_eq!(
                [
                    precision_class(2, 2),
                    precision_class(1, 2),
                    precision_class(0, 2),
                ],
                [
                    PrecisionClass::Full,
                    PrecisionClass::Degraded,
                    PrecisionClass::Dummy,
                ]
            );
        }

        #[test]
        fn diagnostic_package_fields_have_no_function_precision() {
            assert_eq!(owning_precision_function(OwnerClass::Field), None);
        }

        #[test]
        fn diagnostic_package_parses_final_box_family_subjects() {
            assert!(crate::rewriter::decision_snapshot_pre_transform_enabled_from_value(Some("1")));
            assert!(!crate::rewriter::decision_snapshot_pre_transform_enabled_from_value(None));
            assert!(
                std::panic::catch_unwind(|| {
                    crate::rewriter::decision_snapshot_pre_transform_enabled_from_value(Some(
                        "true",
                    ))
                })
                .is_err()
            );
            let input = "\
[pointer-decision] subject=local fn=a name=x original=*mut i32 span=s final=Box\n\
[pointer-decision] subject=param fn=a index=0 name=p original=*mut i32 span=s final=OptBox\n\
[pointer-decision] subject=return fn=a original=*mut i32 final=BoxedSlice\n\
[pointer-decision] subject=field field=S.f original=*mut i32 final=OptBoxedSlice\n";
            assert_eq!(
                parse_pointer_diagnostics(input).expect("pointer diagnostics"),
                BoxDecisionCounts {
                    locals: 1,
                    params: 1,
                    returns: 1,
                    fields: 1,
                    d0_locals: 1,
                }
            );
        }

        #[test]
        fn diagnostic_package_resource_retry_contract_is_deterministic() {
            assert_eq!(
                retry_status("timeout", Some("ok")),
                RetryStatus::CompleteAfterRetry
            );
        }
    }
}

/// Measurement-only report contract for the source-selector leak diagnosis.
///
/// The official untracked solve remains authoritative for selector choices.
/// A separate tracked reconstruction consumes these records with the choices
/// imposed and extracts hard-family cores; nothing in this module changes a
/// production solver decision.
mod selector_leak_diagnosis {
    use std::{
        collections::{BTreeMap, BTreeSet},
        fs,
        path::Path,
    };

    use serde::{Deserialize, Serialize};

    use crate::analyses::borrow_ownership::{
        borrow_verify::ModeACommitTrace,
        slots::SlotId,
        solver::{
            SelectorTrace, SelectorTraceOutcome as SolverOutcome,
            SelectorTracePhase as SolverPhase, SlotRef,
        },
    };

    pub const ENV: &str = "CRAT_BOC1_SELECTOR_LEAK_DIAG";

    pub fn enabled() -> bool {
        match std::env::var(ENV).as_deref() {
            Err(std::env::VarError::NotPresent) | Ok("0") => false,
            Ok("1") => true,
            Ok(other) => panic!("{ENV} must be 0 or 1, got {other:?}"),
            Err(error) => panic!("{ENV} is not valid Unicode: {error}"),
        }
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
    pub enum SelectorClass {
        Source,
        Sink,
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
    pub enum TracePhase {
        Drop,
        Reenable,
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
    pub enum TraceOutcome {
        Dropped,
        Restored,
        StayedDropped,
    }

    #[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
    pub struct TraceEvent {
        pub epoch: usize,
        pub phase: TracePhase,
        pub selector_index: usize,
        pub class: SelectorClass,
        pub active_before: Vec<usize>,
        pub core_selectors: Vec<usize>,
        pub outcome: TraceOutcome,
    }

    #[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
    pub struct CommitEvent {
        pub round: usize,
        pub target: String,
        pub issuer: Option<String>,
        pub requirers: Vec<String>,
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
    pub enum OutParamTag {
        Crosses,
        DoesNotCross,
        Untagged,
    }

    #[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
    pub struct CoreRecord {
        pub program: String,
        pub selector_key: String,
        pub phase: TracePhase,
        pub raw_families: BTreeSet<String>,
        pub minimized_families: BTreeSet<String>,
        pub minimized: bool,
        pub reenable_outcome: TraceOutcome,
        pub out_param_tag: OutParamTag,
        pub commit_origin: Option<String>,
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
    pub enum PortableSlot {
        Field { slot: usize },
        Local { function: usize, slot: usize },
    }

    #[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
    pub struct PortableCommit {
        pub round: usize,
        pub target: PortableSlot,
        pub issuer: Option<PortableSlot>,
        pub requirers: Vec<PortableSlot>,
    }

    #[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
    pub struct EpochTrace {
        pub events: Vec<TraceEvent>,
        pub final_dropped: Vec<usize>,
    }

    #[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
    pub struct OfficialTrace {
        pub program: String,
        pub code_sha: String,
        pub n_sources: usize,
        pub total_selectors: usize,
        pub epochs: Vec<EpochTrace>,
        pub commits: Vec<PortableCommit>,
    }

    #[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
    pub struct CoreEvidence {
        pub program: String,
        pub selector_key: String,
        pub selector_index: usize,
        pub class: SelectorClass,
        pub epoch: usize,
        pub phase: TracePhase,
        pub outcome: TraceOutcome,
        pub active_before: Vec<usize>,
        pub official_selector_core: Vec<usize>,
        pub raw_labels: Vec<String>,
        pub raw_families: BTreeSet<String>,
        pub minimized_labels: Vec<String>,
        pub minimized_families: BTreeSet<String>,
        pub minimized: bool,
        pub out_param_tag: OutParamTag,
        pub commit_origins: Vec<String>,
    }

    #[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
    pub struct DetailEvidence {
        pub program: String,
        pub selector_key: String,
        pub selector_index: usize,
        pub epoch: usize,
        pub raw_labels: Vec<String>,
        pub raw_families: BTreeSet<String>,
        pub minimized_labels: Vec<String>,
        pub minimized_families: BTreeSet<String>,
        pub minimized: bool,
        pub commit_origins: Vec<String>,
    }

    fn phase(phase: SolverPhase) -> TracePhase {
        match phase {
            SolverPhase::Drop => TracePhase::Drop,
            SolverPhase::Reenable => TracePhase::Reenable,
        }
    }

    fn outcome(outcome: SolverOutcome) -> TraceOutcome {
        match outcome {
            SolverOutcome::Dropped => TraceOutcome::Dropped,
            SolverOutcome::Restored => TraceOutcome::Restored,
            SolverOutcome::StayedDropped => TraceOutcome::StayedDropped,
        }
    }

    fn portable_slot(functions: &[rustc_span::def_id::LocalDefId], slot: SlotRef) -> PortableSlot {
        match slot {
            SlotRef::Field(slot) => PortableSlot::Field { slot: slot.index() },
            SlotRef::Local(function, slot) => PortableSlot::Local {
                function: functions
                    .iter()
                    .position(|candidate| *candidate == function)
                    .unwrap_or_else(|| panic!("commit references foreign function {function:?}")),
                slot: slot.index(),
            },
        }
    }

    pub fn restore_slot(
        functions: &[rustc_span::def_id::LocalDefId],
        slot: PortableSlot,
    ) -> SlotRef {
        match slot {
            PortableSlot::Field { slot } => SlotRef::Field(SlotId::from_usize(slot)),
            PortableSlot::Local { function, slot } => SlotRef::Local(
                *functions
                    .get(function)
                    .unwrap_or_else(|| panic!("portable function index {function} out of range")),
                SlotId::from_usize(slot),
            ),
        }
    }

    pub fn portable_slot_key(
        tcx: rustc_middle::ty::TyCtxt<'_>,
        functions: &[rustc_span::def_id::LocalDefId],
        slot: PortableSlot,
    ) -> String {
        match slot {
            PortableSlot::Field { slot } => format!("field:{slot}"),
            PortableSlot::Local { function, slot } => {
                let did = functions
                    .get(function)
                    .unwrap_or_else(|| panic!("portable function index {function} out of range"));
                format!("{}:{slot}", tcx.def_path_str(did.to_def_id()))
            }
        }
    }

    pub fn official_trace(
        program: &str,
        code_sha: &str,
        functions: &[rustc_span::def_id::LocalDefId],
        trace: SelectorTrace,
        commits: Vec<ModeACommitTrace>,
    ) -> OfficialTrace {
        let epochs = trace
            .epochs
            .into_iter()
            .map(|epoch| EpochTrace {
                events: epoch
                    .events
                    .into_iter()
                    .map(|event| TraceEvent {
                        epoch: event.epoch,
                        phase: phase(event.phase),
                        selector_index: event.selector_index,
                        class: if event.selector_index < trace.n_sources {
                            SelectorClass::Source
                        } else {
                            SelectorClass::Sink
                        },
                        active_before: event.active_before,
                        core_selectors: event.core_selectors,
                        outcome: outcome(event.outcome),
                    })
                    .collect(),
                final_dropped: epoch.final_dropped,
            })
            .collect();
        let commits = commits
            .into_iter()
            .map(|commit| PortableCommit {
                round: commit.round,
                target: portable_slot(functions, commit.target),
                issuer: commit
                    .conflict
                    .issuer
                    .map(|slot| portable_slot(functions, slot)),
                requirers: commit
                    .conflict
                    .requirers
                    .into_iter()
                    .map(|slot| portable_slot(functions, slot))
                    .collect(),
            })
            .collect();
        OfficialTrace {
            program: program.to_string(),
            code_sha: code_sha.to_string(),
            n_sources: trace.n_sources,
            total_selectors: trace.total,
            epochs,
            commits,
        }
    }

    pub fn write_official_trace(path: &Path, trace: &OfficialTrace) -> Result<(), String> {
        let encoded = serde_json::to_string_pretty(trace)
            .map_err(|error| format!("encode official selector trace: {error}"))?;
        fs::write(path, format!("{encoded}\n"))
            .map_err(|error| format!("write {}: {error}", path.display()))
    }

    pub fn read_official_trace(path: &Path) -> Result<OfficialTrace, String> {
        let encoded = fs::read_to_string(path)
            .map_err(|error| format!("read {}: {error}", path.display()))?;
        serde_json::from_str(&encoded).map_err(|error| format!("parse {}: {error}", path.display()))
    }

    pub fn write_core_evidence(path: &Path, evidence: &[CoreEvidence]) -> Result<(), String> {
        let mut output = String::new();
        for record in evidence {
            output.push_str(
                &serde_json::to_string(record)
                    .map_err(|error| format!("encode selector core evidence: {error}"))?,
            );
            output.push('\n');
        }
        fs::write(path, output).map_err(|error| format!("write {}: {error}", path.display()))
    }

    pub fn read_core_evidence(path: &Path) -> Result<Vec<CoreEvidence>, String> {
        let input = fs::read_to_string(path)
            .map_err(|error| format!("read {}: {error}", path.display()))?;
        input
            .lines()
            .filter(|line| !line.trim().is_empty())
            .map(|line| {
                serde_json::from_str(line)
                    .map_err(|error| format!("parse {}: {error}", path.display()))
            })
            .collect()
    }

    pub fn write_detail_evidence(path: &Path, evidence: &DetailEvidence) -> Result<(), String> {
        let encoded = serde_json::to_string_pretty(evidence)
            .map_err(|error| format!("encode selector detail evidence: {error}"))?;
        fs::write(path, format!("{encoded}\n"))
            .map_err(|error| format!("write {}: {error}", path.display()))
    }

    pub fn read_detail_evidence(path: &Path) -> Result<DetailEvidence, String> {
        let encoded = fs::read_to_string(path)
            .map_err(|error| format!("read {}: {error}", path.display()))?;
        serde_json::from_str(&encoded).map_err(|error| format!("parse {}: {error}", path.display()))
    }

    pub fn final_records(
        evidence: &[CoreEvidence],
        class: SelectorClass,
    ) -> Result<Vec<CoreRecord>, String> {
        final_evidence(evidence, class)
            .into_iter()
            .map(|record| {
                if record.raw_labels.is_empty() {
                    return Err(format!(
                        "final dropped selector lacks an UNSAT core: {}",
                        record.selector_key
                    ));
                }
                let commits =
                    (!record.commit_origins.is_empty()).then(|| record.commit_origins.join(" || "));
                Ok(CoreRecord {
                    program: record.program.clone(),
                    selector_key: record.selector_key.clone(),
                    phase: record.phase,
                    raw_families: record.raw_families.clone(),
                    minimized_families: record.minimized_families.clone(),
                    minimized: record.minimized,
                    reenable_outcome: record.outcome,
                    out_param_tag: record.out_param_tag,
                    commit_origin: commits,
                })
            })
            .collect()
    }

    pub fn final_evidence(evidence: &[CoreEvidence], class: SelectorClass) -> Vec<&CoreEvidence> {
        let mut latest: BTreeMap<&str, &CoreEvidence> = BTreeMap::new();
        for record in evidence.iter().filter(|record| {
            record.class == class
                && record.phase == TracePhase::Drop
                && record.outcome == TraceOutcome::StayedDropped
        }) {
            match latest.get(record.selector_key.as_str()) {
                Some(previous) if previous.epoch > record.epoch => {}
                _ => {
                    latest.insert(record.selector_key.as_str(), record);
                }
            }
        }
        latest.into_values().collect()
    }

    pub fn capture_event(enabled: bool, event: TraceEvent) -> Vec<TraceEvent> {
        enabled.then_some(event).into_iter().collect()
    }

    pub fn final_dropped(events: &[TraceEvent]) -> BTreeSet<usize> {
        let mut dropped = BTreeSet::new();
        for event in events {
            match (event.phase, event.outcome) {
                (TracePhase::Drop, TraceOutcome::Dropped)
                | (TracePhase::Reenable, TraceOutcome::StayedDropped) => {
                    dropped.insert(event.selector_index);
                }
                (TracePhase::Reenable, TraceOutcome::Restored) => {
                    dropped.remove(&event.selector_index);
                }
                _ => {}
            }
        }
        dropped
    }

    pub fn selector_key(
        program: &str,
        class: SelectorClass,
        overall_index: usize,
        n_sources: usize,
    ) -> String {
        match class {
            SelectorClass::Source => {
                assert!(
                    overall_index < n_sources,
                    "source index outside source partition"
                );
                format!("{program}/source:{overall_index}")
            }
            SelectorClass::Sink => {
                assert!(
                    overall_index >= n_sources,
                    "sink index inside source partition"
                );
                format!("{program}/sink:{}", overall_index - n_sources)
            }
        }
    }

    pub fn commits_for_epoch(epoch: usize, commits: &[CommitEvent]) -> Vec<CommitEvent> {
        let mut matching = commits
            .iter()
            .filter(|commit| commit.round == epoch)
            .cloned()
            .collect::<Vec<_>>();
        matching.sort_by(|left, right| left.target.cmp(&right.target));
        matching
    }

    pub fn validate_families<'a>(
        labels: impl IntoIterator<Item = &'a str>,
        known: &[&str],
    ) -> Result<BTreeSet<String>, String> {
        labels
            .into_iter()
            .map(|label| {
                let family = label
                    .strip_prefix("family-marker::")
                    .ok_or_else(|| format!("hard-core label is not a family marker: {label}"))?;
                known
                    .iter()
                    .copied()
                    .find(|known_family| *known_family == family)
                    .map(str::to_string)
                    .ok_or_else(|| format!("unrecognized hard-family marker: {label}"))
            })
            .collect()
    }

    pub fn minimized_claim(core_len: usize, saw_unknown: bool, cap: usize) -> bool {
        core_len <= cap && !saw_unknown
    }

    pub fn borrow_commit_origin(labels: &[String], commits: &[CommitEvent]) -> Option<String> {
        if !labels
            .iter()
            .any(|label| label.contains("borrow-exclusion"))
        {
            return None;
        }
        let commit = commits.iter().find(|commit| {
            labels
                .iter()
                .any(|label| label.contains("borrow-exclusion") && label.contains(&commit.target))
        })?;
        Some(format!(
            "round={} target={} issuer={} requirers={}",
            commit.round,
            commit.target,
            commit.issuer.as_deref().unwrap_or("-"),
            commit.requirers.join("+")
        ))
    }

    pub fn render_records(records: &[CoreRecord]) -> (String, String) {
        let programs = records
            .iter()
            .map(|record| record.program.as_str())
            .collect::<BTreeSet<_>>();
        let mut rows = String::from(
            "program,selector_key,phase,raw_families,minimized_families,minimized,\
             reenable_outcome,out_param_tag,commit_origin\n",
        );
        for record in records {
            let phase = match record.phase {
                TracePhase::Drop => "drop",
                TracePhase::Reenable => "reenable",
            };
            let outcome = match record.reenable_outcome {
                TraceOutcome::Dropped => "dropped",
                TraceOutcome::Restored => "restored",
                TraceOutcome::StayedDropped => "stayed-dropped",
            };
            let out_param = match record.out_param_tag {
                OutParamTag::Crosses => "crosses",
                OutParamTag::DoesNotCross => "does-not-cross",
                OutParamTag::Untagged => "untagged",
            };
            rows.push_str(&format!(
                "{},{},{},{},{},{},{},{},{}\n",
                record.program,
                record.selector_key,
                phase,
                record
                    .raw_families
                    .iter()
                    .cloned()
                    .collect::<Vec<_>>()
                    .join("+"),
                record
                    .minimized_families
                    .iter()
                    .cloned()
                    .collect::<Vec<_>>()
                    .join("+"),
                record.minimized,
                outcome,
                out_param,
                record.commit_origin.as_deref().unwrap_or("-"),
            ));
        }

        let mut counts: BTreeMap<String, BTreeMap<&str, usize>> = BTreeMap::new();
        for record in records {
            let families = if record.minimized {
                &record.minimized_families
            } else {
                &record.raw_families
            };
            for family in families {
                *counts
                    .entry(family.clone())
                    .or_default()
                    .entry(record.program.as_str())
                    .or_default() += 1;
            }
        }
        let mut cross_tab = format!(
            "family,{},total\n",
            programs.iter().copied().collect::<Vec<_>>().join(",")
        );
        for (family, by_program) in counts {
            let mut total = 0usize;
            cross_tab.push_str(&family);
            for program in &programs {
                let count = by_program.get(program).copied().unwrap_or(0);
                total += count;
                cross_tab.push_str(&format!(",{count}"));
            }
            cross_tab.push_str(&format!(",{total}\n"));
        }
        (rows, cross_tab)
    }

    pub fn cheap_out_param_tag(
        has_direct_selector_slot: bool,
        crosses_boundary: bool,
    ) -> OutParamTag {
        if !has_direct_selector_slot {
            OutParamTag::Untagged
        } else if crosses_boundary {
            OutParamTag::Crosses
        } else {
            OutParamTag::DoesNotCross
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        fn event(
            phase: TracePhase,
            selector_index: usize,
            class: SelectorClass,
            outcome: TraceOutcome,
        ) -> TraceEvent {
            TraceEvent {
                epoch: 0,
                phase,
                selector_index,
                class,
                active_before: vec![0, 1, 2],
                core_selectors: vec![selector_index],
                outcome,
            }
        }

        #[test]
        fn selector_leak_capture_disabled_is_inert() {
            assert!(
                capture_event(
                    false,
                    event(
                        TracePhase::Drop,
                        0,
                        SelectorClass::Source,
                        TraceOutcome::Dropped,
                    ),
                )
                .is_empty()
            );
        }

        #[test]
        fn selector_leak_source_drop_and_reenable_outcome() {
            let events = vec![
                event(
                    TracePhase::Drop,
                    0,
                    SelectorClass::Source,
                    TraceOutcome::Dropped,
                ),
                event(
                    TracePhase::Reenable,
                    0,
                    SelectorClass::Source,
                    TraceOutcome::StayedDropped,
                ),
                event(
                    TracePhase::Drop,
                    1,
                    SelectorClass::Source,
                    TraceOutcome::Dropped,
                ),
                event(
                    TracePhase::Reenable,
                    1,
                    SelectorClass::Source,
                    TraceOutcome::Restored,
                ),
            ];
            assert_eq!(final_dropped(&events), BTreeSet::from([0]));
        }

        #[test]
        fn selector_leak_mixed_trace_records_sink_first() {
            let first = event(
                TracePhase::Drop,
                2,
                SelectorClass::Sink,
                TraceOutcome::Dropped,
            );
            assert_eq!(capture_event(true, first.clone()), vec![first]);
        }

        #[test]
        fn selector_leak_canonical_keys_preserve_partition_and_order() {
            assert_eq!(
                selector_key("binn", SelectorClass::Source, 1, 2),
                "binn/source:1"
            );
            assert_eq!(
                selector_key("binn", SelectorClass::Sink, 4, 2),
                "binn/sink:2"
            );
        }

        #[test]
        fn selector_leak_rejects_unrecognized_hard_families() {
            let known = ["safe-mono", "borrow-exclusion"];
            assert_eq!(
                validate_families(
                    [
                        "family-marker::safe-mono",
                        "family-marker::borrow-exclusion",
                    ],
                    &known,
                )
                .unwrap(),
                BTreeSet::from(["borrow-exclusion".to_string(), "safe-mono".to_string()])
            );
            assert!(
                validate_families(["f::safe-mono(a=>b)"], &known)
                    .unwrap_err()
                    .contains("family marker")
            );
        }

        #[test]
        fn selector_leak_replays_commits_at_original_round_boundary() {
            let commits = vec![
                CommitEvent {
                    round: 2,
                    target: "f:1".to_string(),
                    issuer: Some("f:2".to_string()),
                    requirers: vec!["f:3".to_string()],
                },
                CommitEvent {
                    round: 1,
                    target: "g:4".to_string(),
                    issuer: None,
                    requirers: vec![],
                },
            ];
            assert!(commits_for_epoch(0, &commits).is_empty());
            assert_eq!(commits_for_epoch(1, &commits), vec![commits[1].clone()]);
            assert_eq!(commits_for_epoch(2, &commits), vec![commits[0].clone()]);
        }

        #[test]
        fn selector_leak_minimization_claim_respects_cap_and_unknown() {
            assert!(minimized_claim(50, false, 50));
            assert!(!minimized_claim(51, false, 50));
            assert!(!minimized_claim(10, true, 50));
        }

        #[test]
        fn selector_leak_borrow_commit_traces_one_conflict_hop() {
            let commits = vec![CommitEvent {
                round: 1,
                target: "Local(f,9)".to_string(),
                issuer: Some("Local(f,2)".to_string()),
                requirers: vec!["Local(f,3)".to_string()],
            }];
            let labels = vec![
                "round-1::borrow-exclusion(Some(Local(f,9)),[])".to_string(),
                "emit::safe-mono(Local(f,9)=>Local(f,8))".to_string(),
            ];
            let origin = borrow_commit_origin(&labels, &commits).expect("commit origin");
            assert!(origin.contains("target=Local(f,9)"));
            assert!(origin.contains("issuer=Local(f,2)"));
            assert!(origin.contains("requirers=Local(f,3)"));
        }

        #[test]
        fn selector_leak_renderer_and_out_param_untagged_fallback() {
            let record = CoreRecord {
                program: "bst".to_string(),
                selector_key: "bst/source:0".to_string(),
                phase: TracePhase::Drop,
                raw_families: BTreeSet::from([
                    "borrow-exclusion".to_string(),
                    "safe-mono".to_string(),
                ]),
                minimized_families: BTreeSet::new(),
                minimized: false,
                reenable_outcome: TraceOutcome::StayedDropped,
                out_param_tag: cheap_out_param_tag(false, true),
                commit_origin: Some("target=x issuer=y".to_string()),
            };
            assert_eq!(record.out_param_tag, OutParamTag::Untagged);
            assert_eq!(cheap_out_param_tag(true, true), OutParamTag::Crosses);
            assert_eq!(cheap_out_param_tag(true, false), OutParamTag::DoesNotCross);
            let (rows, cross_tab) = render_records(&[record]);
            for needle in [
                "bst/source:0",
                "borrow-exclusion",
                "safe-mono",
                "stayed-dropped",
                "untagged",
                "target=x issuer=y",
            ] {
                assert!(rows.contains(needle), "missing {needle}: {rows}");
            }
            assert!(cross_tab.contains("family,bst,total"));
            assert!(cross_tab.contains("borrow-exclusion,1,1"));
            assert!(cross_tab.contains("safe-mono,1,1"));
        }

        #[test]
        fn selector_leak_final_records_use_drop_core_not_reenable_tracking() {
            let evidence = CoreEvidence {
                program: "bst".to_string(),
                selector_key: "bst/source:0".to_string(),
                selector_index: 0,
                class: SelectorClass::Source,
                epoch: 0,
                phase: TracePhase::Drop,
                outcome: TraceOutcome::StayedDropped,
                active_before: vec![0],
                official_selector_core: vec![0],
                raw_labels: vec!["family-marker::safe-mono".to_string()],
                raw_families: BTreeSet::from(["safe-mono".to_string()]),
                minimized_labels: Vec::new(),
                minimized_families: BTreeSet::new(),
                minimized: false,
                out_param_tag: OutParamTag::Untagged,
                commit_origins: Vec::new(),
            };
            let records =
                final_records(&[evidence], SelectorClass::Source).expect("drop-phase record");
            assert_eq!(records.len(), 1);
            assert_eq!(records[0].phase, TracePhase::Drop);
            assert_eq!(records[0].reenable_outcome, TraceOutcome::StayedDropped);
        }
    }
}

/// Provenance stamp for `results.jsonl` — a line-1 `{"_provenance":{...}}` object carrying
/// the commit SHA a sweep was produced at, so a killed run that leaves a stale file cannot
/// masquerade as current data (the phantom −97.7% regression postmortem, 2026-07-10). Pure
/// and unit-tested here; the git + filesystem glue lives in `orchestrate` / `boc1_corpus`.
mod provenance {
    /// The line-1 object prepended to `results.jsonl`. Hand-built (not `to_json_line`) so it
    /// never collides with a data row; `dirty`/`unix` are informational, `sha` is the key.
    pub fn line(sha: &str, dirty: bool, unix: u64) -> String {
        format!("{{\"_provenance\":{{\"sha\":\"{sha}\",\"dirty\":{dirty},\"unix\":{unix}}}}}")
    }

    /// Extract the stamped SHA from a candidate first line; `None` if it is not a provenance
    /// stamp (e.g. a pre-guard data row `{"program":...}`).
    pub fn parse_sha(first_line: &str) -> Option<String> {
        let line = first_line.trim();
        if !line.starts_with("{\"_provenance\":") {
            return None;
        }
        let sha = line.split("\"sha\":\"").nth(1)?.split('"').next()?;
        (!sha.is_empty()).then(|| sha.to_string())
    }

    /// Decide whether an existing `results.jsonl` must be moved aside before a sweep writes.
    /// `Some(suffix)` ⇒ rename to `results.jsonl.stale-<suffix>` (SHA mismatch → the stale
    /// file's short SHA; pre-guard file with no stamp → `nostamp`). `None` ⇒ keep (no file,
    /// or the stamp matches the current SHA). Rename, never delete — preserves the forensic
    /// trail that made the phantom-regression postmortem possible.
    pub fn stale_verdict(existing_first_line: Option<&str>, current_sha: &str) -> Option<String> {
        let line = existing_first_line?;
        match parse_sha(line) {
            Some(sha) if sha == current_sha => None,
            Some(sha) => Some(sha.chars().take(8).collect()),
            None => Some("nostamp".to_string()),
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn boc1_provenance_stamp_and_stale_verdict() {
            let l = line("d2c4f828abcdef", false, 1_700_000_000);
            assert!(l.starts_with("{\"_provenance\":"), "line-1 object: {l}");
            assert_eq!(parse_sha(&l).as_deref(), Some("d2c4f828abcdef"));
            assert!(
                line("abc", true, 1).contains("\"dirty\":true"),
                "dirty flag carried"
            );
            // A data row is not a provenance stamp.
            assert_eq!(parse_sha("{\"program\":\"bst\",\"mode\":\"bo\"}"), None);
            // Fresh (SHA matches) → keep; no file → keep.
            assert_eq!(stale_verdict(Some(&l), "d2c4f828abcdef"), None);
            assert_eq!(stale_verdict(None, "d2c4f828abcdef"), None);
            // SHA mismatch → move aside under the STALE file's short SHA.
            assert_eq!(
                stale_verdict(Some(&l), "ffffffffffff").as_deref(),
                Some("d2c4f828")
            );
            // Pre-guard file (no stamp) → move aside as `nostamp` (the phantom-regression case).
            assert_eq!(
                stale_verdict(Some("{\"program\":\"bst\"}"), "d2c4f828abcdef").as_deref(),
                Some("nostamp"),
            );
        }
    }
}

/// §L2 RED — frozen base counts and the certified 26-slot recovery inventory.
///
/// This is test-harness-only. It reads accepted Mode-A models but never changes
/// the solver, validation loop, or emitted output.
mod l2_red_gate {
    use std::collections::{BTreeMap, BTreeSet};

    use super::{CorpusProgram, report::Row};

    const BASE: &str =
        include_str!("analyses/borrow_ownership/testdata/l2_rs_crown_base_ae6f334.csv");
    const TARGETS: &str =
        include_str!("analyses/borrow_ownership/testdata/l2_rs_crown_targets.csv");
    pub const ENV: &str = "CRAT_BOC1_L2_RED_GATE";

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct BaseRow {
        pub program: String,
        pub n_ref: usize,
        pub n_ref_d0: usize,
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct Target {
        pub program: String,
        pub slot: String,
        pub audit_round: usize,
    }

    pub fn enabled() -> bool {
        match std::env::var(ENV).as_deref() {
            Err(std::env::VarError::NotPresent) | Ok("0") => false,
            Ok("1") => true,
            Ok(other) => panic!("{ENV} must be 0 or 1, got {other:?}"),
            Err(error) => panic!("{ENV} is not valid Unicode: {error}"),
        }
    }

    fn data_lines(input: &str) -> impl Iterator<Item = &str> {
        input
            .lines()
            .map(str::trim)
            .filter(|line| !line.is_empty() && !line.starts_with('#'))
    }

    pub fn bases() -> Vec<BaseRow> {
        let mut lines = data_lines(BASE);
        assert_eq!(
            lines.next(),
            Some("program,n_ref,n_ref_d0"),
            "L2 RED base fixture header drifted"
        );
        lines
            .map(|line| {
                let fields: Vec<&str> = line.split(',').collect();
                assert_eq!(fields.len(), 3, "malformed L2 RED base row: {line}");
                BaseRow {
                    program: fields[0].to_string(),
                    n_ref: fields[1]
                        .parse()
                        .unwrap_or_else(|_| panic!("invalid n_ref in L2 RED base row: {line}")),
                    n_ref_d0: fields[2]
                        .parse()
                        .unwrap_or_else(|_| panic!("invalid n_ref_d0 in L2 RED base row: {line}")),
                }
            })
            .collect()
    }

    pub fn targets() -> Vec<Target> {
        let mut lines = data_lines(TARGETS);
        assert_eq!(
            lines.next(),
            Some("program,slot,audit_round"),
            "L2 RED target fixture header drifted"
        );
        lines
            .map(|line| {
                let fields: Vec<&str> = line.split(',').collect();
                assert_eq!(fields.len(), 3, "malformed L2 RED target row: {line}");
                Target {
                    program: fields[0].to_string(),
                    slot: fields[1].to_string(),
                    audit_round: fields[2].parse().unwrap_or_else(|_| {
                        panic!("invalid audit round in L2 RED target row: {line}")
                    }),
                }
            })
            .collect()
    }

    pub fn base_for(program: &str) -> BaseRow {
        bases()
            .into_iter()
            .find(|row| row.program == program)
            .unwrap_or_else(|| panic!("L2 RED base fixture has no row for {program}"))
    }

    pub fn targets_for(program: &str) -> Vec<Target> {
        targets()
            .into_iter()
            .filter(|target| target.program == program)
            .collect()
    }

    pub fn assert_fixtures(corpus: &[CorpusProgram]) {
        let bases = bases();
        let corpus_names: Vec<&str> = corpus.iter().map(|program| program.name).collect();
        let base_names: Vec<&str> = bases.iter().map(|row| row.program.as_str()).collect();
        assert_eq!(
            base_names, corpus_names,
            "L2 RED base fixture must cover the exact frozen corpus in catalog order"
        );
        assert_eq!(
            bases.iter().map(|row| row.n_ref).sum::<usize>(),
            52_810,
            "L2 RED aggregate base n_ref drifted"
        );
        assert_eq!(
            bases.iter().map(|row| row.n_ref_d0).sum::<usize>(),
            49_459,
            "L2 RED aggregate base n_ref_d0 drifted"
        );

        let targets = targets();
        assert_eq!(
            targets.len(),
            26,
            "L2 RED inventory must remain certified N=26"
        );
        let mut seen = BTreeSet::new();
        let mut by_program = BTreeMap::<String, usize>::new();
        let mut by_round = BTreeMap::<usize, usize>::new();
        for target in &targets {
            assert!(
                corpus_names.contains(&target.program.as_str()),
                "L2 RED target names unknown program {}",
                target.program
            );
            assert!(
                seen.insert((target.program.clone(), target.slot.clone())),
                "duplicate L2 RED target {}/{}",
                target.program,
                target.slot
            );
            *by_program.entry(target.program.clone()).or_default() += 1;
            *by_round.entry(target.audit_round).or_default() += 1;
        }
        assert_eq!(
            by_program.into_iter().collect::<Vec<_>>(),
            vec![
                ("binn".to_string(), 7),
                ("bzip2".to_string(), 5),
                ("libtree".to_string(), 7),
                ("lodepng".to_string(), 7),
            ],
            "L2 RED inventory program split drifted"
        );
        assert_eq!(
            by_round.into_iter().collect::<Vec<_>>(),
            vec![(1, 18), (2, 7), (3, 1)],
            "L2 RED inventory audit-round split drifted"
        );
    }

    fn usize_field(row: &Row, key: &str) -> usize {
        row.get(key)
            .unwrap_or_else(|| panic!("L2 RED row missing {key}: {row:?}"))
            .parse()
            .unwrap_or_else(|_| panic!("L2 RED row has non-numeric {key}: {row:?}"))
    }

    fn signed_field(row: &Row, key: &str) -> i64 {
        row.get(key)
            .unwrap_or_else(|| panic!("L2 RED row missing {key}: {row:?}"))
            .parse()
            .unwrap_or_else(|_| panic!("L2 RED row has non-numeric {key}: {row:?}"))
    }

    pub fn summary(rows: &[Row]) -> String {
        let accepted = rows
            .iter()
            .filter(|row| row.get("status") == Some("ok"))
            .count();
        let found = rows
            .iter()
            .filter_map(|row| row.get("l2_targets_found"))
            .filter_map(|value| value.parse::<usize>().ok())
            .sum::<usize>();
        let expected = rows
            .iter()
            .filter_map(|row| row.get("l2_targets_expected"))
            .filter_map(|value| value.parse::<usize>().ok())
            .sum::<usize>();
        let recovered = rows
            .iter()
            .filter_map(|row| row.get("l2_targets_ref"))
            .filter_map(|value| value.parse::<usize>().ok())
            .sum::<usize>();
        let n_ref = rows
            .iter()
            .filter_map(|row| row.get("n_ref"))
            .filter_map(|value| value.parse::<usize>().ok())
            .sum::<usize>();
        let base_n_ref = rows
            .iter()
            .filter_map(|row| row.get("l2_base_n_ref"))
            .filter_map(|value| value.parse::<usize>().ok())
            .sum::<usize>();
        let regressions = rows
            .iter()
            .filter(|row| {
                row.get("l2_n_ref_delta")
                    .and_then(|value| value.parse::<i64>().ok())
                    .is_some_and(|delta| delta < 0)
            })
            .count();
        let check_sat = rows
            .iter()
            .filter_map(|row| row.get("check_sat_count"))
            .filter_map(|value| value.parse::<usize>().ok())
            .sum::<usize>();
        format!(
            "L2RED accepted={accepted}/{} found={found}/{expected} recovered={recovered}/{expected} \
             n_ref={n_ref}/{base_n_ref} delta={} per_program_regressions={regressions} \
             check_sat={check_sat}",
            rows.len(),
            n_ref as i64 - base_n_ref as i64,
        )
    }

    pub fn assert_results(rows: &[Row], corpus: &[CorpusProgram]) {
        assert_eq!(
            rows.len(),
            corpus.len(),
            "L2 RED must run the complete frozen rs-crown corpus"
        );
        let actual_names: Vec<&str> = rows
            .iter()
            .map(|row| row.get("program").expect("L2 RED row has program"))
            .collect();
        let expected_names: Vec<&str> = corpus.iter().map(|program| program.name).collect();
        assert_eq!(
            actual_names, expected_names,
            "L2 RED corpus order/content drifted"
        );

        let non_accepts: Vec<(&str, &str)> = rows
            .iter()
            .filter_map(|row| {
                let status = row.get("status").unwrap_or("missing");
                (status != "ok").then(|| (row.get("program").unwrap_or("missing"), status))
            })
            .collect();
        assert!(
            non_accepts.is_empty(),
            "L2 RED requires 20/20 accepted Mode-A rows; non-accepts={non_accepts:?}"
        );
        for row in rows {
            assert_eq!(
                row.get("repair"),
                Some("mode_a"),
                "L2 RED row is not Mode-A: {row:?}"
            );
            assert_eq!(
                row.get("l2_feature"),
                Some("on"),
                "L2 flag did not reach worker: {row:?}"
            );
            assert_eq!(
                row.get("l2_diag"),
                Some("raw"),
                "L2 diagnostics did not reach worker: {row:?}"
            );
            assert_eq!(
                row.get("safe_mono"),
                Some("per_site"),
                "L2 RED row did not use the frozen per-site safety profile: {row:?}"
            );
            assert_eq!(
                row.get("mut_facts"),
                Some("on"),
                "L2 RED row did not use the frozen mutability-facts profile: {row:?}"
            );
            assert_eq!(
                row.get("z3_full_version"),
                Some("4.15.4.0"),
                "L2 RED row did not use the frozen Z3 version: {row:?}"
            );
            assert!(
                usize_field(row, "check_sat_count") > 0,
                "L2 RED row did not report solver check-sat activity: {row:?}"
            );
        }

        let expected_targets = rows
            .iter()
            .map(|row| usize_field(row, "l2_targets_expected"))
            .sum::<usize>();
        assert_eq!(expected_targets, 26, "L2 RED target denominator drifted");
        let found_targets = rows
            .iter()
            .map(|row| usize_field(row, "l2_targets_found"))
            .sum::<usize>();
        assert_eq!(
            found_targets, expected_targets,
            "L2 RED inventory slot missing or renamed; re-anchor is required"
        );

        let actual_n_ref = rows
            .iter()
            .map(|row| usize_field(row, "n_ref"))
            .sum::<usize>();
        let base_n_ref = rows
            .iter()
            .map(|row| usize_field(row, "l2_base_n_ref"))
            .sum::<usize>();
        assert_eq!(base_n_ref, 52_810, "L2 RED aggregate base n_ref drifted");
        assert!(
            actual_n_ref >= base_n_ref,
            "L2 RED violates the corpus-wide n_ref non-regression gate: \
             actual={actual_n_ref} base={base_n_ref}"
        );
        let reported_delta = rows
            .iter()
            .map(|row| signed_field(row, "l2_n_ref_delta"))
            .sum::<i64>();
        assert_eq!(
            reported_delta,
            actual_n_ref as i64 - base_n_ref as i64,
            "L2 RED per-program n_ref deltas do not sum to the aggregate delta"
        );

        let recovered = rows
            .iter()
            .map(|row| usize_field(row, "l2_targets_ref"))
            .sum::<usize>();
        assert!(
            recovered >= 22,
            "L2 RED: recovered {recovered}/26; implementation merge bar is 22/26"
        );
    }
}

// §NB4-4c-Q: re-export the collateral measurement so the RED shape tests (in `tests.rs`, outside this
// private module) validate the EXACT harness code the sweep runs, not a copy.
#[cfg(test)]
pub(crate) use run::{CollateralMeasurement, measure_collateral};

/// Per-mode analysis drivers producing report rows.
mod run {
    use std::{
        collections::{BTreeMap, BTreeSet},
        path::Path,
        time::{Duration, Instant},
    };

    use points_to::andersen;
    use rustc_hash::{FxHashMap, FxHashSet};
    use rustc_middle::ty::{TyCtxt, TyKind};
    use z3::{SatResult, ast::Bool};

    use super::{
        collect_program, crown_projection,
        ownership_diagnostic_package::{
            self, FunctionPrecisionRecord, NecessityEvidence, PairRemovalOutcome,
            ProductionPrecisionEvidence, RemovalFilter,
        },
        ownership_yield::{self, ModelKindRecord, OwnerClass, SlotRecord},
        report::Row,
        selector_leak_diagnosis::{
            self, CommitEvent, CoreEvidence, DetailEvidence, OutParamTag, SelectorClass, TracePhase,
        },
    };
    use crate::analyses::{
        borrow::{GBorrowInferCtxt, demote_pointers_iterative_with_fields},
        borrow_ownership::{
            CrateCtxt, SafeMonoMode, SlotKind,
            borrow_verify::{
                RepairMode, model_accepts_with_flows, slotref_key,
                verify_to_fixpoint_counting_with_flows, verify_to_fixpoint_with_flows,
                with_capture, with_mode_a_commit_trace,
            },
            coherence::{add_coherence, constrain_field_ownership, field_ownership_candidates},
            crate_slots::CrateSlots,
            emit_crate_ownership_constraints, l2,
            mutability_facts::{MutFacts, MutFactsMode, MutProvider},
            origins::compute_origins,
            slots::{SlotId, SlotOwner},
            solver::{
                CORE_LABEL_FAMILIES, CoreTracker, KindSolver, Selectors, SlotRef,
                with_selector_trace,
            },
            sources::collect_malloc_source_slots,
        },
    };

    fn secs(d: Duration) -> String {
        format!("{:.3}", d.as_secs_f64())
    }

    fn phase(name: &str, since: Instant) {
        eprintln!("BOC1PHASE {name} t={:.2}", since.elapsed().as_secs_f64());
    }

    fn local_key(
        tcx: TyCtxt<'_>,
        fn_did: rustc_span::def_id::LocalDefId,
        local: usize,
        depth: u8,
    ) -> String {
        format!(
            "{}::_{}@d{depth}",
            tcx.def_path_str(fn_did.to_def_id()),
            local
        )
    }

    fn field_key(
        tcx: TyCtxt<'_>,
        struct_did: rustc_span::def_id::LocalDefId,
        field_index: usize,
        depth: u8,
    ) -> String {
        format!(
            "{}::field{field_index}@d{depth}",
            tcx.def_path_str(struct_did.to_def_id())
        )
    }

    fn bo_slot_metadata(
        tcx: TyCtxt<'_>,
        slots: &CrateSlots,
        slot_ref: SlotRef,
    ) -> (String, OwnerClass, u8) {
        match slot_ref {
            SlotRef::Local(fn_did, slot_id) => {
                let slot = slots
                    .fn_local_slots
                    .get(&fn_did)
                    .unwrap_or_else(|| panic!("missing BO local universe for {fn_did:?}"))
                    .slot(slot_id);
                let SlotOwner::Local(local) = slot.owner else {
                    panic!("local SlotRef has non-local owner: {slot_ref:?}");
                };
                (
                    local_key(tcx, fn_did, local.index(), slot.depth),
                    OwnerClass::Local,
                    slot.depth,
                )
            }
            SlotRef::Field(slot_id) => {
                let slot = slots.field_slots.slot(slot_id);
                let SlotOwner::Field(field) = slot.owner else {
                    panic!("field SlotRef has non-field owner: {slot_ref:?}");
                };
                (
                    field_key(tcx, field.struct_did, field.field_index, slot.depth),
                    OwnerClass::Field,
                    slot.depth,
                )
            }
        }
    }

    fn bo_slot_records(
        tcx: TyCtxt<'_>,
        slots: &CrateSlots,
        model: &FxHashMap<SlotRef, SlotKind>,
    ) -> Vec<SlotRecord> {
        let mut records = Vec::with_capacity(model.len());
        for (&slot_ref, &kind) in model {
            let (key, owner, depth) = bo_slot_metadata(tcx, slots, slot_ref);
            records.push(SlotRecord {
                key,
                owner,
                depth,
                owning: kind == SlotKind::Owning,
                forced_output: false,
            });
        }
        records
    }

    fn bo_model_kind_records(
        tcx: TyCtxt<'_>,
        slots: &CrateSlots,
        model: &FxHashMap<SlotRef, SlotKind>,
    ) -> Vec<ModelKindRecord> {
        model
            .iter()
            .map(|(&slot_ref, &kind)| {
                let (key, owner, depth) = bo_slot_metadata(tcx, slots, slot_ref);
                ModelKindRecord {
                    key,
                    owner,
                    depth,
                    kind,
                }
            })
            .collect()
    }

    fn certified_context_enabled() -> bool {
        const ENV: &str = "CRAT_BOC1_L2_CERTIFIED_CONTEXT";
        match std::env::var(ENV).as_deref() {
            Err(std::env::VarError::NotPresent) | Ok("0") => false,
            Ok("1") => true,
            Ok(other) => panic!("{ENV} must be 0 or 1, got {other:?}"),
            Err(error) => panic!("{ENV} is not valid Unicode: {error}"),
        }
    }

    // ───────────────────────── §NB4-4c-Q collateral measurement (item-4 sizing) ─────────────────────
    //
    // Sizes the coherence-collateral Ref-loss from over-including modeled-origin slots in the
    // may-supply demotion set (Codex re-review 2026-07-17). Runs TWO real solves per program in-process
    // (the CHECK_REAL second-solver pattern): FULL demotes the whole no-borrow-origin set (the shipped
    // behavior); MINUS demotes that set with the MITIGATED over-inclusion removed. The n_ref delta
    // (MINUS − FULL) is the collateral. **MEASUREMENT-ONLY** — MINUS must NEVER ship: it un-demotes
    // legitimately-may-reach branch-joins (see `collect_overincluded_modeled_origin_slots`), so the
    // measured collateral is an UPPER BOUND on what the precise item-4 fix would recover.

    pub(crate) struct CollateralMeasurement {
        /// "no-oi" (no over-inclusion → collateral 0, no solves), "ok" (solved + anchorable), or
        /// "real-decline" (a REAL solve declined/unknown — the number is NOT trustworthy; the sweep
        /// surfaces it, post-sweep audit must see none). Codex F2a: never silently skip a decline.
        pub status: &'static str,
        pub overincl_raw: usize,
        pub overincl_mit: usize,
        /// Codex F1: the self-inclusive UPPER-BOUND over-inclusion (catches restored self-origins the
        /// mitigated set misses). `mitigated ⊆ upper`, so `collateral_upper ≥ collateral_mit`.
        pub overincl_upper: usize,
        /// FULL model counts — `Some` only when `status == "ok"` (a real FULL solve ran). The sweep
        /// anchors BOTH to the shipped MIRROR (Codex F2b: n_ref AND n_ref_d0, not just n_ref).
        pub nref_full: Option<usize>,
        pub nref_d0_full: Option<usize>,
        /// collateral = n_ref(MINUS) − n_ref(FULL); may be negative (do NOT assert ≥ 0). `_mit` uses the
        /// mitigated over-inclusion (tighter, storage-excluded), `_upper` the maximal set (the gate).
        pub collateral_mit: i64,
        pub collateral_d0_mit: i64,
        pub collateral_upper: i64,
        pub collateral_d0_upper: i64,
    }

    /// Count Ref slots (all depths) and Ref slots at depth-0 LOCAL only — the exact accounting
    /// `run_bo` uses for `n_ref` / `n_ref_d0` (field slots contribute to `n_ref` but NOT `n_ref_d0`,
    /// which is why field collateral is invisible in the d0 metric).
    fn count_refs(model: &FxHashMap<SlotRef, SlotKind>, slots: &CrateSlots) -> (usize, usize) {
        let (mut n_ref, mut n_ref_d0) = (0usize, 0usize);
        for (s, kind) in model {
            if *kind == SlotKind::Ref {
                n_ref += 1;
                if let SlotRef::Local(fn_did, sid) = s
                    && let Some(u) = slots.fn_local_slots.get(fn_did)
                    && u.slot(*sid).depth == 0
                {
                    n_ref_d0 += 1;
                }
            }
        }
        (n_ref, n_ref_d0)
    }

    /// Emit with EMPTY origins (no in-emit demotion), manually `¬ref` exactly `demote`, add coherence,
    /// and solve with the REAL `verify_to_fixpoint`. `emit_crate_ownership_constraints` reads `origins`
    /// ONLY for its demotion loop, so this reproduces the shipped pipeline with a SWAPPED demotion set.
    fn solve_with_demotion(
        program: &crate::utils::rustc::RustProgram,
        slots: &CrateSlots,
        origin_flows: &crate::analyses::borrow_ownership::origin_flow::OriginFlowResults,
        demote: &[SlotRef],
        mut_facts: &MutFacts,
    ) -> Option<FxHashMap<SlotRef, SlotKind>> {
        let empty = crate::analyses::borrow_ownership::origin_summary::OriginSummaries::default();
        let crate_ctxt = CrateCtxt::new(program);
        let solver = KindSolver::new(slots);
        let (_stats, selectors) =
            emit_crate_ownership_constraints(&crate_ctxt, slots, &empty, &solver).ok()?;
        for slot in demote {
            solver.add_borrow_exclusion(Some(*slot), &[]);
        }
        for &g in &program.functions {
            let body = program
                .tcx
                .mir_drops_elaborated_and_const_checked(g)
                .borrow();
            add_coherence(&solver, slots, g, &body);
        }
        verify_to_fixpoint_with_flows(program, slots, origin_flows, &solver, &selectors, mut_facts)
    }

    /// Measure the collateral. Returns a status-tagged struct (never panics on decline — Codex F2a).
    /// FULL preserves the SHIPPED Vec order/multiplicity (Codex F2c). Short-circuits with no solves
    /// when there is no over-inclusion (the common corpus case). Asserts every over-inclusion set ⊆
    /// FULL and `mitigated ⊆ upper` (mapping/invariant drift = hard STOP).
    pub(crate) fn measure_collateral(
        program: &crate::utils::rustc::RustProgram,
        slots: &CrateSlots,
        origins: &crate::analyses::borrow_ownership::origin_summary::OriginSummaries,
        mut_facts: &MutFacts,
    ) -> CollateralMeasurement {
        use crate::analyses::borrow_ownership::origins::{
            collect_no_borrow_origin_slots, collect_overincluded_modeled_origin_slots,
            collect_upperbound_overincluded_slots,
        };
        // FULL demotion set = the SHIPPED Vec (preserve order + multiplicity — F2c).
        let full_vec = collect_no_borrow_origin_slots(origins, slots);
        let full_set: FxHashSet<SlotRef> = full_vec.iter().copied().collect();
        let raw_set: FxHashSet<SlotRef> =
            collect_overincluded_modeled_origin_slots(origins, slots, false)
                .into_iter()
                .collect();
        let mit_set: FxHashSet<SlotRef> =
            collect_overincluded_modeled_origin_slots(origins, slots, true)
                .into_iter()
                .collect();
        let upper_set: FxHashSet<SlotRef> = collect_upperbound_overincluded_slots(origins, slots)
            .into_iter()
            .collect();
        assert!(
            raw_set.is_subset(&full_set)
                && mit_set.is_subset(&full_set)
                && upper_set.is_subset(&full_set),
            "NB4-4c-Q: an over-inclusion set ⊄ FULL demotion set (mapping drift)"
        );
        assert!(
            mit_set.is_subset(&upper_set),
            "NB4-4c-Q: mitigated ⊄ upper (invariant)"
        );
        let (n_raw, n_mit, n_upper) = (raw_set.len(), mit_set.len(), upper_set.len());
        let build = |status, nf: Option<usize>, nd0, cm, cdm, cu, cdu| CollateralMeasurement {
            status,
            overincl_raw: n_raw,
            overincl_mit: n_mit,
            overincl_upper: n_upper,
            nref_full: nf,
            nref_d0_full: nd0,
            collateral_mit: cm,
            collateral_d0_mit: cdm,
            collateral_upper: cu,
            collateral_d0_upper: cdu,
        };
        // Short-circuit: no over-inclusion ⇒ MINUS == FULL for both variants ⇒ collateral 0, no solves.
        if upper_set.is_empty() {
            return build("no-oi", None, None, 0, 0, 0, 0);
        }
        // Real FULL solve — for the like-with-like delta AND the anchor (both solves are REAL, so the
        // collateral is not confounded by an impl difference; F2b anchors real FULL to run_bo's model).
        let Some(full_model) =
            solve_with_demotion(program, slots, origins.native_flows(), &full_vec, mut_facts)
        else {
            return build("real-decline", None, None, 0, 0, 0, 0);
        };
        let (nref_full, nref_d0_full) = count_refs(&full_model, slots);
        let minus = |exclude: &FxHashSet<SlotRef>| -> Option<(usize, usize)> {
            let v: Vec<SlotRef> = full_vec
                .iter()
                .copied()
                .filter(|s| !exclude.contains(s))
                .collect();
            solve_with_demotion(program, slots, origins.native_flows(), &v, mut_facts)
                .map(|m| count_refs(&m, slots))
        };
        let Some((nref_mu, nref_d0_mu)) = minus(&upper_set) else {
            return build(
                "real-decline",
                Some(nref_full),
                Some(nref_d0_full),
                0,
                0,
                0,
                0,
            );
        };
        // MINUS_mit: reuse FULL if `mit` empty, reuse `upper`'s solve if the sets are equal, else solve.
        let (nref_mm, nref_d0_mm) = if mit_set.is_empty() {
            (nref_full, nref_d0_full)
        } else if mit_set == upper_set {
            (nref_mu, nref_d0_mu)
        } else {
            match minus(&mit_set) {
                Some(x) => x,
                None => {
                    return build(
                        "real-decline",
                        Some(nref_full),
                        Some(nref_d0_full),
                        0,
                        0,
                        0,
                        0,
                    );
                }
            }
        };
        build(
            "ok",
            Some(nref_full),
            Some(nref_d0_full),
            nref_mm as i64 - nref_full as i64,
            nref_d0_mm as i64 - nref_d0_full as i64,
            nref_mu as i64 - nref_full as i64,
            nref_d0_mu as i64 - nref_d0_full as i64,
        )
    }

    /// §NB5-L2 commit-necessity probe verdict for one leave-one-out.
    pub(crate) enum ProbeOutcome {
        /// The re-solve without this commit ACCEPTS with `slot_i` still `Ref` — the commit was
        /// removable (given the other demotions asserted on the base).
        OverPin,
        /// The re-solve declined, or left `slot_i` non-`Ref`, or failed to accept — counted necessary.
        Necessary,
    }

    /// §NB5-L2 — build `run_bo`'s EXACT solver base ONCE: `emit_crate_ownership_constraints(origins)`
    /// with the REAL seed (NOT `solve_with_demotion`'s `&empty`) → `add_coherence` per fn →
    /// `constrain_field_ownership` (the field constraints the loop adds before its first solve). The
    /// audit reuses this base across every probe via `push_scope`/`pop_scope`, so brotli's ~683-commit
    /// exhaustive leave-one-out pays the emit cost once, not per probe. `None` on emit error.
    fn build_probe_base(
        program: &crate::utils::rustc::RustProgram,
        slots: &CrateSlots,
        origins: &crate::analyses::borrow_ownership::origin_summary::OriginSummaries,
    ) -> Option<(KindSolver, Selectors)> {
        // Allow-list: this is outside the armed region, so it records nothing.
        {
            let crate_ctxt = CrateCtxt::new(program);
            let solver = KindSolver::new(slots);
            let (_stats, selectors) =
                emit_crate_ownership_constraints(&crate_ctxt, slots, origins, &solver).ok()?;
            for &g in &program.functions {
                let body = program
                    .tcx
                    .mir_drops_elaborated_and_const_checked(g)
                    .borrow();
                add_coherence(&solver, slots, g, &body);
            }
            constrain_field_ownership(&solver, slots, program);
            Some((solver, selectors))
        }
    }

    /// §NB5-L2 — the leave-one-out primitive on a PREBUILT base (the ratified Q2 MECHANISM: ONE solve +
    /// ONE validate, NOT a CEGAR re-run). Pushes a scope, asserts `¬ref(d)` for every `d ∈ demote`,
    /// solves ONCE, validates ONCE, then pops — so the base is untouched for the next probe. Returns
    /// true iff the model ACCEPTS (`model_accepts`) AND leaves `target` `Ref` (dropping `target`'s
    /// commit still accepts with `target` a borrow).
    ///
    /// Rider 4 (push/pop determinism): reusing the incremental solver may tie-break OTHER slots
    /// differently than a fresh `KindSolver` would, and `model_kinds_relaxing` may relax selectors
    /// differently than the anchor fixpoint did. Neither matters: this is a CLASSIFICATION only
    /// (accept ∧ `target`==`Ref`), never a model comparison — so do NOT "fix" it to fresh solves for a
    /// parity that is irrelevant here.
    fn probe_accepts_with_ref(
        program: &crate::utils::rustc::RustProgram,
        slots: &CrateSlots,
        origin_flows: &crate::analyses::borrow_ownership::origin_flow::OriginFlowResults,
        base: &KindSolver,
        selectors: &Selectors,
        is_mutable: impl MutProvider + Copy,
        demote: &[SlotRef],
        target: SlotRef,
    ) -> bool {
        base.push_scope();
        for &d in demote {
            base.add_borrow_exclusion(Some(d), &[]);
        }
        // Allow-list: outside the armed region ⇒ records nothing.
        let verdict = match base.model_kinds_relaxing(selectors) {
            Some(model) => {
                model.get(&target) == Some(&SlotKind::Ref)
                    && model_accepts_with_flows(program, slots, origin_flows, &model, is_mutable)
            }
            // UNSAT even without `target` ⇒ `target` is not the reason it declines; NOT removable.
            None => false,
        };
        base.pop_scope();
        verdict
    }

    /// §NB5-L2 — single-shot leave-one-out (build base + one probe). The audit driver builds the base
    /// once and calls `probe_accepts_with_ref` directly; this wrapper keeps the calibration-test API
    /// (`commit_set`, `i`) rebuilding the base per call, which is fine at test scale. `commit_set[i]` is
    /// an OVER-PIN iff a solve over `commit_set \ {commit_set[i]}` accepts with `slot_i` `Ref`.
    pub(crate) fn necessity_probe(
        program: &crate::utils::rustc::RustProgram,
        slots: &CrateSlots,
        origins: &crate::analyses::borrow_ownership::origin_summary::OriginSummaries,
        is_mutable: impl MutProvider + Copy,
        commit_set: &[SlotRef],
        i: usize,
    ) -> ProbeOutcome {
        let Some((base, selectors)) = build_probe_base(program, slots, origins) else {
            return ProbeOutcome::Necessary;
        };
        let demote: Vec<SlotRef> = commit_set
            .iter()
            .enumerate()
            .filter_map(|(j, &c)| (j != i).then_some(c))
            .collect();
        if probe_accepts_with_ref(
            program,
            slots,
            origins.native_flows(),
            &base,
            &selectors,
            is_mutable,
            &demote,
            commit_set[i],
        ) {
            ProbeOutcome::OverPin
        } else {
            ProbeOutcome::Necessary
        }
    }

    /// §NB5-L2 — format a slot for the over-pin inventory: `def_path::_local@dN` (locals) /
    /// `def_path::fieldK@dN` (struct fields). The L2 RED inventory reads these back.
    pub(super) fn fmt_slot(
        program: &crate::utils::rustc::RustProgram,
        slots: &CrateSlots,
        s: SlotRef,
    ) -> String {
        match s {
            SlotRef::Local(fn_did, sid) => {
                let sl = slots.fn_local_slots.get(&fn_did).map(|u| *u.slot(sid));
                let (local, depth) = match sl.map(|s| (s.owner, s.depth)) {
                    Some((SlotOwner::Local(l), d)) => (l.as_u32(), d),
                    other => (u32::MAX, other.map_or(0, |(_, d)| d)),
                };
                format!(
                    "{}::_{}@d{}",
                    program.tcx.def_path_str(fn_did.to_def_id()),
                    local,
                    depth
                )
            }
            SlotRef::Field(sid) => {
                let sl = slots.field_slots.slot(sid);
                match sl.owner {
                    SlotOwner::Field(f) => format!(
                        "{}::field{}@d{}",
                        program.tcx.def_path_str(f.struct_did.to_def_id()),
                        f.field_index,
                        sl.depth
                    ),
                    SlotOwner::Local(_) => format!("field?@d{}", sl.depth),
                }
            }
        }
    }

    fn record_l2_red_inventory(
        program: &crate::utils::rustc::RustProgram,
        slots: &CrateSlots,
        model: &FxHashMap<SlotRef, SlotKind>,
        repair: RepairMode,
        n_ref: usize,
        row: &mut Row,
    ) {
        if !super::l2_red_gate::enabled() {
            return;
        }
        assert!(
            crate::analyses::borrow_ownership::l2::enabled_from_env(),
            "L2 RED gate requires CRAT_BO_L2_GUARDED_COMMITS=1"
        );
        assert_eq!(repair, RepairMode::ModeA, "L2 RED gate is Mode-A-only");
        let diagnostics = std::env::var("CRAT_POINTER_DECISION_DIAGNOSTICS")
            .expect("L2 RED gate requires decision diagnostics");
        assert_eq!(
            diagnostics, "raw",
            "L2 RED gate requires CRAT_POINTER_DECISION_DIAGNOSTICS=raw"
        );
        assert_eq!(
            crate::rewriter::diagnostics::DiagnosticsMode::from_env_value(Some(&diagnostics)),
            crate::rewriter::diagnostics::DiagnosticsMode::Raw,
        );

        let program_name =
            std::env::var("CRAT_BOC1_NAME").expect("L2 RED worker requires CRAT_BOC1_NAME");
        let expected = super::l2_red_gate::targets_for(&program_name);
        let mut model_by_name = FxHashMap::default();
        for (&slot, &kind) in model {
            let name = fmt_slot(program, slots, slot);
            assert!(
                model_by_name.insert(name.clone(), (slot, kind)).is_none(),
                "L2 RED model has duplicate canonical slot {name}"
            );
        }

        let mut found = 0usize;
        let mut recovered = 0usize;
        for target in &expected {
            let Some((slot, kind)) = model_by_name.get(&target.slot).copied() else {
                continue;
            };
            found += 1;
            recovered += usize::from(kind == SlotKind::Ref);
            let kind = match kind {
                SlotKind::Ref => "ref",
                SlotKind::Raw => "raw",
                SlotKind::Owning => "owning",
            };
            eprintln!(
                "L2TARGET program={} slot={} slot_key={} audit_round={} kind={kind}",
                target.program,
                target.slot,
                crate::analyses::borrow_ownership::l2::slotref_diagnostic(slot),
                target.audit_round
            );
        }

        let base = super::l2_red_gate::base_for(&program_name);
        row.set("l2_feature", "on");
        row.set("l2_diag", "raw");
        row.set("l2_targets_expected", expected.len());
        row.set("l2_targets_found", found);
        row.set("l2_targets_ref", recovered);
        row.set("l2_base_n_ref", base.n_ref);
        row.set("l2_n_ref_delta", n_ref as i64 - base.n_ref as i64);
    }

    /// §NB5-L2 commit-necessity audit driver — measure the L2 headroom Mode-A leaves (env-gated by
    /// `CRAT_BOC1_NECESSITY_AUDIT`; called from `run_bo`). FULL-ANCHOR first: the audit's baseline IS
    /// `run_bo`'s own accepted `model`, so only measure if it accepted, assert it satisfies
    /// `model_accepts` (anti-drift), and record `na_anchor_nref[_d0]` for the post-run cross-check
    /// against the merged NB5-L `mode_a` sweep row.
    ///
    /// Then TWO leave-one-out passes over the distinct commit set `C`, both EXHAUSTIVE (no sampling —
    /// the base is emitted once and every probe reuses it via `push_scope`/`pop_scope`, so even brotli's
    /// full `C` is affordable):
    /// - **Independent** (`na_indep_overpins`): each `ci` tested against the full `C\{ci}`. NOT a bound
    ///   and INCOMPARABLE with the gate number — it OVER-counts alternative-repair pairs (both reported
    ///   though only one Ref is jointly recoverable, Codex F1) AND UNDER-counts joint recoveries (a slot
    ///   removable only while other removed slots stay `Ref` is missed, since independent demotes them
    ///   all — e.g. coherence-equated slots; this is why `na_overpins` can EXCEED `na_indep_overpins`,
    ///   as on libtree 3 → 7). A labeled diagnostic for continuity with the pre-redesign partial; do
    ///   NOT gate on it and do NOT assume any ≤/≥ relation to `na_overpins`.
    /// - **Witnessed-joint greedy** (`na_overpins` — THE gate number): in ROUND ORDER (rider 3), retain
    ///   all commits and test removing each given the CURRENT retained set (already-removed commits left
    ///   un-demoted, so removability is tested GIVEN the recovered set); a success is made PERMANENT. The
    ///   removed set is certified JOINTLY recoverable by a final witness solve (`na_joint_witnessed`:
    ///   demote ONLY the final retained set → every removed slot `Ref` + accept) — a TRUE lower bound on
    ///   recoverable Refs, sound regardless of any push/pop tie-breaking (the witness is the certificate).
    ///   CAVEAT (rider 2): still blind to joint-ONLY pins (neither member individually removable given
    ///   the retained set — greedy never enters), so "close the line" still carries "joint-only headroom
    ///   unmeasured". Order-dependent: A witnessed lower bound, not THE maximum removable set; round order
    ///   is the diagnostic choice (late-round commits sit on more accumulation — the round DISTRIBUTION
    ///   of the removed set is a first-class output).
    ///
    /// Emits per-program counts + the `NAOVERPIN` slot inventory for the witnessed-joint set (rider 4:
    /// runs under the seed-pinned worker env; the push/pop reuse is classification-only).
    pub(crate) fn run_necessity_audit(
        program: &crate::utils::rustc::RustProgram,
        slots: &CrateSlots,
        origins: &crate::analyses::borrow_ownership::origin_summary::OriginSummaries,
        is_mutable: impl MutProvider + Copy,
        model: &Option<FxHashMap<SlotRef, SlotKind>>,
        events: &[(SlotRef, usize)],
        row: &mut Row,
    ) {
        // FULL-ANCHOR: no anchor model ⇒ nothing to measure; surface it, never a silent skip.
        let Some(model) = model else {
            row.set("na_status", "anchor-declined");
            return;
        };
        assert!(
            model_accepts_with_flows(program, slots, origins.native_flows(), model, is_mutable,),
            "necessity audit: the anchor's accepted model must satisfy model_accepts (drift STOP)"
        );
        let (anchor_nref, anchor_nref_d0) = count_refs(model, slots);
        row.set("na_anchor_nref", anchor_nref);
        row.set("na_anchor_nref_d0", anchor_nref_d0);
        // Distinct commit set C (dedup by slot, keep the FIRST round each slot was committed), then
        // ROUND ORDER (round, slotref_key) — the greedy processing order (rider 3), deterministic.
        let mut seen = FxHashSet::default();
        let mut commit_set: Vec<(SlotRef, usize)> = Vec::new();
        for &(s, r) in events {
            if seen.insert(s) {
                commit_set.push((s, r));
            }
        }
        commit_set.sort_by(|a, b| (a.1, slotref_key(&a.0)).cmp(&(b.1, slotref_key(&b.0))));
        let n = commit_set.len();
        row.set("na_commits_total", n);
        if n == 0 {
            row.set("na_status", "no-commits");
            row.set("na_indep_overpins", 0);
            row.set("na_overpins", 0);
            return;
        }
        // Emit the probe base ONCE; every probe reuses it via push/pop (rider 4 / cost).
        let Some((base, selectors)) = build_probe_base(program, slots, origins) else {
            row.set("na_status", "base-error");
            return;
        };
        let slots_only: Vec<SlotRef> = commit_set.iter().map(|(s, _)| *s).collect();
        let program_name =
            std::env::var("CRAT_BOC1_NAME").unwrap_or_else(|_| "unnamed".to_string());

        // --- Independent pass (over-count diagnostic; each ci vs the FULL C\{ci}). It is exactly `n`
        // extra solves on top of the greedy pass, so for the largest programs it is the difference
        // between feasible and not. `CRAT_BOC1_NA_GREEDY_ONLY` skips it (the GATE metric is the greedy
        // witnessed-joint below; independent is only a labeled diagnostic — rider 5's "continuity" is
        // about the small/mid programs, which keep both passes). Emits `na_indep_overpins=skipped`. ---
        if std::env::var_os("CRAT_BOC1_NA_GREEDY_ONLY").is_some() {
            row.set("na_indep_overpins", "skipped");
        } else {
            let mut indep_overpins = 0usize;
            for i in 0..n {
                let demote: Vec<SlotRef> =
                    (0..n).filter(|&j| j != i).map(|j| slots_only[j]).collect();
                if probe_accepts_with_ref(
                    program,
                    slots,
                    origins.native_flows(),
                    &base,
                    &selectors,
                    is_mutable,
                    &demote,
                    slots_only[i],
                ) {
                    indep_overpins += 1;
                }
            }
            row.set("na_indep_overpins", indep_overpins);
        }

        // --- Witnessed-joint greedy (THE gate number), round order. Buffer the removed set; the
        // NAOVERPIN inventory + na_overpins publish ONLY after the joint witness certifies it (F1). ---
        let mut retained = vec![true; n];
        let mut removed: Vec<(SlotRef, usize)> = Vec::new();
        for i in 0..n {
            // Demote every STILL-retained commit except the candidate; the already-removed commits are
            // left un-demoted (Ref-eligible), so removability is tested GIVEN the recovered set.
            let demote: Vec<SlotRef> = (0..n)
                .filter(|&j| j != i && retained[j])
                .map(|j| slots_only[j])
                .collect();
            if probe_accepts_with_ref(
                program,
                slots,
                origins.native_flows(),
                &base,
                &selectors,
                is_mutable,
                &demote,
                slots_only[i],
            ) {
                retained[i] = false;
                removed.push(commit_set[i]);
            }
        }

        // F1 (Codex): certify the JOINT property FAIL-CLOSED before publishing anything. HARD-PIN every
        // removed slot `Ref` (not a passive optimum inspection — tie-breaking could otherwise miss a
        // valid witness), demote ONLY the final retained set, and require an ACCEPTING model. On success
        // the removed set is provably jointly recoverable → publish the gate number + inventory + `ok`.
        // On failure (a sequential-removal hole, or the pins are UNSAT) the gate metric is SUPPRESSED and
        // the status is `witness-failed` — a never-silent, never-trusted uncertified count.
        let final_demote: Vec<SlotRef> = (0..n)
            .filter(|&j| retained[j])
            .map(|j| slots_only[j])
            .collect();
        base.push_scope();
        for &(s, _) in &removed {
            base.assume(s, SlotKind::Ref);
        }
        for &d in &final_demote {
            base.add_borrow_exclusion(Some(d), &[]);
        }
        // Allow-list: outside the armed region ⇒ records nothing.
        let witnessed = match base.model_kinds_relaxing(&selectors) {
            // Removed slots are hard-pinned `Ref`, so a SAT model has them all `Ref` by construction;
            // only acceptance remains to check.
            Some(m) => {
                model_accepts_with_flows(program, slots, origins.native_flows(), &m, is_mutable)
            }
            // UNSAT under the pins ⇒ the removed set is NOT jointly `Ref`-recoverable (unless empty).
            None => removed.is_empty(),
        };
        base.pop_scope();
        row.set("na_joint_witnessed", witnessed);

        if !witnessed {
            // Fail-closed: suppress the gate metric; do NOT emit `na_overpins` or the inventory.
            row.set("na_status", "witness-failed");
            return;
        }

        // Certified. Publish the gate number, the RED inventory, and the round distribution.
        row.set("na_overpins", removed.len());
        for &(s, r) in &removed {
            // Grep-able RED inventory (the `NBRCORE` pattern): one line per CERTIFIED over-pin.
            eprintln!(
                "NAOVERPIN {program_name} {} round={r}",
                fmt_slot(program, slots, s)
            );
        }
        let mut by_round: FxHashMap<usize, usize> = FxHashMap::default();
        for &(_, r) in &removed {
            *by_round.entry(r).or_default() += 1;
        }
        let mut rounds: Vec<(usize, usize)> = by_round.into_iter().collect();
        rounds.sort();
        row.set(
            "na_overpins_by_round",
            rounds
                .iter()
                .map(|(r, c)| format!("{r}:{c}"))
                .collect::<Vec<_>>()
                .join("/"),
        );
        row.set("na_status", "ok");
    }

    /// D2 witness-only replay of the audit's final certification step.
    ///
    /// The certified inventory supplies the already-reviewed `removed` set, so
    /// this skips both leave-one-out passes: hard-pin those slots `Ref`, demote
    /// every other captured Mode-A commit, invoke the existing relaxing solver
    /// once, and validate the resulting model with the audit's exact
    /// `model_accepts` predicate.
    fn run_certified_context(
        program: &crate::utils::rustc::RustProgram,
        slots: &CrateSlots,
        origins: &crate::analyses::borrow_ownership::origin_summary::OriginSummaries,
        is_mutable: impl MutProvider + Copy,
        events: &[(SlotRef, usize)],
        row: &mut Row,
    ) {
        assert!(
            !crate::analyses::borrow_ownership::l2::enabled_from_env(),
            "certified-context replay must capture the Mode-A feature-off commit set"
        );
        assert!(
            l2::diagnostics_enabled_from_env(),
            "certified-context replay requires CRAT_POINTER_DECISION_DIAGNOSTICS"
        );

        let program_name = std::env::var("CRAT_BOC1_NAME")
            .expect("certified-context worker requires program name");
        let expected = super::l2_red_gate::targets_for(&program_name);
        assert!(
            !expected.is_empty(),
            "certified-context replay has no certified targets for {program_name}"
        );
        let expected_names: FxHashSet<String> =
            expected.iter().map(|target| target.slot.clone()).collect();

        let mut seen = FxHashSet::default();
        let mut commit_set = events
            .iter()
            .copied()
            .filter(|(slot, _)| seen.insert(*slot))
            .collect::<Vec<_>>();
        commit_set.sort_by(|a, b| (a.1, slotref_key(&a.0)).cmp(&(b.1, slotref_key(&b.0))));

        let mut removed = Vec::new();
        let mut retained = Vec::new();
        let mut found_names = FxHashSet::default();
        for &(slot, _) in &commit_set {
            let name = fmt_slot(program, slots, slot);
            if expected_names.contains(&name) {
                assert!(
                    found_names.insert(name),
                    "duplicate certified-context target in Mode-A commit set"
                );
                removed.push(slot);
            } else {
                retained.push(slot);
            }
        }
        assert_eq!(
            found_names, expected_names,
            "certified-context targets do not match the captured Mode-A commit set"
        );

        let (base, selectors) =
            build_probe_base(program, slots, origins).expect("certified-context probe base");
        base.push_scope();
        for &slot in &removed {
            base.assume(slot, SlotKind::Ref);
        }
        for &slot in &retained {
            base.add_borrow_exclusion(Some(slot), &[]);
        }
        let before_checks = base.check_sat_count();
        let witness = base.model_kinds_relaxing(&selectors);
        let witness_checks = base.check_sat_count() - before_checks;
        base.pop_scope();

        let witness = witness.expect("certified-context hard-pinned witness must be SAT");
        assert!(
            removed
                .iter()
                .all(|slot| witness.get(slot) == Some(&SlotKind::Ref)),
            "certified-context witness violated a hard Ref pin"
        );
        assert!(
            model_accepts_with_flows(program, slots, origins.native_flows(), &witness, is_mutable,),
            "certified-context hard-pinned witness must pass audit acceptance"
        );

        let mut witness_slots = witness.keys().copied().collect::<Vec<_>>();
        witness_slots.sort_by_key(slotref_key);
        for slot in witness_slots {
            let kind = match witness[&slot] {
                SlotKind::Ref => "ref",
                SlotKind::Raw => "raw",
                SlotKind::Owning => "owning",
            };
            eprintln!(
                "[bo-l2] event=l2_certified_kind|program={program_name}|slot={}|slot_key={}|kind={kind}",
                fmt_slot(program, slots, slot),
                l2::slotref_diagnostic(slot),
            );
        }
        row.set("l2_certified_context", "ok");
        row.set("l2_certified_targets", removed.len());
        row.set("l2_certified_demoted", retained.len());
        row.set("l2_certified_solve_calls", 1);
        row.set("l2_certified_check_sat", witness_checks);
    }

    fn tracked_label(
        literal: &Bool,
        tracker: &CoreTracker,
        selectors: &Selectors,
        program_name: &str,
    ) -> String {
        if let Some(label) = tracker.label_of(literal) {
            return label;
        }
        let index = selectors.index_of(literal).unwrap_or_else(|| {
            panic!("tracked core contains an unrecognized assumption: {literal}")
        });
        let class = if index < selectors.sources().len() {
            SelectorClass::Source
        } else {
            SelectorClass::Sink
        };
        format!(
            "{}({})",
            match class {
                SelectorClass::Source => "source-selector",
                SelectorClass::Sink => "sink-selector",
            },
            selector_leak_diagnosis::selector_key(
                program_name,
                class,
                index,
                selectors.sources().len(),
            )
        )
    }

    fn tracked_labels(
        core: &[Bool],
        tracker: &CoreTracker,
        selectors: &Selectors,
        program_name: &str,
    ) -> Vec<String> {
        core.iter()
            .map(|literal| tracked_label(literal, tracker, selectors, program_name))
            .collect()
    }

    fn family_marker_labels(core: &[Bool], tracker: &CoreTracker) -> Vec<String> {
        let mut labels = core
            .iter()
            .filter_map(|literal| tracker.label_of(literal))
            .collect::<Vec<_>>();
        labels.sort();
        labels.dedup();
        labels
    }

    fn hard_families(labels: &[String]) -> BTreeSet<String> {
        labels
            .iter()
            .filter_map(|label| super::explain::family_of(label))
            .filter(|family| !matches!(*family, "source-selector" | "sink-selector"))
            .map(str::to_string)
            .collect()
    }

    fn commit_events_for_reporting(
        tcx: TyCtxt<'_>,
        program: &crate::utils::rustc::RustProgram,
        trace: &selector_leak_diagnosis::OfficialTrace,
    ) -> Vec<CommitEvent> {
        trace
            .commits
            .iter()
            .map(|commit| CommitEvent {
                round: commit.round,
                target: selector_leak_diagnosis::portable_slot_key(
                    tcx,
                    &program.functions,
                    commit.target,
                ),
                issuer: commit.issuer.map(|slot| {
                    selector_leak_diagnosis::portable_slot_key(tcx, &program.functions, slot)
                }),
                requirers: commit
                    .requirers
                    .iter()
                    .map(|slot| {
                        selector_leak_diagnosis::portable_slot_key(tcx, &program.functions, *slot)
                    })
                    .collect(),
            })
            .collect()
    }

    fn replay_commit_round(
        tcx: TyCtxt<'_>,
        program: &crate::utils::rustc::RustProgram,
        official: &selector_leak_diagnosis::OfficialTrace,
        solver: &KindSolver,
        tracker: Option<&CoreTracker>,
        round: usize,
    ) {
        for commit in official
            .commits
            .iter()
            .filter(|commit| commit.round == round)
        {
            let target_key =
                selector_leak_diagnosis::portable_slot_key(tcx, &program.functions, commit.target);
            if let Some(tracker) = tracker {
                tracker.set_context(&format!("borrow-round-{round}-target={target_key}"));
            }
            solver.add_borrow_exclusion(
                Some(selector_leak_diagnosis::restore_slot(
                    &program.functions,
                    commit.target,
                )),
                &[],
            );
        }
    }

    /// Tracked diagnostic worker. The official trace fixes every active
    /// selector set and Mode-A commit boundary; this worker only extracts the
    /// corresponding hard core.
    pub fn run_selector_core(tcx: TyCtxt<'_>, t_tcx: Duration) -> Row {
        let t0 = Instant::now();
        let mut row = Row::default();
        row.set("t_tcx_s", secs(t_tcx));
        row.set("z3_full_version", z3::full_version().to_string());

        let program_name =
            std::env::var("CRAT_BOC1_NAME").expect("selector-core worker requires program name");
        let trace_path = std::env::var("CRAT_BOC1_SELECTOR_TRACE")
            .expect("selector-core worker requires CRAT_BOC1_SELECTOR_TRACE");
        let evidence_path = std::env::var("CRAT_BOC1_SELECTOR_EVIDENCE")
            .expect("selector-core worker requires CRAT_BOC1_SELECTOR_EVIDENCE");
        let official = selector_leak_diagnosis::read_official_trace(Path::new(&trace_path))
            .unwrap_or_else(|error| panic!("{error}"));
        assert_eq!(official.program, program_name);
        assert_eq!(
            official.code_sha,
            super::orchestrate::git_sha(),
            "selector trace/code SHA mismatch"
        );

        let program = collect_program(tcx);
        let origins = compute_origins(&program);
        let slots = CrateSlots::build(&program);
        let crate_ctxt = CrateCtxt::new(&program);
        let solver = KindSolver::new_family_tracked(&slots);
        let (_stats, selectors) =
            emit_crate_ownership_constraints(&crate_ctxt, &slots, &origins, &solver)
                .expect("tracked selector-core emission");
        let tracker = solver.tracker().expect("tracked solver");
        tracker.set_context("coherence");
        for &function in &program.functions {
            let body = tcx
                .mir_drops_elaborated_and_const_checked(function)
                .borrow();
            add_coherence(&solver, &slots, function, &body);
        }
        tracker.set_context("field-law");
        constrain_field_ownership(&solver, &slots, &program);

        assert_eq!(selectors.sources().len(), official.n_sources);
        assert_eq!(selectors.all().len(), official.total_selectors);
        let mut evidence = Vec::new();

        for (epoch_index, epoch) in official.epochs.iter().enumerate() {
            assert!(
                epoch.events.iter().all(|event| event.epoch == epoch_index),
                "official selector event epoch drift"
            );
            replay_commit_round(
                tcx,
                &program,
                &official,
                &solver,
                Some(tracker),
                epoch_index,
            );

            let reenable_outcomes = epoch
                .events
                .iter()
                .filter(|event| event.phase == TracePhase::Reenable)
                .map(|event| (event.selector_index, event.outcome))
                .collect::<FxHashMap<_, _>>();
            for event in epoch
                .events
                .iter()
                .filter(|event| event.phase == TracePhase::Drop)
            {
                let mut assumptions = tracker.tracks();
                assumptions.extend(event.active_before.iter().map(|index| {
                    selectors
                        .all()
                        .get(*index)
                        .unwrap_or_else(|| panic!("selector index {index} out of range"))
                        .clone()
                }));
                let actual = solver.optimize().check(&assumptions);
                assert_eq!(
                    actual,
                    SatResult::Unsat,
                    "tracked reconstruction diverged at {program_name} epoch {epoch_index} \
                     selector {} {:?}",
                    event.selector_index,
                    event.phase
                );

                let raw_core = solver.optimize().get_unsat_core();
                let raw_labels = family_marker_labels(&raw_core, tracker);
                let raw_families = selector_leak_diagnosis::validate_families(
                    raw_labels.iter().map(String::as_str),
                    CORE_LABEL_FAMILIES,
                )
                .unwrap_or_else(|error| panic!("{error}"));
                let outcome = *reenable_outcomes
                    .get(&event.selector_index)
                    .unwrap_or_else(|| {
                        panic!(
                            "official trace lacks re-enable outcome for selector {}",
                            event.selector_index
                        )
                    });
                evidence.push(CoreEvidence {
                    program: program_name.clone(),
                    selector_key: selector_leak_diagnosis::selector_key(
                        &program_name,
                        event.class,
                        event.selector_index,
                        official.n_sources,
                    ),
                    selector_index: event.selector_index,
                    class: event.class,
                    epoch: epoch_index,
                    phase: event.phase,
                    outcome,
                    active_before: event.active_before.clone(),
                    official_selector_core: event.core_selectors.clone(),
                    raw_labels,
                    raw_families,
                    minimized_labels: Vec::new(),
                    minimized_families: BTreeSet::new(),
                    minimized: false,
                    out_param_tag: OutParamTag::Untagged,
                    commit_origins: Vec::new(),
                });
            }

            let dropped = epoch
                .final_dropped
                .iter()
                .copied()
                .collect::<FxHashSet<_>>();
            let mut final_assumptions = tracker.tracks();
            final_assumptions.extend(
                selectors
                    .all()
                    .iter()
                    .enumerate()
                    .filter(|(index, _)| !dropped.contains(index))
                    .map(|(_, selector)| selector.clone()),
            );
            assert_eq!(
                solver.optimize().check(&final_assumptions),
                SatResult::Sat,
                "tracked final retained set must be SAT at epoch {epoch_index}"
            );
        }

        selector_leak_diagnosis::write_core_evidence(Path::new(&evidence_path), &evidence)
            .unwrap_or_else(|error| panic!("{error}"));
        let final_dropped = official
            .epochs
            .last()
            .map(|epoch| epoch.final_dropped.as_slice())
            .unwrap_or_default();
        row.set("selector_core_events", evidence.len());
        row.set(
            "selector_core_sources_final",
            final_dropped
                .iter()
                .filter(|index| **index < official.n_sources)
                .count(),
        );
        row.set(
            "selector_core_sinks_final",
            final_dropped
                .iter()
                .filter(|index| **index >= official.n_sources)
                .count(),
        );
        row.set("check_sat_count", solver.check_sat_count());
        row.set("t_total_s", secs(t0.elapsed()));
        row.set("status", "ok");
        row
    }

    /// Per-assertion diagnostic for one representative drop case selected
    /// after the family matrix exists. Each invocation handles exactly one
    /// `(epoch, selector)` case and is supervised independently.
    pub fn run_selector_core_detail(tcx: TyCtxt<'_>, t_tcx: Duration) -> Row {
        let t0 = Instant::now();
        let mut row = Row::default();
        row.set("t_tcx_s", secs(t_tcx));
        row.set("z3_full_version", z3::full_version().to_string());

        let program_name =
            std::env::var("CRAT_BOC1_NAME").expect("selector detail worker requires program name");
        let trace_path = std::env::var("CRAT_BOC1_SELECTOR_TRACE")
            .expect("selector detail worker requires CRAT_BOC1_SELECTOR_TRACE");
        let detail_path = std::env::var("CRAT_BOC1_SELECTOR_DETAIL_EVIDENCE")
            .expect("selector detail worker requires CRAT_BOC1_SELECTOR_DETAIL_EVIDENCE");
        let case = std::env::var("CRAT_BOC1_SELECTOR_DETAIL_CASE")
            .expect("selector detail worker requires CRAT_BOC1_SELECTOR_DETAIL_CASE");
        let (epoch, selector_index) = case
            .split_once(':')
            .and_then(|(epoch, selector)| {
                Some((
                    epoch.parse::<usize>().ok()?,
                    selector.parse::<usize>().ok()?,
                ))
            })
            .unwrap_or_else(|| panic!("selector detail case must be EPOCH:SELECTOR, got {case:?}"));
        let official = selector_leak_diagnosis::read_official_trace(Path::new(&trace_path))
            .unwrap_or_else(|error| panic!("{error}"));
        assert_eq!(official.program, program_name);
        assert_eq!(
            official.code_sha,
            super::orchestrate::git_sha(),
            "selector trace/code SHA mismatch"
        );

        let program = collect_program(tcx);
        let origins = compute_origins(&program);
        let slots = CrateSlots::build(&program);
        let crate_ctxt = CrateCtxt::new(&program);
        let solver = KindSolver::new_tracked(&slots);
        let (_stats, selectors) =
            emit_crate_ownership_constraints(&crate_ctxt, &slots, &origins, &solver)
                .expect("per-assertion selector detail emission");
        let tracker = solver.tracker().expect("tracked solver");
        tracker.set_context("coherence");
        for &function in &program.functions {
            let body = tcx
                .mir_drops_elaborated_and_const_checked(function)
                .borrow();
            add_coherence(&solver, &slots, function, &body);
        }
        tracker.set_context("field-law");
        constrain_field_ownership(&solver, &slots, &program);

        assert_eq!(selectors.sources().len(), official.n_sources);
        assert_eq!(selectors.all().len(), official.total_selectors);
        let reporting_commits = commit_events_for_reporting(tcx, &program, &official);
        for round in 0..=epoch {
            replay_commit_round(tcx, &program, &official, &solver, Some(tracker), round);
        }

        let event = official
            .epochs
            .get(epoch)
            .unwrap_or_else(|| panic!("selector detail epoch {epoch} out of range"))
            .events
            .iter()
            .find(|event| event.phase == TracePhase::Drop && event.selector_index == selector_index)
            .unwrap_or_else(|| {
                panic!(
                    "selector detail lacks drop event at epoch {epoch} selector {selector_index}"
                )
            });
        let mut assumptions = tracker.tracks();
        assumptions.extend(event.active_before.iter().map(|index| {
            selectors
                .all()
                .get(*index)
                .unwrap_or_else(|| panic!("selector index {index} out of range"))
                .clone()
        }));
        assert_eq!(
            solver.optimize().check(&assumptions),
            SatResult::Unsat,
            "per-assertion representative case must reconstruct UNSAT"
        );
        let raw_core = solver.optimize().get_unsat_core();
        let raw_labels = tracked_labels(&raw_core, tracker, &selectors, &program_name);
        let raw_families = hard_families(&raw_labels);
        let (minimal_core, minimized) = super::explain::minimize_core(&solver, raw_core);
        let minimized_labels = tracked_labels(&minimal_core, tracker, &selectors, &program_name);
        let minimized_families = hard_families(&minimized_labels);
        let commit_origins = reporting_commits
            .iter()
            .filter(|commit| {
                raw_labels.iter().any(|label| {
                    label.contains("borrow-exclusion") && label.contains(&commit.target)
                })
            })
            .map(|commit| {
                format!(
                    "round={} target={} issuer={} requirers={}",
                    commit.round,
                    commit.target,
                    commit.issuer.as_deref().unwrap_or("-"),
                    commit.requirers.join("+")
                )
            })
            .collect::<Vec<_>>();
        let evidence = DetailEvidence {
            program: program_name.clone(),
            selector_key: selector_leak_diagnosis::selector_key(
                &program_name,
                event.class,
                selector_index,
                official.n_sources,
            ),
            selector_index,
            epoch,
            raw_labels,
            raw_families,
            minimized_labels,
            minimized_families,
            minimized,
            commit_origins,
        };
        selector_leak_diagnosis::write_detail_evidence(Path::new(&detail_path), &evidence)
            .unwrap_or_else(|error| panic!("{error}"));
        row.set("selector_detail_epoch", epoch);
        row.set("selector_detail_index", selector_index);
        row.set("selector_detail_minimized", minimized);
        row.set("t_total_s", secs(t0.elapsed()));
        row.set("status", "ok");
        row
    }

    /// Untracked removal-based necessity worker. The accepted family-core
    /// matrix limits probes to families present in a preserved UNSAT core;
    /// absent families are recorded non-necessary without a solve.
    pub fn run_selector_necessity(tcx: TyCtxt<'_>, t_tcx: Duration) -> Row {
        let t0 = Instant::now();
        let mut row = Row::default();
        row.set("t_tcx_s", secs(t_tcx));
        row.set("z3_full_version", z3::full_version().to_string());

        let program_name =
            std::env::var("CRAT_BOC1_NAME").expect("necessity worker requires program name");
        let trace_path = std::env::var("CRAT_BOC1_SELECTOR_TRACE")
            .expect("necessity worker requires CRAT_BOC1_SELECTOR_TRACE");
        let matrix_path = std::env::var("CRAT_BOC1_SELECTOR_FAMILY_MATRIX")
            .expect("necessity worker requires CRAT_BOC1_SELECTOR_FAMILY_MATRIX");
        let evidence_path = std::env::var("CRAT_BOC1_NECESSITY_EVIDENCE")
            .expect("necessity worker requires CRAT_BOC1_NECESSITY_EVIDENCE");
        let official = selector_leak_diagnosis::read_official_trace(Path::new(&trace_path))
            .unwrap_or_else(|error| panic!("{error}"));
        assert_eq!(official.program, program_name);
        assert_eq!(
            official.code_sha,
            super::orchestrate::git_sha(),
            "selector trace/code SHA mismatch"
        );
        let matrix = ownership_diagnostic_package::read_family_matrix(Path::new(&matrix_path))
            .unwrap_or_else(|error| panic!("{error}"));
        let program_prefix = format!("{program_name}/source:");
        let program_matrix = matrix
            .into_iter()
            .filter(|(key, _)| key.starts_with(&program_prefix))
            .collect::<BTreeMap<_, _>>();

        let last_epoch_index = official
            .epochs
            .len()
            .checked_sub(1)
            .expect("official trace must contain a selector epoch");
        let last_epoch = &official.epochs[last_epoch_index];
        let actual_source_keys = last_epoch
            .final_dropped
            .iter()
            .filter(|index| **index < official.n_sources)
            .map(|index| {
                selector_leak_diagnosis::selector_key(
                    &program_name,
                    SelectorClass::Source,
                    *index,
                    official.n_sources,
                )
            })
            .collect::<BTreeSet<_>>();
        let expected_source_keys = program_matrix.keys().cloned().collect::<BTreeSet<_>>();
        assert!(
            ownership_diagnostic_package::replay_matches_official(
                &expected_source_keys
                    .iter()
                    .map(|key| {
                        key.strip_prefix(&program_prefix)
                            .expect("program source key")
                            .parse::<usize>()
                            .expect("source selector index")
                    })
                    .collect::<Vec<_>>(),
                &actual_source_keys
                    .iter()
                    .map(|key| {
                        key.strip_prefix(&program_prefix)
                            .expect("program source key")
                            .parse::<usize>()
                            .expect("source selector index")
                    })
                    .collect::<Vec<_>>(),
            ),
            "official/family-matrix selector-set mismatch for {program_name}: \
             expected={expected_source_keys:?} actual={actual_source_keys:?}"
        );

        let mut drop_events = BTreeMap::new();
        for event in last_epoch
            .events
            .iter()
            .filter(|event| event.phase == TracePhase::Drop)
        {
            let key = selector_leak_diagnosis::selector_key(
                &program_name,
                event.class,
                event.selector_index,
                official.n_sources,
            );
            if program_matrix.contains_key(&key) {
                assert!(
                    drop_events.insert(key, event).is_none(),
                    "duplicate final-epoch drop event"
                );
            }
        }
        assert_eq!(
            drop_events.keys().cloned().collect::<BTreeSet<_>>(),
            expected_source_keys,
            "final leaked source lacks a final-epoch drop event"
        );

        let program = collect_program(tcx);
        let origins = compute_origins(&program);
        let slots = CrateSlots::build(&program);
        let candidate_families = program_matrix
            .values()
            .flat_map(|families| families.iter().cloned())
            .collect::<BTreeSet<_>>();
        for family in &candidate_families {
            assert!(
                CORE_LABEL_FAMILIES.contains(&family.as_str()),
                "unrecognized family in accepted matrix: {family}"
            );
        }

        let probe = |filter: RemovalFilter, keys: &BTreeSet<String>| -> (BTreeSet<String>, usize) {
            ownership_diagnostic_package::with_removal_filter(filter, || {
                let crate_ctxt = CrateCtxt::new(&program);
                let solver = KindSolver::new(&slots);
                let (_stats, selectors) =
                    emit_crate_ownership_constraints(&crate_ctxt, &slots, &origins, &solver)
                        .expect("untracked necessity emission");
                for &function in &program.functions {
                    let body = tcx
                        .mir_drops_elaborated_and_const_checked(function)
                        .borrow();
                    add_coherence(&solver, &slots, function, &body);
                }
                constrain_field_ownership(&solver, &slots, &program);
                assert_eq!(selectors.sources().len(), official.n_sources);
                assert_eq!(selectors.all().len(), official.total_selectors);
                let mut necessary = BTreeSet::new();
                for round in 0..=last_epoch_index {
                    replay_commit_round(tcx, &program, &official, &solver, None, round);
                    if round != last_epoch_index {
                        continue;
                    }
                    for key in keys {
                        let event = drop_events
                            .get(key)
                            .unwrap_or_else(|| panic!("missing drop event for {key}"));
                        let assumptions = event
                            .active_before
                            .iter()
                            .map(|index| {
                                selectors
                                    .all()
                                    .get(*index)
                                    .unwrap_or_else(|| {
                                        panic!("selector index {index} out of range")
                                    })
                                    .clone()
                            })
                            .collect::<Vec<_>>();
                        match solver.check_with_assumptions(&assumptions) {
                            SatResult::Sat => {
                                necessary.insert(key.clone());
                            }
                            SatResult::Unsat => {}
                            SatResult::Unknown => {
                                panic!("necessity probe returned unknown for {key}")
                            }
                        }
                    }
                }
                (necessary, solver.check_sat_count())
            })
        };

        let mut necessary_by_key: BTreeMap<String, BTreeSet<String>> = program_matrix
            .keys()
            .cloned()
            .map(|key| (key, BTreeSet::new()))
            .collect();
        let mut check_sat_count = 0usize;
        for family in &candidate_families {
            let keys = program_matrix
                .iter()
                .filter(|(_, families)| families.contains(family))
                .map(|(key, _)| key.clone())
                .collect::<BTreeSet<_>>();
            let family = CORE_LABEL_FAMILIES
                .iter()
                .copied()
                .find(|candidate| *candidate == family.as_str())
                .expect("validated family");
            let (necessary, checks) = probe(RemovalFilter::Family(family), &keys);
            check_sat_count = check_sat_count.saturating_add(checks);
            for key in necessary {
                necessary_by_key
                    .get_mut(&key)
                    .expect("necessity key")
                    .insert(family.to_string());
            }
        }

        let pairwise_enabled = ownership_diagnostic_package::pairwise_enabled();
        let joint_keys = necessary_by_key
            .iter()
            .filter(|(_, families)| families.is_empty())
            .map(|(key, _)| key.clone())
            .collect::<BTreeSet<_>>();
        let mut pair_outcomes_by_key = if pairwise_enabled {
            joint_keys
                .iter()
                .cloned()
                .map(|key| (key, Vec::new()))
                .collect::<BTreeMap<_, _>>()
        } else {
            BTreeMap::new()
        };
        if pairwise_enabled && !joint_keys.is_empty() {
            for pair in ownership_diagnostic_package::pairwise_removal_pairs() {
                // Joint rows have already failed every singleton-family removal,
                // so every SAT pair here is minimal by construction.
                let (sat_keys, checks) = probe(RemovalFilter::FamilyPair(pair), &joint_keys);
                check_sat_count = check_sat_count.saturating_add(checks);
                for key in &joint_keys {
                    pair_outcomes_by_key
                        .get_mut(key)
                        .expect("joint pair-removal row")
                        .push(PairRemovalOutcome::new(pair, sat_keys.contains(key)));
                }
            }
        }

        let own_assume_keys = necessary_by_key
            .iter()
            .filter(|(_, families)| families.contains("own-assume"))
            .map(|(key, _)| key.clone())
            .collect::<BTreeSet<_>>();
        let mut necessary_sites_by_key: BTreeMap<String, BTreeSet<String>> = program_matrix
            .keys()
            .cloned()
            .map(|key| (key, BTreeSet::new()))
            .collect();
        if !own_assume_keys.is_empty() {
            for &site in ownership_diagnostic_package::ASSUME_SITES {
                let (necessary, checks) =
                    probe(RemovalFilter::OwnAssumeSite(site), &own_assume_keys);
                check_sat_count = check_sat_count.saturating_add(checks);
                for key in necessary {
                    necessary_sites_by_key
                        .get_mut(&key)
                        .expect("assume-site key")
                        .insert(site.as_str().to_string());
                }
            }
        }

        let evidence = program_matrix
            .into_iter()
            .map(|(selector_key, raw_families)| {
                let event = drop_events[&selector_key];
                let necessary_families = necessary_by_key
                    .remove(&selector_key)
                    .expect("necessary-family row");
                let family_refs = necessary_families
                    .iter()
                    .map(String::as_str)
                    .collect::<Vec<_>>();
                let causal_bucket = ownership_diagnostic_package::causal_bucket(&family_refs);
                let pair_removal = if pairwise_enabled
                    && causal_bucket
                        == ownership_diagnostic_package::CausalBucket::JointNoSingleFamilyNecessity
                {
                    Some(
                        ownership_diagnostic_package::completed_pair_removal_evidence(
                            pair_outcomes_by_key
                                .remove(&selector_key)
                                .expect("joint pair-removal outcomes"),
                        ),
                    )
                } else {
                    assert!(
                        !pair_outcomes_by_key.contains_key(&selector_key),
                        "singleton-necessary row received pair-removal outcomes"
                    );
                    None
                };
                NecessityEvidence {
                    program: program_name.clone(),
                    selector_key: selector_key.clone(),
                    selector_index: event.selector_index,
                    epoch: last_epoch_index,
                    raw_families,
                    necessary_families,
                    own_assume_necessary_sites: necessary_sites_by_key
                        .remove(&selector_key)
                        .expect("assume-site row"),
                    causal_bucket,
                    pair_removal,
                }
            })
            .collect::<Vec<_>>();
        assert!(
            pair_outcomes_by_key.is_empty(),
            "unconsumed joint pair-removal outcomes"
        );
        ownership_diagnostic_package::write_json(Path::new(&evidence_path), &evidence)
            .unwrap_or_else(|error| panic!("{error}"));
        row.set("necessity_sources", evidence.len());
        row.set(
            "necessity_joint",
            evidence
                .iter()
                .filter(|record| {
                    record.causal_bucket
                        == ownership_diagnostic_package::CausalBucket::JointNoSingleFamilyNecessity
                })
                .count(),
        );
        row.set(
            "necessity_pair_recovered",
            evidence
                .iter()
                .filter(|record| {
                    record
                        .pair_removal
                        .as_ref()
                        .is_some_and(|pair| !pair.minimal_sat_pairs.is_empty())
                })
                .count(),
        );
        row.set(
            "necessity_no_pair",
            evidence
                .iter()
                .filter(|record| {
                    record
                        .pair_removal
                        .as_ref()
                        .is_some_and(|pair| pair.no_pair())
                })
                .count(),
        );
        row.set("check_sat_count", check_sat_count);
        row.set("t_total_s", secs(t0.elapsed()));
        row.set("status", "ok");
        row
    }

    /// BO mode: the exact `assert_ownership_parity` construction, with the native fixpoint loop's
    /// round/commit counts (`verify_to_fixpoint_counting`), per-phase timings, and the model readout
    /// (kind tallies + leaked sources).
    pub fn run_bo(tcx: TyCtxt<'_>, t_tcx: Duration) -> Row {
        let t0 = Instant::now();
        let mut row = Row::default();
        row.set("t_tcx_s", secs(t_tcx));

        // §NB5-Z (2026-07-17): stamp the z3 library version on every BO row — provenance for the seed
        // pin. The PIN itself lives at the ignored `boc1_run_one` worker entry (see there for why it
        // must NOT live here or in the solver — both are reached by the parallel suite). Unconditional
        // now (was `CRAT_BOC1_COLLATERAL`-gated in NB4-4c-Q).
        row.set("z3_full_version", z3::full_version().to_string());

        let program = collect_program(tcx);
        row.set("fn_count", program.functions.len());
        row.set("struct_count", program.structs.len());

        // NB5-O: derive BO-native signature summaries and body flows ONCE per program,
        // kind-independent. The summaries feed candidacy while the retained body flows feed the
        // native replay seam. `ORIGIN_DERIVATION_COUNT` pins this actual full-program fixpoint
        // boundary. `t_origins_s` keeps the existing brotli cost watch.
        let t = Instant::now();
        let origins = compute_origins(&program);
        row.set("t_origins_s", secs(t.elapsed()));
        // Brotli-scale stop instrumentation. `origin_slots` is the BO-native signature-slot count;
        // `subset_edges` reports the transitively closed summary relation (the main retained-space
        // concern).
        row.set(
            "origin_slots",
            origins.values().map(|s| s.slots.len()).sum::<usize>(),
        );
        row.set(
            "origin_subset_edges",
            origins
                .values()
                .map(|s| {
                    s.subset
                        .rows()
                        .map(|r| s.subset.row(r).map_or(0, |b| b.iter().count()))
                        .sum::<usize>()
                })
                .sum::<usize>(),
        );
        // §NB3-3c-i F5 (Codex): the other retained-footprint dimension besides slots/subset edges is
        // the poisoned-slot set. (Storage is no longer a separate matrix — it folds into subset, F4 —
        // so there is no separate storage-edge count to report.)
        row.set(
            "origin_unknown_slots",
            origins.values().map(|s| s.unknown.count()).sum::<usize>(),
        );

        // §NB4-4c SEED-SIZE GATE (amendment 1): compute-only poisoned-slot tiers + untabled-extern
        // histogram, then return BEFORE the emit/solve. Sizes the F2 arg/field extensions so the
        // demotion row cannot be catastrophic "for the wrong reason" (a printf/fprintf-class untabled
        // extern making every pointer arg it touches Raw). Off by default; no effect on normal sweeps.
        //   tier-1 `poison_base`             = current `collect_no_borrow_origin_slots` (fields skipped)
        //   tier-2 `poison_arg0_extern_delta`= depth-0 raw-ptr args to UNTABLED externs, NEW over base
        //   tier-3 `poison_field_sig`        = `summary.unknown` field-slots (count only; the kind-slot
        //                                      bridge is the deferred RED-5 spike, not needed for sizing)
        //   `untabled_externs`              = "name:ptr_arg_calls" histogram, top 12 by frequency
        if std::env::var_os("CRAT_BOC1_SEED_SIZE").is_some() {
            use rustc_hash::{FxHashMap, FxHashSet};
            use rustc_middle::mir::TerminatorKind;

            use crate::analyses::borrow_ownership::{
                boundary_table::{self, Matcher},
                origins::collect_no_borrow_origin_slots,
            };

            let slots = CrateSlots::build(&program);
            // The full no-borrow-origin set (base signature slots + mapped fields). Decompose it into
            // the two tiers so they don't double-count (the diagnostic's job is to isolate the field
            // extension): `poison_base` = unique Local members, `poison_field` = unique mapped
            // `SlotRef::Field` members. `all` (both) is the membership set the arg0-tier delta checks.
            let all: FxHashSet<SlotRef> = collect_no_borrow_origin_slots(&origins, &slots)
                .into_iter()
                .collect();
            let base: FxHashSet<SlotRef> = all
                .iter()
                .copied()
                .filter(|s| matches!(s, SlotRef::Local(..)))
                .collect();
            row.set("poison_base", base.len());
            row.set(
                "poison_field",
                all.iter()
                    .filter(|s| matches!(s, SlotRef::Field(_)))
                    .count(),
            );

            // c2rust emits cross-module *local* callees as `extern "C"` DECLARATIONS (ForeignItems
            // with no body) at their call sites, while the DEFINITION lives elsewhere in the crate.
            // Those are summary-covered, NOT opaque — exclude them by name so "opaque" means a
            // genuine foreign symbol (no crate-local definition), matching lifetime_flow's notion.
            let crate_fn_names: FxHashSet<String> = program
                .functions
                .iter()
                .map(|f| tcx.item_name(f.to_def_id()).to_string())
                .collect();

            let mut arg0_new: FxHashSet<SlotRef> = FxHashSet::default();
            let mut hist: FxHashMap<String, usize> = FxHashMap::default();
            for &fn_did in &program.functions {
                let Some(universe) = slots.fn_local_slots.get(&fn_did) else {
                    continue;
                };
                let body = tcx.mir_drops_elaborated_and_const_checked(fn_did).borrow();
                for bb in body.basic_blocks.iter() {
                    let Some(term) = &bb.terminator else { continue };
                    let TerminatorKind::Call { func, args, .. } = &term.kind else {
                        continue;
                    };
                    // Untabled extern = a crate-local `ForeignItem` decl with no ForeignC row
                    // (mirrors `sources.rs::is_allocator_call` gating). Opaque = worst-case.
                    let Some((def_id, _)) = func.const_fn_def() else { continue };
                    let Some(local_did) = def_id.as_local() else { continue };
                    let rustc_hir::Node::ForeignItem(fi) = tcx.hir_node_by_def_id(local_did) else {
                        continue;
                    };
                    let name = fi.ident.as_str();
                    if boundary_table::lookup(name, Matcher::ForeignC).is_some() {
                        continue; // tabled — a known effect row, not opaque
                    }
                    if crate_fn_names.contains(name) {
                        continue; // cross-module crate-local decl — summary-covered, not opaque
                    }
                    let mut ptr_args = 0usize;
                    for a in args.iter() {
                        let Some(place) = a.node.place() else { continue };
                        if !place.ty(&*body, tcx).ty.is_raw_ptr() {
                            continue;
                        }
                        ptr_args += 1;
                        if let Some(base_local) = place.as_local()
                            && let Some(id) = universe.slot_for_local_depth(base_local, 0)
                        {
                            let sref = SlotRef::Local(fn_did, id);
                            if !base.contains(&sref) {
                                arg0_new.insert(sref);
                            }
                        }
                    }
                    if ptr_args > 0 {
                        *hist.entry(name.to_string()).or_default() += ptr_args;
                    }
                }
            }
            row.set("poison_arg0_extern_delta", arg0_new.len());

            let field_sig: usize = origins
                .values()
                .map(|s| {
                    s.unknown
                        .iter()
                        .filter(|slot| s.slots[*slot].place.field.is_some())
                        .count()
                })
                .sum();
            row.set("poison_field_sig", field_sig);

            let mut hv: Vec<(String, usize)> = hist.into_iter().collect();
            hv.sort_by(|x, y| y.1.cmp(&x.1).then(x.0.cmp(&y.0)));
            let hs = hv
                .iter()
                .take(12)
                .map(|(n, c)| format!("{n}:{c}"))
                .collect::<Vec<_>>()
                .join(",");
            row.set("untabled_externs", hs);
            row.set("status", "seed-size");
            return row;
        }

        // The same `origins` value is threaded into both constraint emission and replay below;
        // neither consumer reruns the native derivation.

        // §NB3-3c-i measurement seam: origins-only mode returns before the fixpoint solve, so the
        // origin-derivation cost (t_origins) and size (origin_slots/origin_subset_edges) can be
        // sampled at brotli scale without paying the ~minutes-long z3 fixpoint. Off by default —
        // no effect on any normal sweep run. Reused verbatim at 3c-ii's double-sweep origins-watch.
        if std::env::var_os("CRAT_BOC1_ORIGINS_ONLY").is_some() {
            row.set("status", "origins-only");
            return row;
        }

        // MIR warm-up: forces the (memoized) query per fn so `t_slots`/`t_emit`
        // below time the analysis, not rustc's MIR pipeline. Result-neutral.
        let t = Instant::now();
        for &g in &program.functions {
            let _ = tcx.mir_drops_elaborated_and_const_checked(g);
        }
        row.set("t_mir_s", secs(t.elapsed()));
        phase("mir_done", t0);

        let t = Instant::now();
        let slots = CrateSlots::build(&program);
        row.set("t_slots_s", secs(t.elapsed()));
        let slots_total: usize = slots.field_slots.len()
            + slots
                .fn_local_slots
                .values()
                .map(|u| u.len())
                .sum::<usize>();
        row.set("slots_total", slots_total);
        phase("slots_done", t0);

        // §NB4-4c per-class demotion counts (rider 5): the no-borrow-origin slots the may-supply
        // `¬ref` demotes, split base (Local) vs struct field. The honest per-class sweep columns.
        {
            let demoted =
                crate::analyses::borrow_ownership::origins::collect_no_borrow_origin_slots(
                    &origins, &slots,
                );
            let field_ct = demoted
                .iter()
                .filter(|s| matches!(s, SlotRef::Field(_)))
                .count();
            row.set("nb4c_demoted_base", demoted.len() - field_ct);
            row.set("nb4c_demoted_field", field_ct);
        }

        // §NB4-4c-Q COUNT-ONLY (compute-only, no solve): the over-inclusion COUNTS for programs whose
        // collateral SOLVE times out (binn/brotli under the 3-solve collateral mode). If a program's
        // upper over-inclusion is 0, its collateral is 0 by construction (no slot removed) — the gate is
        // complete without the expensive solve. Off by default; returns before emit/fixpoint.
        if std::env::var_os("CRAT_BOC1_COLLATERAL_COUNT").is_some() {
            use crate::analyses::borrow_ownership::origins::{
                collect_overincluded_modeled_origin_slots, collect_upperbound_overincluded_slots,
            };
            let dedup = |v: Vec<SlotRef>| v.into_iter().collect::<FxHashSet<_>>().len();
            row.set(
                "nb4c_overincl_raw",
                dedup(collect_overincluded_modeled_origin_slots(
                    &origins, &slots, false,
                )),
            );
            row.set(
                "nb4c_overincl_mit",
                dedup(collect_overincluded_modeled_origin_slots(
                    &origins, &slots, true,
                )),
            );
            row.set(
                "nb4c_overincl_upper",
                dedup(collect_upperbound_overincluded_slots(&origins, &slots)),
            );
            row.set("status", "collateral-count");
            return row;
        }

        // ALLOW-LIST capture (ruling on ADV-1). Capture is armed HERE and
        // disarmed immediately after the fixpoint, so the export describes the
        // accepted run and nothing else. Every probe below — `explain_unsat`,
        // `measure_collateral`/`solve_with_demotion`, the CHECK_REAL second
        // fixpoint, and any surface added later — is outside this scope and
        // therefore records nothing BY CONSTRUCTION, with no enumeration to
        // keep in sync. Two prior cycles shipped an incomplete deny-list.
        //
        // RAII rather than a closure: the emit-error path below does an early
        // `return row`, and `Drop` ends the scope correctly on that path
        // without restructuring the region.
        let capture_arm = crate::analyses::borrow_ownership::export::arm_capture();
        let crate_ctxt = CrateCtxt::new(&program);
        let solver = KindSolver::new(&slots);
        let t = Instant::now();
        let (stats, selectors) =
            match emit_crate_ownership_constraints(&crate_ctxt, &slots, &origins, &solver) {
                Ok(x) => x,
                Err(e) => {
                    row.set("status", "emit-error");
                    row.set("err", format!("{e:#}"));
                    return row;
                }
            };
        row.set("t_emit_s", secs(t.elapsed()));
        row.set("z3_ast_len", stats.z3_ast_len);
        row.set("source_sink_emissions", stats.source_sink_emissions);
        row.set("selectors", selectors.all().len());
        // §NB1: record the active safety-monotonicity mode so the ablation
        // sweeps (per_site vs chain) are self-labeling in the results.
        row.set("safe_mono", SafeMonoMode::current().label());
        // §NB2: record the active mutability-facts mode (on = fact-driven immutability from
        // Foster; off = pre-NB2 forced-mut) so the dual-mode sweep is self-labeling.
        row.set("mut_facts", MutFactsMode::current().label());
        phase("emit_done", t0);

        let t = Instant::now();
        for &g in &program.functions {
            let body = tcx.mir_drops_elaborated_and_const_checked(g).borrow();
            add_coherence(&solver, &slots, g, &body);
        }
        row.set("t_coherence_s", secs(t.elapsed()));
        phase("coherence_done", t0);

        // §NB2: build the per-local mutability oracle once (production-parity map). Mode Off
        // reproduces pre-NB2 forced-mut; the borrow replay reads it per pointer local.
        let t = Instant::now();
        let mut_facts = match MutFactsMode::current() {
            MutFactsMode::Off => MutFacts::all_mut(),
            MutFactsMode::On => MutFacts::from_program(&program),
        };
        row.set("t_mut_facts_s", secs(t.elapsed()));

        let t = Instant::now();
        // §NB5-M: native fork counters (the bo_c1 mirror is RETIRED — parity was proven at the NB5-M
        // gate, byte-identical to the NB5-Z baseline on all 19 both profiles). `verify_to_fixpoint_counting`
        // is the single CEGAR loop; `verify_to_fixpoint` is its model-only wrapper.
        // §NB5-L2: under `CRAT_BOC1_NECESSITY_AUDIT`, wrap the SAME solve in `with_capture` so Mode-A's
        // `(slot, round)` commits are recorded — a side-channel, so `(model, rstats)` are byte-identical
        // to the non-audit branch (the sweep numbers do not move whether or not the audit is on).
        let audit = std::env::var_os("CRAT_BOC1_NECESSITY_AUDIT").is_some();
        let certified_context = certified_context_enabled();
        let selector_core_capture = match std::env::var("CRAT_BOC1_SELECTOR_CORE").as_deref() {
            Err(std::env::VarError::NotPresent) | Ok("0") => false,
            Ok("official") => true,
            Ok(other) => panic!(
                "CRAT_BOC1_SELECTOR_CORE must be 0 or official in the BO worker, got {other:?}"
            ),
            Err(error) => panic!("CRAT_BOC1_SELECTOR_CORE is not valid Unicode: {error}"),
        };
        assert!(
            [audit, certified_context, selector_core_capture]
                .into_iter()
                .filter(|enabled| *enabled)
                .count()
                <= 1,
            "necessity audit, certified-context replay, and selector-core capture are mutually exclusive"
        );
        let ((model, rstats), captured) = if selector_core_capture {
            let ((model_and_stats, commit_trace), selector_trace) = with_selector_trace(|| {
                with_mode_a_commit_trace(|| {
                    verify_to_fixpoint_counting_with_flows(
                        &program,
                        &slots,
                        origins.native_flows(),
                        &solver,
                        &selectors,
                        &mut_facts,
                    )
                })
            });
            let trace_path = std::env::var("CRAT_BOC1_SELECTOR_TRACE")
                .expect("official selector-core worker requires CRAT_BOC1_SELECTOR_TRACE");
            let program_name = std::env::var("CRAT_BOC1_NAME")
                .expect("official selector-core worker requires CRAT_BOC1_NAME");
            let trace = selector_leak_diagnosis::official_trace(
                &program_name,
                &super::orchestrate::git_sha(),
                &program.functions,
                selector_trace,
                commit_trace,
            );
            selector_leak_diagnosis::write_official_trace(Path::new(&trace_path), &trace)
                .unwrap_or_else(|error| panic!("{error}"));
            (model_and_stats, None)
        } else if audit || certified_context {
            let (mr, events) = with_capture(|| {
                verify_to_fixpoint_counting_with_flows(
                    &program,
                    &slots,
                    origins.native_flows(),
                    &solver,
                    &selectors,
                    &mut_facts,
                )
            });
            (mr, Some(events))
        } else {
            (
                verify_to_fixpoint_counting_with_flows(
                    &program,
                    &slots,
                    origins.native_flows(),
                    &solver,
                    &selectors,
                    &mut_facts,
                ),
                None,
            )
        };
        // End of the accepted-run region: everything after this point is
        // reporting or probing, and must not reach the recorder. M1 replaces
        // this `drop` with `capture_arm.finish()` to consume the export.
        drop(capture_arm);
        row.set("t_fixpoint_s", secs(t.elapsed()));
        phase("fixpoint_done", t0);

        // §NB5-L guard 3 — mode-stamp the sweep row with the repair strategy that produced it, so the
        // S7 both-mode differential is never mode-ambiguous in the log.
        row.set("repair", rstats.repair.label());
        row.set("rounds", rstats.rounds);
        row.set("commits_conflict", rstats.commits_conflict);
        row.set("check_sat_count", solver.check_sat_count());
        row.set(
            "commits_per_round",
            rstats
                .commits_per_round
                .iter()
                .map(|c| c.to_string())
                .collect::<Vec<_>>()
                .join("/"),
        );

        let sources = collect_malloc_source_slots(program.tcx, &program.functions, &slots);
        row.set("sources_total", sources.len());

        // §NB-F: selector-level leak accounting (SLOT-level `sources_leaked`
        // below is unchanged). `sinks_leaked` counts frees the relax loop
        // dropped — leak-the-free semantics, the stage-1 headline metric.
        row.set("sinks_total", selectors.sinks().len());
        row.set("sinks_leaked", rstats.dropped_sinks);
        row.set("sources_leaked_sel", rstats.dropped_sources);

        // §S2-3 field-yield histogram (NB5-F). Model-independent buckets: `fields_total` = depth-0
        // pointer field slots (denominator); `stores_owned` = Owning CANDIDATES (≥1 owned store, no
        // blocking non-owned store) from the same scan the field-ownership constraints use; `blocked`
        // = fields with a non-owned store (upstream cause). `owning_model` (the S2-3 gate numerator —
        // fields that come out `Owning` in the accepted model) is emitted in the accept arm below.
        let s23_fields_total = (0..slots.field_slots.len())
            .filter(|&i| slots.field_slots.slot(SlotId::from_usize(i)).depth == 0)
            .count();
        let (s23_candidates, s23_blocked) = field_ownership_candidates(&slots, &program);
        row.set("s23_fields_total", s23_fields_total);
        row.set("s23_stores_owned", s23_candidates.len());
        row.set("s23_blocked", s23_blocked.len());

        match &model {
            None => {
                row.set("status", "decline");
                // §NB5-F: a field-conflict decline is SAT-with-a-non-`Ref`-field-residual, NOT an
                // UNSAT — running `decline_reason` (a selector-core replay) would misreport it as
                // `sat-in-replay`. Intercept it from the native stats FIRST, tag it distinctly, and
                // attribute it to the offending field for the sweep's per-program accounting (rider 1).
                // Only genuine UNSAT-family declines fall through to `decline_reason` + the explain path.
                // §NB5-L (Codex MEDIUM): a `Lemmas` cap-exhaustion decline is a relaxed-SAT model that
                // hit the round cap — NOT an UNSAT. Intercept it FIRST so `decline_reason` (a
                // selector-core replay) does not mislabel it `sat-in-replay` and hide the cap exhaustion.
                if let Some(reason) = &rstats.l2_decline {
                    row.set("decline_reason", "l2");
                    row.set("l2_decline", reason.diagnostic_label(rstats.rounds));
                } else if rstats.cap_exhausted {
                    row.set("decline_reason", "cap-exhausted");
                } else if let Some(field_slot) = rstats.field_conflict_decline {
                    row.set("decline_reason", "field-conflict");
                    if let SlotRef::Field(id) = field_slot
                        && let SlotOwner::Field(f) = slots.field_slots.slot(id).owner
                    {
                        row.set(
                            "decline_field",
                            format!(
                                "{}::field{}",
                                tcx.def_path_str(f.struct_did.to_def_id()),
                                f.field_index
                            ),
                        );
                    }
                } else {
                    row.set("decline_reason", decline_reason(&solver, &selectors));
                }
                // §NB-R (opt-in): explain the decline via a second, TRACKED
                // construction — labeled minimal core (or family histogram at
                // scale). Never on the default path: doubles solve cost. §NB5-F/L: skip for
                // field-conflict and cap-exhaustion declines (both are SAT, so the tracked replay
                // would not be UNSAT).
                if rstats.field_conflict_decline.is_none()
                    && !rstats.cap_exhausted
                    && rstats.l2_decline.is_none()
                    && std::env::var("CRAT_BOC1_EXPLAIN")
                        .map(|v| v == "1")
                        .unwrap_or(false)
                {
                    let t = Instant::now();
                    match super::explain::explain_unsat(tcx) {
                        super::explain::Explained::Unsat { core, minimized } => {
                            row.set("core_size", core.len());
                            row.set("core_minimized", minimized);
                            row.set("core_families", super::explain::family_histogram(&core));
                            for label in &core {
                                eprintln!("NBRCORE {label}");
                            }
                        }
                        super::explain::Explained::Sat => {
                            row.set("core_families", "sat-in-tracked-replay");
                        }
                        super::explain::Explained::Unknown => {
                            row.set("core_families", "z3-unknown-in-tracked-replay");
                        }
                    }
                    row.set("t_explain_s", secs(t.elapsed()));
                    phase("explain_done", t0);
                }
            }
            Some(m) => {
                let (mut n_ref, mut n_raw, mut n_own) = (0usize, 0usize, 0usize);
                let (mut n_ref_d0, mut n_raw_d0, mut n_own_d0) = (0usize, 0usize, 0usize);
                // §NB2: split depth-0 Ref into shared (&T) vs mut (&mut T) via the fact map,
                // and count depth-0 slots that defaulted to Mut for lack of a fact
                // (missing-data guard — requirement #1; ~0 when the map is complete).
                let (mut n_ref_shared_d0, mut n_ref_mut_d0, mut mut_default_fires) =
                    (0usize, 0usize, 0usize);
                for (s, kind) in m {
                    match kind {
                        SlotKind::Ref => n_ref += 1,
                        SlotKind::Raw => n_raw += 1,
                        SlotKind::Owning => n_own += 1,
                    }
                    // Depth-0 LOCAL slots only: the accounting `n_ref_prod`
                    // (production baseline) is comparable with.
                    if let SlotRef::Local(fn_did, sid) = s
                        && let Some(u) = slots.fn_local_slots.get(fn_did)
                        && u.slot(*sid).depth == 0
                    {
                        match kind {
                            SlotKind::Ref => n_ref_d0 += 1,
                            SlotKind::Raw => n_raw_d0 += 1,
                            SlotKind::Owning => n_own_d0 += 1,
                        }
                        if let SlotOwner::Local(local) = u.slot(*sid).owner {
                            if mut_facts.is_defaulted(*fn_did, local) {
                                mut_default_fires += 1;
                            }
                            if *kind == SlotKind::Ref {
                                if mut_facts.is_mutable(*fn_did, local) {
                                    n_ref_mut_d0 += 1;
                                } else {
                                    n_ref_shared_d0 += 1;
                                }
                            }
                        }
                    }
                }
                let leaked = sources
                    .iter()
                    .filter(|s| m.get(s) != Some(&SlotKind::Owning))
                    .count();
                row.set("status", "ok");
                row.set("n_ref", n_ref);
                row.set("n_raw", n_raw);
                row.set("n_own", n_own);
                row.set("n_ref_d0", n_ref_d0);
                row.set("n_raw_d0", n_raw_d0);
                row.set("n_own_d0", n_own_d0);
                // §NB2: &T vs &mut split of n_ref_d0 (shared + mut == n_ref_d0), plus the
                // count of depth-0 slots that fell back to the Mut default.
                row.set("n_ref_shared_d0", n_ref_shared_d0);
                row.set("n_ref_mut_d0", n_ref_mut_d0);
                row.set("mut_default_fires", mut_default_fires);
                row.set("sources_leaked", leaked);
                // §S2-3 numerator: depth-0 struct-field slots that come out `Owning` in the accepted
                // model — the field-ownership yield the S2-3 gate ("still zero after NB5") consumes.
                // §NB5-F2: `s23_fields_raw` counts depth-0 field slots settled `Raw` — the direct
                // measure of the crate-wide field-demotion hammer (a Raw field's loans are disabled in
                // every function). These are INVISIBLE in `n_ref_d0`/`n_raw_d0` (Local-only), so this is
                // the column that shows the row's real field cost (pre-load 3).
                let mut s23_owning_model = 0usize;
                let mut s23_fields_raw = 0usize;
                for (s, kind) in m {
                    if let SlotRef::Field(id) = s
                        && slots.field_slots.slot(*id).depth == 0
                    {
                        match kind {
                            SlotKind::Owning => s23_owning_model += 1,
                            SlotKind::Raw => s23_fields_raw += 1,
                            SlotKind::Ref => {}
                        }
                    }
                }
                row.set("s23_owning_model", s23_owning_model);
                row.set("s23_fields_raw", s23_fields_raw);
                if let Some(path) = std::env::var_os("CRAT_BOC1_MODEL_KIND_SNAPSHOT") {
                    let records = bo_model_kind_records(tcx, &slots, m);
                    ownership_yield::write_model_kind_snapshot(Path::new(&path), &records)
                        .unwrap_or_else(|error| panic!("{error}"));
                    row.set("model_kind_snapshot", records.len());
                }
                if ownership_yield::enabled() {
                    let records = bo_slot_records(tcx, &slots, m);
                    ownership_yield::write_worker_snapshot(&records)
                        .unwrap_or_else(|error| panic!("{error}"));
                    row.set("ownership_yield_snapshot", records.len());
                }
                if let Some(records) =
                    crown_projection::maybe_write_model_snapshot(tcx, &program, &slots, m)
                {
                    row.set("crown_projection_snapshot", records);
                }
                record_l2_red_inventory(&program, &slots, m, rstats.repair, n_ref, &mut row);
            }
        }

        // §NB5-L2 commit-necessity audit (CRAT_BOC1_NECESSITY_AUDIT=1): leave-one-out over Mode-A's
        // captured commit set → the over-pin count = L2 headroom (a LOWER BOUND). MEASUREMENT-ONLY, off
        // by default; the `captured` events are `Some` only under the same gate.
        if let Some(events) = captured {
            // F3 (Codex): the audit measures Mode-A's commit set, and `with_capture` only records in the
            // Mode-A commit branch — so under any other `CRAT_BO_REPAIR` the events would be empty and the
            // audit would report a plausible-but-meaningless zero. Refuse it with an explicit status and no
            // numeric audit fields, rather than contaminating a comparative sweep.
            if rstats.repair != RepairMode::ModeA {
                row.set("na_status", "wrong-repair-mode");
            } else if certified_context {
                let t = Instant::now();
                run_certified_context(&program, &slots, &origins, &mut_facts, &events, &mut row);
                row.set("t_certified_context_s", secs(t.elapsed()));
                phase("certified_context_done", t0);
            } else {
                let t = Instant::now();
                run_necessity_audit(
                    &program, &slots, &origins, &mut_facts, &model, &events, &mut row,
                );
                row.set("t_necessity_s", secs(t.elapsed()));
                phase("necessity_done", t0);
            }
        }

        // §NB4-4c-Q collateral measurement (CRAT_BOC1_COLLATERAL=1): size the coherence-collateral
        // Ref-loss from over-including modeled-origin slots (Codex re-review 2026-07-17). Two extra
        // real solves in-process (FULL then MINUS); MEASUREMENT-ONLY. Off by default. Gate metric =
        // `nb4c_collateral_d0` (net corpus-wide); `nb4c_collateral` (full n_ref) reported alongside
        // because FIELD collateral is invisible at depth-0.
        if std::env::var_os("CRAT_BOC1_COLLATERAL").is_some() {
            let t = Instant::now();
            let cm = measure_collateral(&program, &slots, &origins, &mut_facts);
            row.set("nb4c_collateral_status", cm.status);
            row.set("nb4c_overincl_raw", cm.overincl_raw);
            row.set("nb4c_overincl_mit", cm.overincl_mit);
            row.set("nb4c_overincl_upper", cm.overincl_upper);
            row.set("nb4c_collateral_mit", cm.collateral_mit); // n_ref delta, may be < 0
            row.set("nb4c_collateral_d0_mit", cm.collateral_d0_mit);
            row.set("nb4c_collateral_upper", cm.collateral_upper); // the GATE numerator (upper bound)
            row.set("nb4c_collateral_d0_upper", cm.collateral_d0_upper);
            // ANCHOR (amendment 4a + Codex F2b): when the measurement actually solved FULL, it must
            // reproduce the shipped n_ref AND n_ref_d0 — validates emit(empty)+manual-demotion ≡ the
            // shipped pipeline here. A mismatch is a hard STOP. (Committed-row anchor is the external
            // check, post-sweep; a "real-decline" status is surfaced, never silent — F2a.) §NB5-M:
            // "shipped" is now run_bo's NATIVE `verify_to_fixpoint_counting` model (mirror retired).
            if let (Some(nf), Some(nd0), Some(m)) = (cm.nref_full, cm.nref_d0_full, &model) {
                let (shipped_nref, shipped_nref_d0) = count_refs(m, &slots);
                assert_eq!(
                    nf, shipped_nref,
                    "NB4-4c-Q ANCHOR: FULL n_ref ({nf}) != shipped n_ref ({shipped_nref})"
                );
                assert_eq!(
                    nd0, shipped_nref_d0,
                    "NB4-4c-Q ANCHOR: FULL n_ref_d0 ({nd0}) != shipped n_ref_d0 ({shipped_nref_d0})"
                );
            }
            row.set("t_collateral_s", secs(t.elapsed()));
            phase("collateral_done", t0);
        }

        // Optional corpus-level fidelity cross-check (CRAT_BOC1_CHECK_REAL=1):
        // run the REAL `verify_to_fixpoint` on a second fresh construction and
        // compare. Doubles the solve cost — off by default; the orchestrator
        // does not set it. Same mitigation as the fixture equivalence tests,
        // extended to real inputs on demand.
        if std::env::var("CRAT_BOC1_CHECK_REAL")
            .map(|v| v == "1")
            .unwrap_or(false)
        {
            let t = Instant::now();
            // Allow-list: outside the armed region ⇒ records nothing.
            let real = {
                let crate_ctxt = CrateCtxt::new(&program);
                let solver = KindSolver::new(&slots);
                // §NB4-4c F3: CHECK_REAL reuses run_bo's `origins` — the SAME demotion seed as run_bo's
                // native solve, so the fidelity cross-check compares identical clause sets.
                match emit_crate_ownership_constraints(&crate_ctxt, &slots, &origins, &solver) {
                    Ok((_s, selectors)) => {
                        for &g in &program.functions {
                            let body = tcx.mir_drops_elaborated_and_const_checked(g).borrow();
                            add_coherence(&solver, &slots, g, &body);
                        }
                        // §NB2: same oracle as run_bo's native solve above, so the fidelity check
                        // compares like with like (shipped facts vs a fresh real solve).
                        Some(verify_to_fixpoint_with_flows(
                            &program,
                            &slots,
                            origins.native_flows(),
                            &solver,
                            &selectors,
                            &mut_facts,
                        ))
                    }
                    Err(_) => None,
                }
            };
            phase("check_real_done", t0);
            match real {
                None => row.set("real_status", "emit-error"),
                Some(real) => {
                    row.set("real_status", if real.is_some() { "ok" } else { "decline" });
                    row.set("real_matches_model", (real == model).to_string());
                }
            }
            row.set("t_check_real_s", secs(t.elapsed()));
        }

        row.set("t_total_s", secs(t0.elapsed() + t_tcx));
        row
    }

    /// Harness-side diagnostic for a `decline` (Codex review F7): distinguish
    /// "the constraint system is UNSAT for non-source reasons" from "z3 gave
    /// up (Unknown)" by replaying `model_kinds_relaxing`'s phase-1 selector
    /// dropping read-only (`check` with assumptions asserts nothing). Runs on
    /// the solver state at the moment of decline, so for a round-0 decline it
    /// replays exactly the failing first solve. §S2-1: the replay mirrors the
    /// real loop's sinks-first drop priority (lockstep with `solver.rs`).
    pub(super) fn decline_reason(solver: &KindSolver, selectors: &Selectors) -> &'static str {
        // §NB-R guard (Codex F1): this replay assumes ONLY selectors; under a
        // tracked solver the hard constraints would be disabled and the reply
        // would be a bogus "sat-in-replay".
        assert!(
            solver.tracker().is_none(),
            "tracked KindSolver must not enter decline_reason (constraints are track-gated)"
        );
        let mut assumptions: Vec<Bool> = selectors.all().to_vec();
        loop {
            match solver.optimize().check(&assumptions) {
                // Should not happen (relaxing declined); a nondeterministic
                // Unknown->Sat flip lands here rather than lying.
                SatResult::Sat => return "sat-in-replay",
                SatResult::Unknown => return "z3-unknown",
                SatResult::Unsat => {
                    let core = solver.optimize().get_unsat_core();
                    let in_core = |s: &Bool| core.iter().any(|c| c == s);
                    match assumptions
                        .iter()
                        .position(|s| selectors.is_sink(s) && in_core(s))
                        .or_else(|| assumptions.iter().position(|s| in_core(s)))
                    {
                        Some(i) => {
                            assumptions.swap_remove(i);
                        }
                        None => return "unsat-nonsource",
                    }
                }
            }
        }
    }

    /// Production baseline: the independent greedy driver `assert_borrow_parity`
    /// uses (tests.rs) — `demote_pointers_iterative_with_fields` from all-Ref —
    /// mapped to depth-0 slots with the same accounting as `n_ref_d0`.
    pub fn run_prod(tcx: TyCtxt<'_>, t_tcx: Duration) -> Row {
        let t0 = Instant::now();
        let mut row = Row::default();
        row.set("t_tcx_s", secs(t_tcx));

        let program = collect_program(tcx);
        let t = Instant::now();
        for &g in &program.functions {
            let _ = tcx.mir_drops_elaborated_and_const_checked(g);
        }
        row.set("t_mir_s", secs(t.elapsed()));
        phase("mir_done", t0);

        // Same slot universe as BO mode so depth-0 accounting is identical.
        let slots = CrateSlots::build(&program);
        let mut n_slots_d0 = 0usize;
        for u in slots.fn_local_slots.values() {
            for i in 0..u.len() {
                let slot = u.slot(SlotId::from_usize(i));
                if slot.depth == 0 && matches!(slot.owner, SlotOwner::Local(_)) {
                    n_slots_d0 += 1;
                }
            }
        }
        row.set("n_slots_d0", n_slots_d0);
        phase("slots_done", t0);

        let t = Instant::now();
        let mut ctxt = GBorrowInferCtxt::new(&program, |_| |_| true, |_| |_| true);
        let d_prod = demote_pointers_iterative_with_fields(&program, &mut ctxt);
        row.set("t_prod_s", secs(t.elapsed()));
        phase("prod_done", t0);

        // Verbatim mapping from tests.rs `assert_borrow_parity`.
        let mut prod_slots: FxHashSet<SlotRef> = FxHashSet::default();
        for (g, dem) in &d_prod.locals {
            let Some(universe) = slots.fn_local_slots.get(g) else {
                continue;
            };
            for local in dem.iter() {
                if let Some(sid) = universe.slot_for_local_depth(local, 0) {
                    prod_slots.insert(SlotRef::Local(*g, sid));
                }
            }
        }
        row.set("n_demoted_prod", prod_slots.len());
        row.set("n_ref_prod", n_slots_d0 - prod_slots.len());
        row.set("status", "ok");
        row.set("t_total_s", secs(t0.elapsed() + t_tcx));
        row
    }

    /// Registered PRIMARY ownership-yield reference: run the real production ownership pipeline,
    /// solidify it without modification, and export its declaration-level universe for comparison
    /// with BO. This is selected only by the measurement-specific corpus mode; the existing
    /// production-borrow reference above remains unchanged.
    pub fn run_prod_ownership(tcx: TyCtxt<'_>, t_tcx: Duration) -> Row {
        use crate::analyses::{
            output_params::compute_output_params,
            ownership::{
                AnalysisKind, CrateCtxt as OwnershipCrateCtxt,
                solidify::SolidifiedOwnershipSchemes, total_deref_level,
                whole_program::WholeProgramAnalysis,
            },
            type_qualifier::foster::mutability::mutability_analysis,
        };

        fn records(
            program: &crate::utils::rustc::RustProgram<'_>,
            solidified: &SolidifiedOwnershipSchemes,
            output_params: &crate::analyses::output_params::OutputParams,
        ) -> Vec<SlotRecord> {
            let tcx = program.tcx;
            let mut records = Vec::new();
            for &fn_did in &program.functions {
                let body = tcx.mir_drops_elaborated_and_const_checked(fn_did).borrow();
                let result = solidified.fn_results(&fn_did.to_def_id());
                for local in body.local_decls.indices() {
                    for (depth, ownership) in result.local_result(local).iter().enumerate() {
                        let depth =
                            u8::try_from(depth).expect("production local pointer depth exceeds u8");
                        records.push(SlotRecord {
                            key: local_key(tcx, fn_did, local.index(), depth),
                            owner: OwnerClass::Local,
                            depth,
                            owning: ownership.is_owning(),
                            forced_output: ownership.is_owning()
                                && depth == 0
                                && output_params
                                    .get(&fn_did)
                                    .is_some_and(|params| params.contains(local)),
                        });
                    }
                }
            }

            for &struct_did in &program.structs {
                let ty = tcx.type_of(struct_did).skip_binder();
                let TyKind::Adt(adt_def, _) = ty.kind() else {
                    continue;
                };
                for (field_index, _) in adt_def.all_fields().enumerate() {
                    for (depth, ownership) in solidified
                        .struct_field_result(&struct_did.to_def_id(), field_index)
                        .iter()
                        .enumerate()
                    {
                        let depth =
                            u8::try_from(depth).expect("production field pointer depth exceeds u8");
                        records.push(SlotRecord {
                            key: field_key(tcx, struct_did, field_index, depth),
                            owner: OwnerClass::Field,
                            depth,
                            owning: ownership.is_owning(),
                            forced_output: false,
                        });
                    }
                }
            }
            records
        }

        let t0 = Instant::now();
        let mut row = Row::default();
        row.set("t_tcx_s", secs(t_tcx));
        row.set("z3_full_version", z3::full_version().to_string());
        let program = collect_program(tcx);
        row.set("fn_count", program.functions.len());
        row.set("struct_count", program.structs.len());

        let t = Instant::now();
        for &fn_did in &program.functions {
            let _ = tcx.mir_drops_elaborated_and_const_checked(fn_did);
        }
        row.set("t_mir_s", secs(t.elapsed()));
        phase("mir_done", t0);

        let t = Instant::now();
        let arena = typed_arena::Arena::new();
        let type_shapes = ::utils::ty_shape::get_ty_shapes(&arena, tcx, false);
        let andersen_config = andersen::Config {
            use_optimized_mir: false,
            c_exposed_fns: FxHashSet::default(),
        };
        let pre_points_to = andersen::pre_analyze(&andersen_config, &type_shapes, tcx);
        let points_to = andersen::analyze(&andersen_config, &pre_points_to, &type_shapes, tcx);
        let aliases = crate::rewriter::find_param_aliases(&pre_points_to, &points_to, tcx);
        row.set("t_andersen_s", secs(t.elapsed()));
        phase("andersen_done", t0);

        let t = Instant::now();
        let mutability = mutability_analysis(&program);
        let output_params = compute_output_params(&program, &mutability, &aliases);
        row.set("t_output_params_s", secs(t.elapsed()));
        row.set(
            "forced_output_params",
            output_params
                .values()
                .map(|params| params.iter().count())
                .sum::<usize>(),
        );
        phase("output_params_done", t0);

        let t = Instant::now();
        let crate_ctxt = OwnershipCrateCtxt::new(&program);
        let results =
            match <WholeProgramAnalysis as AnalysisKind>::analyze(crate_ctxt, &output_params) {
                Ok(results) => results,
                Err(error) => {
                    row.set("status", "ownership-error");
                    row.set("err", format!("{error:#}"));
                    row.set("t_ownership_s", secs(t.elapsed()));
                    row.set("t_total_s", secs(t0.elapsed() + t_tcx));
                    return row;
                }
            };
        row.set("t_ownership_s", secs(t.elapsed()));
        phase("ownership_done", t0);

        let t = Instant::now();
        let solidified = results.solidify(&program);
        row.set("t_solidify_s", secs(t.elapsed()));
        phase("solidify_done", t0);

        let records = records(&program, &solidified, &output_params);
        let counts = ownership_yield::side_counts(&records);
        if let Ok(path) = std::env::var("CRAT_BOC1_PROD_PRECISION_EVIDENCE") {
            let required_precision = std::cmp::min(
                program
                    .functions
                    .iter()
                    .copied()
                    .map(|did| {
                        let body = tcx.mir_drops_elaborated_and_const_checked(did).borrow();
                        total_deref_level(&body) + 1
                    })
                    .max()
                    .unwrap_or(0),
                3,
            );
            let functions = program
                .functions
                .iter()
                .copied()
                .map(|did| {
                    let final_precision = results.precision(&did.to_def_id());
                    let body = tcx.mir_drops_elaborated_and_const_checked(did).borrow();
                    let fn_result = solidified.fn_results(&did.to_def_id());
                    let owning_locals = body
                        .local_decls
                        .indices()
                        .map(|local| {
                            fn_result
                                .local_result(local)
                                .iter()
                                .filter(|ownership| ownership.is_owning())
                                .count()
                        })
                        .sum();
                    FunctionPrecisionRecord {
                        program: std::env::var("CRAT_BOC1_NAME")
                            .expect("production precision worker name"),
                        function: tcx.def_path_str(did.to_def_id()),
                        required_precision,
                        final_precision,
                        class: ownership_diagnostic_package::precision_class(
                            final_precision,
                            required_precision,
                        ),
                        owning_locals,
                    }
                })
                .collect::<Vec<_>>();
            let local_owning = functions
                .iter()
                .map(|record| record.owning_locals)
                .sum::<usize>();
            let field_owning_not_applicable = counts.field_owning_by_depth.values().sum::<usize>();
            assert_eq!(
                local_owning + field_owning_not_applicable,
                counts.total_owning,
                "production precision attribution must reconcile to solver-layer Owning"
            );
            ownership_diagnostic_package::write_json(
                Path::new(&path),
                &ProductionPrecisionEvidence {
                    program: std::env::var("CRAT_BOC1_NAME")
                        .expect("production precision worker name"),
                    functions,
                    field_owning_not_applicable,
                    total_owning: counts.total_owning,
                },
            )
            .unwrap_or_else(|error| panic!("{error}"));
        }
        let forced = records.iter().filter(|record| record.forced_output).count();
        row.set("n_own_prod", counts.total_owning);
        row.set(
            "n_own_prod_fields",
            counts.field_owning_by_depth.values().sum::<usize>(),
        );
        row.set("n_own_prod_forced_output", forced);
        row.set(
            "n_own_prod_without_forced",
            counts
                .total_owning
                .checked_sub(forced)
                .expect("forced output entries exceed production Owning count"),
        );
        if std::env::var_os("CRAT_BOC1_YIELD_SNAPSHOT").is_some() {
            ownership_yield::write_worker_snapshot(&records)
                .unwrap_or_else(|error| panic!("{error}"));
            row.set("ownership_yield_snapshot", records.len());
        }
        row.set("status", "ok");
        row.set("t_total_s", secs(t0.elapsed() + t_tcx));
        row
    }

    /// **S2a-H corpus reconciliation** (C.4 + C.5, repaired in Track 1).
    ///
    /// Emits producer A's and producer B's artifacts for one program and
    /// reconciles them. The comparison itself lives in `coverage_recon`; this
    /// is the harness that feeds it and reports the per-program verdict.
    ///
    /// # The verdict flows THROUGH THE FILES
    ///
    /// The artifacts are written, read back, decoded, and the **decoded** rows
    /// are what `compare` sees. That is the ratified architecture — the
    /// comparison is an artifact diff — and the first implementation quietly
    /// deviated from it by comparing the in-memory rows, which meant `decode`
    /// had no consumer and an encoder defect could not reach a verdict.
    ///
    /// `CRAT_BOC1_ARTIFACT_DIR` is therefore **mandatory** for this mode: no
    /// files, no verdict. Write failures panic rather than being swallowed.
    ///
    /// # Per-program verdict (C.5)
    ///
    /// `status` DERIVES from the verdict; it is never an unconditional `ok`.
    /// A pairing mismatch fails this program and its rewriter output is
    /// untrusted, but the row is still printed and **the sweep continues**, so
    /// one run yields full incidence rather than halting at the first failure.
    ///
    /// # Provenance
    ///
    /// The artifacts are run-products. Their SHA-256 digests are computed by
    /// the DRIVER with `shasum` — the tool that already guards the
    /// frozen-corpus digest — rather than in-process by a crypto dependency
    /// added for one stamp. This function records the paths; the driver
    /// records the digests.
    pub fn run_m1_recon(tcx: TyCtxt<'_>, t_tcx: Duration) -> Row {
        use crate::coverage_recon::{compare, producer_b, schema};

        let t0 = Instant::now();
        let mut row = Row::default();
        row.set("t_tcx_s", secs(t_tcx));

        let dir = std::env::var_os("CRAT_BOC1_ARTIFACT_DIR").map(std::path::PathBuf::from).expect(
            "m1-recon requires CRAT_BOC1_ARTIFACT_DIR: the verdict is computed \
             from the written artifacts, so without a directory there is no \
             verdict to compute",
        );
        let name = std::env::var("CRAT_BOC1_NAME").unwrap_or_else(|_| "unnamed".to_string());

        let a = match crate::bo_rewriter::artifact_rows(tcx) {
            Ok(rows) => rows,
            Err(why) => {
                row.set("status", "producer-a-declined");
                row.set("detail", super::report::sanitize(&why));
                row.set("t_total_s", secs(t0.elapsed() + t_tcx));
                return row;
            }
        };
        let b = producer_b::rows(tcx);

        // TEST SEAM. Refused unless the fault variable is set; it exists so the
        // enforcement path has a witness that a real defect would trigger.
        let fault = std::env::var("CRAT_BOC1_RECON_FAULT").unwrap_or_default();
        let mut a_text = schema::encode(&a);
        if fault == "drop-a-row" {
            a_text = a_text.lines().skip(1).collect::<Vec<_>>().join("\n") + "\n";
        }
        let b_text = schema::encode(&b);

        std::fs::create_dir_all(&dir)
            .unwrap_or_else(|e| panic!("artifact dir {dir:?} not creatable: {e}"));
        let a_path = dir.join(format!("{name}.a.jsonl"));
        let b_path = dir.join(format!("{name}.b.jsonl"));
        std::fs::write(&a_path, &a_text)
            .unwrap_or_else(|e| panic!("artifact {a_path:?} not writable: {e}"));
        std::fs::write(&b_path, &b_text)
            .unwrap_or_else(|e| panic!("artifact {b_path:?} not writable: {e}"));
        if fault == "corrupt-a-file" {
            let corrupted = std::fs::read_to_string(&a_path).expect("written artifact readable");
            std::fs::write(&a_path, corrupted.replacen('{', "{,", 1)).expect("corrupt artifact");
        }
        if fault == "alter-a-file" {
            // VALID JSONL, different VALUE. This is the fault that proves the
            // verdict reads the FILE: a syntactic corruption is caught by the
            // decode step alone and would leave an in-memory comparison passing.
            let text = std::fs::read_to_string(&a_path).expect("written artifact readable");
            std::fs::write(&a_path, text.replacen("\"param_name\":\"p\"", "\"param_name\":\"ZZ\"", 1))
                .expect("alter artifact");
        }
        row.set("a_path", a_path.display());
        row.set("b_path", b_path.display());

        // THE VERDICT IS COMPUTED FROM THE FILES.
        let a_decoded = match schema::decode(
            &std::fs::read_to_string(&a_path).expect("producer A artifact readable"),
        ) {
            Ok(rows) => rows,
            Err(why) => {
                row.set("status", "artifact-a-undecodable");
                row.set("detail", super::report::sanitize(&why));
                row.set("recon", "FAIL");
                row.set("t_total_s", secs(t0.elapsed() + t_tcx));
                return row;
            }
        };
        let b_decoded = match schema::decode(
            &std::fs::read_to_string(&b_path).expect("producer B artifact readable"),
        ) {
            Ok(rows) => rows,
            Err(why) => {
                row.set("status", "artifact-b-undecodable");
                row.set("detail", super::report::sanitize(&why));
                row.set("recon", "FAIL");
                row.set("t_total_s", secs(t0.elapsed() + t_tcx));
                return row;
            }
        };
        row.set("a_rows", a_decoded.len());
        row.set("b_rows", b_decoded.len());

        // Activation contract (c): the axis state is printed PER PROGRAM, in
        // every sweep line. Dormancy must be visible, never inferred silence.
        row.set(
            "span_axis",
            if compare::span_axis_active(&b_decoded) {
                "ACTIVE"
            } else {
                "INACTIVE"
            },
        );

        // S3.2′-0 — the facts-side join, written beside the artifacts it
        // explains. Ordering-independent by construction: it reads the facts,
        // not the decision, which is the whole reason the ruled method is a
        // join rather than a reason-field tally.
        //
        // MEASUREMENT ONLY: written before the verdict is computed and read by
        // nothing that computes it.
        match crate::bo_rewriter::facts_join_tsv(tcx) {
            Ok(tsv) => {
                let path = dir.join(format!("{name}.facts.tsv"));
                std::fs::write(&path, tsv)
                    .unwrap_or_else(|e| panic!("write facts join {}: {e}", path.display()));
                row.set("facts_join", "ok");
            }
            // R3 — no silent caps. A program the pass cannot cover is recorded
            // WITH ITS CAUSE, in the row, so an absent artifact is never read as
            // an absent finding.
            Err(why) => row.set("facts_join", super::report::sanitize(&why)),
        }

        // R2 — the fatness pass is SEPARATE, and its failure is caught here.
        // When fatness rode inside the facts join, one program's panic took the
        // whole invariant sweep with it. `catch_unwind` because the failure mode
        // measured on urlparser was a panic in a shared utility, not an `Err`.
        let fatness = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            crate::bo_rewriter::fatness_tsv(tcx)
        }));
        match fatness {
            Ok(Ok(tsv)) => {
                let path = dir.join(format!("{name}.fatness.tsv"));
                std::fs::write(&path, tsv)
                    .unwrap_or_else(|e| panic!("write fatness {}: {e}", path.display()));
                row.set("fatness_pass", "ok");
            }
            Ok(Err(why)) => row.set("fatness_pass", super::report::sanitize(&why)),
            Err(_) => row.set("fatness_pass", "panicked"),
        }

        let verdict = compare::compare(&a_decoded, &b_decoded);
        let aggregates_clean = record_expected_zero_aggregates(&mut row, &verdict);
        row.set("violations", verdict.violations.len());
        row.set("findings", verdict.findings.len());
        let passed = verdict.passed() && aggregates_clean;
        row.set("recon", if passed { "PASS" } else { "FAIL" });

        // Enumerate rather than summarise: full incidence in one run.
        for v in &verdict.violations {
            println!(
                "BOC1-RECON-VIOLATION class={} fn={} local={} detail={}",
                v.class, v.fn_path, v.mir_local, v.detail
            );
        }
        for f in &verdict.findings {
            println!(
                "BOC1-RECON-FINDING class={} fn={} local={} detail={}",
                f.class, f.fn_path, f.mir_local, f.detail
            );
        }

        // The owed exclusion census, from the same classify invocation.
        let universe = crate::bo_rewriter::classify_universe(tcx);
        row.set("excl_impl", universe.excluded.impl_items);
        row.set("excl_trait", universe.excluded.trait_items);
        row.set("excl_foreign", universe.excluded.foreign_items);

        row.set("t_total_s", secs(t0.elapsed() + t_tcx));
        // DERIVED, never an unconditional ok.
        row.set("status", if passed { "ok" } else { "recon-fail" });
        row
    }

    pub(super) fn record_expected_zero_aggregates(
        row: &mut Row,
        verdict: &crate::coverage_recon::compare::Verdict,
    ) -> bool {
        let mut aggregates_clean = true;
        for class in crate::coverage_recon::compare::FINDING_CLASSES {
            let key = format!("agg_{}", class.replace('-', "_"));
            match verdict.aggregates.get(class).copied() {
                Some(n) => {
                    // The VALUE is always recorded — the corpus driver checks
                    // the population-pinned class against its per-program table
                    // and needs the number present. Only the zero JUDGEMENT is
                    // class-dependent.
                    if n != 0 && crate::coverage_recon::compare::expects_zero(class) {
                        aggregates_clean = false;
                    }
                    row.set(&key, n);
                }
                None => {
                    aggregates_clean = false;
                    row.set(&key, "missing");
                }
            }
        }
        aggregates_clean
    }

    /// **M1 collector census** (coverage-apparatus review §3).
    ///
    /// Runs the SHIPPING subject collector and reports what it sees, so the
    /// alias population is a number produced by the code that matters rather
    /// than by a scratchpad reimplementation. The retired `4171/0/0/2039`
    /// census applied the same syntactic `*mut`/`*const` test as the classifier
    /// it was meant to validate, so it inherited the alias blind spot and could
    /// not have detected it.
    ///
    /// `resolved_only = resolved - syntactic_ptr` is the population the retired
    /// predicate could not see; `alias` is the C2Rust type-alias class within
    /// it.
    ///
    /// Analysis-free by design: no solver, no BO run. This measures the
    /// collector's predicate and nothing downstream of it.
    /// **1.4 validation transfer** — one diagnose, both extraction paths live.
    pub fn run_m1_diag(input: &std::path::Path) -> Row {
        let t0 = Instant::now();
        let mut row = Row::default();
        match crate::bo_rewriter::diagnose_once(input) {
            Ok((observed_root, diags)) => {
                // The FRAME, emitted once. Both extraction paths canonicalize
                // against it with the production canonicalizer, so neither side
                // carries a normalization of its own — the instrument emits the
                // raw capture and the comparison layer normalizes it.
                println!("M1DIAG-ROOT dir={}", observed_root.display());
                for d in &diags {
                    println!(
                        "M1DIAG-STRUCT file={} line={} dir={:?}",
                        d.file, d.line, d.direction
                    );
                }
                row.set("struct_diags", diags.len());
                row.set("status", "ok");
            }
            Err(why) => {
                row.set("struct_diags", 0usize);
                row.set("detail", super::report::sanitize(&why));
                row.set("status", "diag-error");
            }
        }
        row.set("t_total_s", secs(t0.elapsed()));
        row
    }

    /// **S2b.0 — full M1 pipeline on one program.** decide → plan → apply →
    /// verify, whole-crate gate, temp copies only.
    ///
    /// Takes a PATH rather than a `TyCtxt`: `rewrite_m1_path` opens its own
    /// compiler session, and nesting one inside the worker's would run two
    /// rustc invocations in one process for no reason.
    pub fn run_m1_emit(input: &std::path::Path) -> Row {
        use crate::bo_rewriter::{RewriteOutcome, rewrite_m1_path};

        let t0 = Instant::now();
        let mut row = Row::default();
        let outcome = rewrite_m1_path(input);
        row.set("t_total_s", secs(t0.elapsed()));

        // ONE filling site, reading the outcome uniformly. The previous shape
        // matched on the variant and hand-filled each arm, which zeroed a real
        // value twice — `emitted` at S2b.0 and then `reverted` while repairing
        // it. Fields that exist on both arms are read once, before the branch.
        let (
            emitted,
            degraded,
            files_touched,
            reverted,
            blind,
            probes,
            base_keys,
            base_errors,
            base_msg_env,
        ) = match &outcome {
            RewriteOutcome::Emitted {
                emitted_count,
                degradations,
                files,
                reverted_count,
                attribution_blind,
                bisect_probes,
                baseline_keys,
                baseline_errors,
                baseline_msg_env,
                ..
            } => (
                *emitted_count,
                degradations.len(),
                files.len(),
                *reverted_count,
                *attribution_blind,
                *bisect_probes,
                *baseline_keys,
                *baseline_errors,
                *baseline_msg_env,
            ),
            RewriteOutcome::Degraded {
                emitted_count,
                degradations,
                files_touched,
                reverted_count,
                attribution_blind,
                bisect_probes,
                baseline_keys,
                baseline_errors,
                baseline_msg_env,
                ..
            } => (
                *emitted_count,
                degradations.len(),
                *files_touched,
                *reverted_count,
                *attribution_blind,
                *bisect_probes,
                *baseline_keys,
                *baseline_errors,
                *baseline_msg_env,
            ),
        };
        // S3.1′ E3c — the reverted subjects BY IDENTITY, not just a count.
        //
        // `reverted` is an aggregate, and the question it is being asked (how
        // much of the revert load belongs to LOCALS) is a per-population one.
        // Rather than thread `SubjectKind` down through two partition sites,
        // this prints the identity `plan` already stamps —
        // `{owner}::{name}#{mir_local}` — which joins against the recon
        // artifact's `(fn_path, mir_local)` to recover the population. An
        // independent join beats new plumbing, per the box-candidate-split
        // precedent.
        //
        // MEASUREMENT ONLY: nothing branches on this, and no gate reads it.
        {
            let degradations = match &outcome {
                RewriteOutcome::Emitted { degradations, .. }
                | RewriteOutcome::Degraded { degradations, .. } => degradations,
            };
            let ids: Vec<&str> = degradations
                .iter()
                .filter(|d| {
                    matches!(
                        d.reason,
                        crate::bo_rewriter::decision::DegradeReason::RevertedAfterVerifyFailure
                    )
                })
                .map(|d| d.subject.as_str())
                .collect();
            for id in &ids {
                println!("M1EMIT-REVERT subject={id}");
            }
            // Stdout is NOT a channel to the sweep. `ChildOutcome` carries the
            // sentinel row and `stderr`; everything else the worker prints is
            // parsed for the row and discarded. The `println!` above is for
            // running this worker DIRECTLY; the file below is what the corpus
            // sweep can actually read — the same shape as
            // `CRAT_BOC1_ARTIFACT_DIR`.
            //
            // Measured the hard way: the first version printed only, was
            // de-risked by invoking the worker directly (where stdout IS
            // visible), and produced zero lines across a full 18-minute sweep.
            // The de-risk exercised a different invocation path from the real
            // run, which is the one property it needed to share.
            if let Some(dir) = std::env::var_os("CRAT_BOC1_REVERT_DIR") {
                let name = std::env::var("CRAT_BOC1_NAME").unwrap_or_else(|_| "unnamed".into());
                let path = std::path::Path::new(&dir).join(format!("{name}.reverts.txt"));
                // Trailing newline: without it `wc -l` reports N-1 and an
                // empty list is indistinguishable from a one-entry list.
                let body: String = ids.iter().map(|id| format!("{id}\n")).collect();
                std::fs::write(&path, body)
                    .unwrap_or_else(|e| panic!("write revert list {}: {e}", path.display()));

                // S3.2′-0 — THE OP SPLIT.
                //
                // `DegradeReason::key()` collapses every raw-pointer operation
                // to the single string `"raw-pointer-operation"`, so the
                // artifact cannot distinguish `offset` (the real slice market)
                // from `is_null` (already served by the Option forms) or from
                // `as-cast` (frequently just a `free`-site cast). That makes
                // the 1,440-subject market an UPPER BOUND with unknown
                // composition, and no yield claim may rest on it until this is
                // measured.
                //
                // Written as a side file rather than added to `Row`: this is a
                // measurement, not part of the reconciliation wire contract.
                // A new column would oblige producer B to carry a field it has
                // no opinion on — B is a coverage walker, not a decision
                // oracle — for no gain, and would perturb the row-equality
                // controls for every future sweep comparison.
                let ops: String = degradations
                    .iter()
                    .filter_map(|d| match &d.reason {
                        crate::bo_rewriter::decision::DegradeReason::RawPointerOperation {
                            op,
                        } => Some(format!("{}\t{op}\n", d.subject)),
                        _ => None,
                    })
                    .collect();
                let op_path = std::path::Path::new(&dir).join(format!("{name}.ops.tsv"));
                std::fs::write(&op_path, ops)
                    .unwrap_or_else(|e| panic!("write op split {}: {e}", op_path.display()));
            }
        }
        row.set("emitted", emitted);
        row.set("degraded", degraded);
        row.set("files_touched", files_touched);
        row.set("reverted", reverted);
        row.set("attribution_blind", blind);
        row.set("bisect_probes", probes);
        row.set("baseline_keys", base_keys);
        row.set("baseline_errors", base_errors);
        row.set("baseline_msg_env", base_msg_env);

        match &outcome {
            RewriteOutcome::Emitted {
                unplaceable,
                escalated,
                ..
            } => {
                row.set("verdict", "PASS");
                row.set("unplaceable", unplaceable.len());
                row.set(
                    "escalated",
                    match escalated.as_deref() {
                        Some(why) if why.contains("no progress") => "detector",
                        Some(why) if why.contains("round cap") => "round-cap",
                        Some(_) => "other",
                        None => "no",
                    },
                );
                row.set("status", "ok");
            }
            RewriteOutcome::Degraded { reason, unplaceable, .. } => {
                // A gate failure is DATA, not an error to repair mid-run.
                row.set("verdict", "FAIL");
                // READ, not written as `0usize`. The constant here made every
                // FAIL row's `unplaceable` a claim about nothing, and S2b.3's
                // pin would have inherited it.
                row.set("unplaceable", unplaceable.len());
                row.set("escalated", "failed");
                row.set("detail", super::report::sanitize(reason));
                row.set("status", "gate-fail");
            }
        }
        row
    }

    pub fn run_m1_census(tcx: TyCtxt<'_>, t_tcx: Duration) -> Row {
        let t0 = Instant::now();
        let mut row = Row::default();
        row.set("t_tcx_s", secs(t_tcx));
        let census = crate::bo_rewriter::census(tcx);
        row.set("resolved", census.resolved);
        row.set("syntactic_ptr", census.syntactic_ptr);
        row.set(
            "resolved_only",
            census.resolved.saturating_sub(census.syntactic_ptr),
        );
        row.set("alias", census.resolved_only_alias);
        row.set("reference", census.resolved_only_reference);
        row.set("other", census.resolved_only_other);
        row.set("t_total_s", secs(t0.elapsed() + t_tcx));
        row.set("status", "ok");
        row
    }

    /// Production end-to-end decision worker. The generated source is
    /// intentionally discarded; final pointer decisions are emitted by the
    /// existing full diagnostics surface and parsed by the parent harness.
    pub fn run_prod_box(tcx: TyCtxt<'_>, t_tcx: Duration) -> Row {
        let t0 = Instant::now();
        let mut row = Row::default();
        row.set("t_tcx_s", secs(t_tcx));
        let (generated, _) = crate::replace_local_borrows(&crate::Config::default(), tcx);
        drop(generated);
        row.set("t_total_s", secs(t0.elapsed() + t_tcx));
        row.set("status", "ok");
        row
    }

    /// §NB3-3c-i runs-once invariant: the driver (`run_bo`) computes signature origins EXACTLY ONCE
    /// per program, kind-independent. `ORIGIN_DERIVATION_COUNT` is thread-local, so this before/after
    /// delta
    /// around a single `run_bo` call — all on one compiler-callback thread — is race-free under the
    /// suite's parallel (thread-local rustc-session) test execution. Guards against a future refactor
    /// that recomputes origins per-kind / per-fn / per-query (which would push the delta above 1).
    #[test]
    fn origins_runs_once_per_program() {
        use crate::analyses::borrow_ownership::origin_flow::ORIGIN_DERIVATION_COUNT;
        ::utils::compilation::run_compiler_on_str(
            "unsafe fn id(p: *mut i32) -> *mut i32 { p }\n\
             unsafe fn f(p: *mut i32) -> *mut i32 { id(p) }",
            |tcx| {
                let before = ORIGIN_DERIVATION_COUNT.with(|c| c.get());
                let _row = run_bo(tcx, Duration::ZERO);
                let delta = ORIGIN_DERIVATION_COUNT.with(|c| c.get()) - before;
                assert_eq!(
                    delta, 1,
                    "compute_origins must run exactly once per program on the analysis path \
                     (kind-independent); the driver made {delta} calls"
                );
            },
        )
        .unwrap_or_else(|e| e.raise());
    }
}

/// Shared C2Rust delete-node fixture (was defined among the retired mirror tests; several surviving
/// NB-F / leak tests below use it).
#[cfg(test)]
const DELETE_NODE_WITNESS: &str = r#"
unsafe extern "C" {
    fn free(ptr: *mut core::ffi::c_void);
}

#[derive(Copy, Clone)]
#[repr(C)]
pub struct node {
    pub key: i32,
    pub left: *mut node,
    pub right: *mut node,
}

pub unsafe fn delete_node(mut root: *mut node, mut key: i32) -> *mut node {
    if root.is_null() {
        return root;
    }
    if key < (*root).key {
        (*root).left = delete_node((*root).left, key);
    } else if key > (*root).key {
        (*root).right = delete_node((*root).right, key);
    } else {
        if ((*root).left).is_null() {
            let mut temp: *mut node = (*root).right;
            free(root as *mut core::ffi::c_void);
            return temp;
        } else if ((*root).right).is_null() {
            let mut temp_0: *mut node = (*root).left;
            free(root as *mut core::ffi::c_void);
            return temp_0;
        }
        let mut temp_1: *mut node = (*root).right;
        (*root).key = (*temp_1).key;
        (*root).right = delete_node((*root).right, (*temp_1).key);
    }
    return root;
}
"#;

// ---------------------------------------------------------------------------
// §NB5-M wrapper-thinness guard (replaces the retired mirror-fidelity tests).
// ---------------------------------------------------------------------------

/// §NB5-M: guards WRAPPER-THINNESS. `verify_to_fixpoint` is a model-only wrapper over
/// `verify_to_fixpoint_counting` (the single CEGAR loop). This is a near-tautology today — the
/// wrapper literally returns `verify_to_fixpoint_counting(..).0` — and that is exactly its purpose:
/// if anyone later adds logic to the wrapper (a filter, retry, or a different solve), the sweep's
/// NATIVE counters would silently diverge from the model the suite verifies through the wrapper (the
/// mirror-drift the retired `boc1_mirror_matches_real_*` tests guarded). It runs an accept-no-commit
/// and an accept-with-commit shape so the loop is exercised; decline yields the same wrapper==native
/// by construction (both are the same loop).
#[test]
fn verify_to_fixpoint_is_thin_wrapper() {
    use crate::analyses::borrow_ownership::{
        CrateCtxt,
        borrow_verify::{verify_to_fixpoint, verify_to_fixpoint_counting},
        coherence::add_coherence,
        crate_slots::CrateSlots,
        emit_crate_ownership_constraints,
        origins::compute_origins,
        solver::KindSolver,
    };
    let shapes = [
        // accept, no commit (rounds == 1).
        "unsafe fn f(p: *mut i32) -> *mut i32 { let q = p; q }",
        // accept with a commit (coherence drags the modeled-origin param to Raw).
        "unsafe extern \"C\" { fn op(p: *mut i32) -> *mut i32; } \
         unsafe fn f(p: *mut i32) -> *mut i32 { let mut q = op(p); q = p; q }",
    ];
    for code in shapes {
        ::utils::compilation::run_compiler_on_str(code, |tcx| {
            let program = collect_program(tcx);
            let slots = CrateSlots::build(&program);
            let build = || {
                let crate_ctxt = CrateCtxt::new(&program);
                let solver = KindSolver::new(&slots);
                let (_s, selectors) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &solver,
                )
                .expect("emission");
                for &g in &program.functions {
                    let body = tcx.mir_drops_elaborated_and_const_checked(g).borrow();
                    add_coherence(&solver, &slots, g, &body);
                }
                (solver, selectors)
            };
            let (ws, wsel) = build();
            let wrapper = verify_to_fixpoint(&program, &slots, &ws, &wsel, true);
            let (ns, nsel) = build();
            let native = verify_to_fixpoint_counting(&program, &slots, &ns, &nsel, true).0;
            assert_eq!(
                wrapper, native,
                "§NB5-M: verify_to_fixpoint (wrapper) must equal verify_to_fixpoint_counting(..).0 — \
                 keep the wrapper thin"
            );
        })
        .unwrap_or_else(|e| e.raise());
    }
}

/// §NB5-M counter contract (Codex RE-4 fold): pins native `RoundStats` so a counter regression can
/// NOT pass the suite silently. The retired mirror-fidelity tests + the parity-window dual-compute
/// asserted these counters; the wrapper-thinness test guards only the model, so this is now the sole
/// counter guard. Covers accept-no-commit, accept-with-commit, sink-drop, and source-drop; the
/// decline paths (rounds carried on `None`) are structural (rounds only increments inside the loop)
/// and were checked in the NB5-M review (RE-3).
#[test]
fn nb5m_native_round_stats_contract() {
    use crate::analyses::borrow_ownership::{
        CrateCtxt,
        borrow_verify::{RoundStats, verify_to_fixpoint_counting},
        coherence::add_coherence,
        crate_slots::CrateSlots,
        emit_crate_ownership_constraints,
        origins::compute_origins,
        solver::KindSolver,
    };
    fn stats_of(code: &str) -> RoundStats {
        ::utils::compilation::run_compiler_on_str(code, |tcx| {
            let program = collect_program(tcx);
            let slots = CrateSlots::build(&program);
            let crate_ctxt = CrateCtxt::new(&program);
            let solver = KindSolver::new(&slots);
            let (_s, selectors) = emit_crate_ownership_constraints(
                &crate_ctxt,
                &slots,
                &compute_origins(&program),
                &solver,
            )
            .expect("emission");
            for &g in &program.functions {
                let body = tcx.mir_drops_elaborated_and_const_checked(g).borrow();
                add_coherence(&solver, &slots, g, &body);
            }
            verify_to_fixpoint_counting(&program, &slots, &solver, &selectors, true).1
        })
        .unwrap_or_else(|e| e.raise())
    }
    // (a) accept-first-model, no commit.
    let accept = stats_of("unsafe fn f(p: *mut i32) -> *mut i32 { let q = p; q }");
    assert_eq!(accept.rounds, 1, "accept: one round");
    assert_eq!(accept.commits_conflict, 0, "accept: no commits");
    assert_eq!(accept.commits_per_round, vec![0], "accept: [0]");
    assert_eq!(accept.dropped_sinks, 0, "accept: no sinks");
    assert_eq!(accept.dropped_sources, 0, "accept: no sources");
    // §NB5-F: an accept never carries a field-conflict decline. Under NB5-F2 the field-conflict
    // path now RESTORES (field loan disabled → accept with the field Raw; see
    // `nb5f2_field_conflict_restores`); `field_conflict_decline` stays reachable only as the backstop
    // for genuinely un-dischargeable field residuals.
    assert_eq!(
        accept.field_conflict_decline, None,
        "accept: no field-conflict decline"
    );
    // (b) accept WITH a conflict CASCADE: `x = id(p)` is a live Ref requirer invalidated by the write
    // through the base `b = p` (A′), committed `¬ref` over two commit rounds + the accepting round.
    let commit = stats_of(
        "unsafe fn id(p: *mut i32) -> *mut i32 { p } \
         unsafe fn f(p: *mut i32) -> i32 { let x = id(p); *x = 1; let b = p; *b = 2; *x }",
    );
    assert_eq!(
        commit.rounds, 3,
        "cascade: 2 commit rounds + accepting round"
    );
    assert_eq!(commit.commits_conflict, 2, "cascade: two commits");
    assert_eq!(
        commit.commits_per_round,
        vec![1, 1, 0],
        "cascade: one commit/round then accept"
    );
    assert_eq!(commit.dropped_sinks, 0);
    assert_eq!(commit.dropped_sources, 0);
    // (c) sink drop: the delete-node witness commits 3 conflicts, then the final solve leaks its two
    // free sinks. `dropped_sources == 0` here guards the `record_dropped` is_sink split (a regression
    // counting the 2 sinks as sources would make this 2). Genuine source-leak COUNTING
    // (`dropped_sources > 0`) is exercised across the corpus and was verified at the NB5-M parity gate.
    let sink = stats_of(DELETE_NODE_WITNESS);
    assert_eq!(sink.rounds, 2);
    assert_eq!(sink.commits_conflict, 3);
    assert_eq!(sink.commits_per_round, vec![3, 0]);
    assert_eq!(
        sink.dropped_sinks, 2,
        "delete-node leaks its two free sinks"
    );
    assert_eq!(
        sink.dropped_sources, 0,
        "the two dropped selectors are BOTH sinks (is_sink split)"
    );
    // (d) POSITIVE source drop (Codex RR-2): `&raw mut p` escapes the address of a malloc'd local,
    // so the alloc cannot be proven Owning; the eager `¬ref(source)` round-1 model surfaces one
    // conflict, committed into the accepting round-2 model, and the final solve DROPS the source
    // selector. This is the ONLY shape that pins `dropped_sources > 0` (the others pin it at 0).
    let source = stats_of(
        "unsafe extern \"C\" { fn malloc(size: usize) -> *mut core::ffi::c_void; } \
         pub unsafe fn leak() -> *mut *mut core::ffi::c_void { let mut p = malloc(8); &raw mut p }",
    );
    assert_eq!(
        source.rounds, 2,
        "source-drop: eager ¬ref round-1 + accepting round-2"
    );
    assert_eq!(source.commits_conflict, 1, "source-drop: one commit");
    assert_eq!(source.commits_per_round, vec![1, 0]);
    assert_eq!(source.dropped_sinks, 0, "no free in this shape");
    assert_eq!(
        source.dropped_sources, 1,
        "the leaked alloc drops its source selector (POSITIVE)"
    );
}

/// §NB5-F — field-universe expansion makes struct-field borrow conflicts visible to the BO
/// verifier (`owner_to_slot` no longer drops `Field` owners). Because the replay candidacy is
/// Local-only, a field requirer cannot be soundly demoted (its loan is not model-gated), so the
/// A′ principle extended to field requirers yields a DECLINE (Option A) rather than an unsound
/// discharge. This fixture is also the empirical test of the three-fact mechanism reading:
/// pre-partition it fails as the guard PANIC (`borrow_verify.rs` "every residual conflict slot
/// must be Ref"); post-partition it declines with the offending field tagged. Both shapes assert
/// the FINAL semantics: model `None` + `field_conflict_decline = Some(the field)`.
#[test]
fn nb5f2_field_conflict_restores() {
    use crate::analyses::borrow_ownership::{
        CrateCtxt, SlotKind,
        borrow_verify::verify_to_fixpoint_counting,
        coherence::add_coherence,
        crate_slots::CrateSlots,
        emit_crate_ownership_constraints,
        origins::compute_origins,
        slots::{SlotId, SlotOwner},
        solver::{KindSolver, SlotRef},
    };
    // §NB5-F2: run the BO verifier and report (accepted?, kinds of every depth-0 FIELD slot in the
    // accepted model, the tagged decline field if it declined). F2 extends the fork's demotion loop to
    // DISABLE a Raw field's loan (via the manifest-widened `disable_owner(Field)`) — so a field
    // conflict that F CB-declined now clears and ACCEPTS with the field `Raw`, exactly like a local.
    struct Outcome {
        accepted: bool,
        field_kinds: Vec<(String, SlotKind)>,
    }
    fn run(code: &str) -> Outcome {
        ::utils::compilation::run_compiler_on_str(code, |tcx| {
            let program = collect_program(tcx);
            let slots = CrateSlots::build(&program);
            let crate_ctxt = CrateCtxt::new(&program);
            let solver = KindSolver::new(&slots);
            let (_s, sel) = emit_crate_ownership_constraints(
                &crate_ctxt,
                &slots,
                &compute_origins(&program),
                &solver,
            )
            .expect("emission");
            for &g in &program.functions {
                let body = tcx.mir_drops_elaborated_and_const_checked(g).borrow();
                add_coherence(&solver, &slots, g, &body);
            }
            let field_name = |id: SlotId| match slots.field_slots.slot(id).owner {
                SlotOwner::Field(f) => {
                    format!(
                        "{}::field{}",
                        tcx.item_name(f.struct_did.to_def_id()),
                        f.field_index
                    )
                }
                SlotOwner::Local(_) => "LOCAL-owner(bug)".to_string(),
            };
            let (model, _stats) =
                verify_to_fixpoint_counting(&program, &slots, &solver, &sel, true);
            let mut field_kinds = Vec::new();
            if let Some(m) = &model {
                for (s, kind) in m {
                    if let SlotRef::Field(id) = s
                        && slots.field_slots.slot(*id).depth == 0
                    {
                        field_kinds.push((field_name(*id), *kind));
                    }
                }
            }
            Outcome {
                accepted: model.is_some(),
                field_kinds,
            }
        })
        .unwrap_or_else(|e| e.raise())
    }

    // (1) PURE field conflict (the F fixture, flipped): `h.p` borrows `x`, `x = 1` invalidates that
    // loan, `*h.p` uses it after. Under F this DECLINED (field requirer un-dischargeable); under F2 the
    // demotion loop disables `Holder::field0`'s loan → the conflict clears → ACCEPT with the field Raw.
    let o = run("struct Holder { p: *mut i32 } \
         unsafe fn f() { let mut x = 0i32; let mut h = Holder { p: core::ptr::null_mut() }; \
         h.p = &raw mut x; x = 1; *h.p = 2; }");
    assert!(
        o.accepted,
        "F2: pure field conflict must now ACCEPT (field loan disabled), not decline"
    );
    assert!(
        o.field_kinds
            .contains(&("Holder::field0".to_string(), SlotKind::Raw)),
        "F2: the restored field settles Raw (its loan was disabled); got {:?}",
        o.field_kinds
    );

    // (2) MIXED edge (local `v` + field `h.p` both alias `x`, both written after): under F2 the field
    // is disabled AND the local `v` demotes on its own path → ACCEPT with the field Raw.
    let o = run("struct Holder { p: *mut i32 } \
         unsafe fn f() { let mut x = 0i32; let mut h = Holder { p: core::ptr::null_mut() }; \
         let v = &raw mut x; h.p = &raw mut x; x = 1; *h.p = 2; *v = 3; }");
    assert!(
        o.accepted,
        "F2: mixed local+field conflict must now ACCEPT, not decline"
    );
    assert!(
        o.field_kinds
            .contains(&("Holder::field0".to_string(), SlotKind::Raw)),
        "F2: the restored field settles Raw; got {:?}",
        o.field_kinds
    );

    // (3) BACKSTOP TRIPWIRE (Codex NB5-F2 HIGH). The fix: F2 disables only EXACT-`Raw` fields, so an
    // `Owning` field is NEVER disabled — it falls through to the `residual_nonref_field` decline. A
    // POSITIVE owning-field-decline fixture is NOT constructible: an owning field is all-malloc-store
    // (no `&`-loan), so it cannot BE in a borrow conflict, and the solver prefers `Ref`/`Raw` over
    // `Owning` anyway (corpus-wide `s23_owning_model == 0`). So this is a defensive tripwire, not a
    // positive exercise (rider-3: don't synthesize). Codex's shape (a malloc'd pointer stored into
    // `H::p`, then aliased+written) DOES produce a field conflict; the field settles `Raw` and F2
    // restores it. The invariant we guard: **no accepted model of a field-conflict shape may carry an
    // `Owning` field** — that would be the unsound owning-field-aliased accept the exact-`Raw` guard
    // exists to prevent. Coverage of the owning branch rests on the exact-`Raw` predicate itself (cf.
    // the NB5-F Local-assert arm), not a synthesized case.
    let o = run(
        "unsafe extern \"C\" { fn malloc(n: usize) -> *mut core::ffi::c_void; } \
         struct H { p: *mut i32 } \
         unsafe fn f() { let mut h = H { p: core::ptr::null_mut() }; \
         let p = malloc(4) as *mut i32; h.p = p; *p = 1; let _ = *h.p; }",
    );
    assert!(
        !(o.accepted && o.field_kinds.iter().any(|(_, k)| *k == SlotKind::Owning)),
        "F2 BACKSTOP: an accepted field-conflict model must not carry an Owning field (exact-Raw \
         guard regressed → owning-field disable → unsound accept); got {:?}",
        o.field_kinds
    );
}

/// §S2-3 DIAGNOSTIC PROBE (NB5-F2 carried item 2; compute-only, no fixes). The corpus histogram shows
/// 155 owning-store field CANDIDATES but 0 field-`Owning` in-model, with `s23_blocked == 0` everywhere —
/// so the ⋀-law store-block (family (a)) is ruled out. This probe answers the remaining question on an
/// owning-CAPABLE field (malloc store + `free` sink, the corpus candidate pattern): is `own(field)`
/// **achievable** (SAT ⇒ the zero yield is a SOFT objective/retention blocker — `Ref ≻ Raw ≻ Owning` +
/// leak-minimal drops the source/sink rather than paying `Owning`), or **hard-blocked** (UNSAT ⇒ a
/// constraint family forbids it)? Reports the verdict; not a fix.
#[test]
#[ignore = "S2-3 diagnostic probe (compute-only); run explicitly"]
fn s23_owning_blocker_probe() {
    use z3::{SatResult, ast::Bool};

    use crate::analyses::borrow_ownership::{
        CrateCtxt,
        coherence::{add_coherence, constrain_field_ownership},
        crate_slots::CrateSlots,
        emit_crate_ownership_constraints,
        origins::compute_origins,
        slots::{SlotId, SlotOwner},
        solver::{KindSolver, SlotRef},
    };
    ::utils::compilation::run_compiler_on_str(
        "unsafe extern \"C\" { fn malloc(n: usize) -> *mut core::ffi::c_void; fn free(p: *mut core::ffi::c_void); } \
         struct H { p: *mut i32 } \
         unsafe fn f() { let mut h = H { p: core::ptr::null_mut() }; \
         h.p = malloc(4) as *mut i32; free(h.p as *mut core::ffi::c_void); }",
        |tcx| {
            let program = collect_program(tcx);
            let slots = CrateSlots::build(&program);
            let crate_ctxt = CrateCtxt::new(&program);
            // TRACKED solver so an UNSAT core maps to labeled constraint families (per `explain_unsat`).
            let solver = KindSolver::new_tracked(&slots);
            let (_s, selectors) = emit_crate_ownership_constraints(
                &crate_ctxt, &slots, &compute_origins(&program), &solver,
            ).expect("emission");
            let tracker = solver.tracker().expect("new_tracked");
            tracker.set_context("coherence");
            for &g in &program.functions {
                let body = tcx.mir_drops_elaborated_and_const_checked(g).borrow();
                add_coherence(&solver, &slots, g, &body);
            }
            tracker.set_context("field-law");
            constrain_field_ownership(&solver, &slots, &program);
            let field = (0..slots.field_slots.len())
                .map(SlotId::from_usize)
                .find(|&sid| {
                    slots.field_slots.slot(sid).depth == 0
                        && matches!(slots.field_slots.slot(sid).owner, SlotOwner::Field(_))
                })
                .map(SlotRef::Field)
                .expect("H::p depth-0 field slot");
            tracker.set_context("s23-force-own");
            solver.assert_owning(field);
            // Assume every track (⇔ the untracked hard system) + all source/sink selectors retained.
            let mut assumptions: Vec<Bool> = tracker.tracks();
            assumptions.extend(selectors.all().iter().cloned());
            match solver.optimize().check(&assumptions) {
                SatResult::Sat => eprintln!("S23_PROBE field={field:?} force_own=SAT (SOFT blocker: own achievable, objective/retention settles it lower)"),
                SatResult::Unknown => eprintln!("S23_PROBE field={field:?} force_own=UNKNOWN"),
                SatResult::Unsat => {
                    let core = solver.optimize().get_unsat_core();
                    let labels: Vec<String> = core.iter().map(|l| {
                        tracker.label_of(l).unwrap_or_else(|| {
                            if selectors.is_sink(l) { "sink-selector".to_string() }
                            else { "source-selector".to_string() }
                        })
                    }).collect();
                    eprintln!(
                        "S23_PROBE field={field:?} force_own=UNSAT (HARD blocker) core_labels={labels:?}"
                    );
                }
            }
        },
    )
    .unwrap_or_else(|e| e.raise());
}

/// §NB-F stage 1 (option (a), approved at the NB-R gate) — the CAUSAL flip:
/// with `free`/`realloc` sink owning selector-gated, the deleteNode witness
/// must ACCEPT under the REAL `verify_to_fixpoint` — the relax loop drops the
/// two free-sink selectors (leak-the-frees: an unprovable free stays a raw
/// free) and, with no malloc in the shape, nothing else forces owning.
/// Deliberately NO assertion on the freed values' final kinds: dropping a sink
/// selector removes forced owning but asserts neither ¬own nor ¬ref (there is
/// no sink analogue of NB0's eager ¬ref(source), by design) — the observed
/// final kind is recorded in the task doc, not pinned here.
#[test]
fn nbf_sink_retractable_delete_node() {
    use crate::analyses::borrow_ownership::{
        CrateCtxt, borrow_verify::verify_to_fixpoint, coherence::add_coherence,
        crate_slots::CrateSlots, emit_crate_ownership_constraints, solver::KindSolver,
    };

    ::utils::compilation::run_compiler_on_str(DELETE_NODE_WITNESS, |tcx| {
        let program = collect_program(tcx);
        let slots = CrateSlots::build(&program);
        let crate_ctxt = CrateCtxt::new(&program);
        let solver = KindSolver::new(&slots);
        let (_s, selectors) = emit_crate_ownership_constraints(
            &crate_ctxt,
            &slots,
            &crate::analyses::borrow_ownership::origins::compute_origins(&program),
            &solver,
        )
        .expect("emission");
        for &g in &program.functions {
            let body = tcx.mir_drops_elaborated_and_const_checked(g).borrow();
            add_coherence(&solver, &slots, g, &body);
        }
        let model = verify_to_fixpoint(&program, &slots, &solver, &selectors, true);
        assert!(
            model.is_some(),
            "retractable sinks: the witness must ACCEPT (its only forced owning \
             was the free sink, now selector-dropped)"
        );
    })
    .unwrap_or_else(|e| e.raise());
}

// ---------------------------------------------------------------------------
// §NB-R — tracked-core explain driver (diagnosis only; no analysis change).
// ---------------------------------------------------------------------------

/// Explains why the BO system is infeasible on a crate, using a TRACKED
/// `KindSolver` (`new_tracked`): every hard constraint is `track ⇒ c`, the
/// solve is `check(&[tracks ∪ source selectors])`, and on UNSAT the core's
/// track literals map back to labeled emission sites.
mod explain {
    use rustc_middle::ty::TyCtxt;
    use z3::{SatResult, ast::Bool};

    use super::collect_program;
    use crate::analyses::borrow_ownership::{
        CrateCtxt,
        coherence::{add_coherence, constrain_field_ownership},
        crate_slots::CrateSlots,
        emit_crate_ownership_constraints,
        solver::{CORE_LABEL_FAMILIES, KindSolver},
    };

    pub enum Explained {
        Sat,
        Unknown,
        Unsat {
            /// Labeled core (`{context}::{family}(…)` strings). When
            /// `minimized`, this set has been drop-restore minimized AND
            /// re-checked UNSAT on its own (a raw z3 core is not minimal;
            /// an unverified "minimal" core would poison the diagnosis).
            core: Vec<String>,
            /// False only when the size cap was hit (histogram-scale core);
            /// the labels are then the RAW core.
            minimized: bool,
        },
    }

    /// Cap above which minimization is skipped (brotli-scale safety) and the
    /// raw core is returned for histogram use only.
    pub const MINIMIZE_CAP: usize = 50;

    /// NB-R's existing destructive drop-restore minimizer, shared by the
    /// selector-core reconstruction. The boolean is true only for a
    /// rechecked, 1-minimal core; oversized and Unknown-tainted cores remain
    /// honest raw-core evidence.
    pub(super) fn minimize_core(solver: &KindSolver, mut core: Vec<Bool>) -> (Vec<Bool>, bool) {
        if core.len() > MINIMIZE_CAP {
            return (core, false);
        }
        let mut saw_unknown = false;
        let mut index = 0;
        while index < core.len() {
            let mut candidate = core.clone();
            candidate.swap_remove(index);
            match solver.optimize().check(&candidate) {
                SatResult::Unsat => {
                    core = candidate;
                }
                SatResult::Sat => index += 1,
                SatResult::Unknown => {
                    saw_unknown = true;
                    index += 1;
                }
            }
        }
        assert_eq!(
            solver.optimize().check(&core),
            SatResult::Unsat,
            "minimized core must re-check UNSAT on its own"
        );
        (core, !saw_unknown)
    }

    /// Build the full tracked BO system over the crate (emission + coherence +
    /// the §9.10.2 field law — exactly what the real pipeline has asserted by
    /// the time of its FIRST solve inside `verify_to_fixpoint`, which is where
    /// every round-0 corpus decline happens) and explain that first solve.
    pub fn explain_unsat(tcx: TyCtxt<'_>) -> Explained {
        let program = collect_program(tcx);
        let slots = CrateSlots::build(&program);
        let crate_ctxt = CrateCtxt::new(&program);
        let solver = KindSolver::new_tracked(&slots);
        let (_stats, selectors) = emit_crate_ownership_constraints(
            &crate_ctxt,
            &slots,
            &crate::analyses::borrow_ownership::origins::compute_origins(&program),
            &solver,
        )
        .expect("NB-R: tracked emission");
        let tracker = solver.tracker().expect("new_tracked");
        tracker.set_context("coherence");
        for &g in &program.functions {
            let body = tcx.mir_drops_elaborated_and_const_checked(g).borrow();
            add_coherence(&solver, &slots, g, &body);
        }
        tracker.set_context("field-law");
        constrain_field_ownership(&solver, &slots, &program);

        // Solve with EVERY track assumed (⇔ the untracked hard system) plus
        // the source selectors (the hard-source reading, as in the real
        // pipeline's first solve).
        let tracks = tracker.tracks();
        let mut assumptions: Vec<Bool> = tracks;
        assumptions.extend(selectors.all().iter().cloned());
        match solver.optimize().check(&assumptions) {
            SatResult::Sat => Explained::Sat,
            SatResult::Unknown => Explained::Unknown,
            SatResult::Unsat => {
                let (core, minimized) = minimize_core(&solver, solver.optimize().get_unsat_core());
                let labels = core
                    .iter()
                    .map(|literal| {
                        tracker.label_of(literal).unwrap_or_else(|| {
                            // Non-track core literals are selectors; §NB-F
                            // splits them by identity so a leaked-free MUS
                            // reads differently from a leaked-alloc MUS.
                            if selectors.is_sink(literal) {
                                "sink-selector".to_string()
                            } else {
                                "source-selector".to_string()
                            }
                        })
                    })
                    .collect();
                Explained::Unsat {
                    core: labels,
                    minimized,
                }
            }
        }
    }

    /// The family a label belongs to, if any (the parse contract: every label
    /// the tracker emits must contain exactly one known family tag).
    pub fn family_of(label: &str) -> Option<&'static str> {
        CORE_LABEL_FAMILIES
            .iter()
            .copied()
            .find(|family| label.contains(family))
    }

    /// KV-safe family histogram of a labeled core: `fam:count/fam:count`,
    /// ordered by count desc then name asc (deterministic).
    pub fn family_histogram(core: &[String]) -> String {
        let mut counts: Vec<(&'static str, usize)> = Vec::new();
        for label in core {
            let family = family_of(label).unwrap_or("unknown");
            match counts.iter_mut().find(|(f, _)| *f == family) {
                Some((_, n)) => *n += 1,
                None => counts.push((family, 1)),
            }
        }
        counts.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(b.0)));
        counts
            .iter()
            .map(|(f, n)| format!("{f}:{n}"))
            .collect::<Vec<_>>()
            .join("/")
    }
}

/// §NB-R histogram format contract (pure; mechanism-only).
#[test]
fn nbr_family_histogram_format() {
    let labels: Vec<String> = vec![
        "f::own-assume(1=true)".into(),
        "g::kind-equate(x,y,own)".into(),
        "f::own-assume(2=false)".into(),
        "weird label".into(),
    ];
    assert_eq!(
        explain::family_histogram(&labels),
        "own-assume:2/kind-equate:1/unknown:1"
    );
}

/// §NB-R MECHANISM-ONLY guard on the explain driver (deliberately no
/// family-content assertions: which families appear in the witness core is
/// R2a's FINDING, recorded in the task doc — baking the pre-registered
/// hypothesis into CI would turn the most interesting outcome into a red
/// build. After R2a confirms the diagnosis, a SEPARATE regression fixture
/// pins it).
#[test]
fn nbr_core_extraction_delete_node() {
    ::utils::compilation::run_compiler_on_str(DELETE_NODE_WITNESS, |tcx| {
        match explain::explain_unsat(tcx) {
            explain::Explained::Unsat { core, minimized } => {
                assert!(
                    !core.is_empty(),
                    "an UNSAT explanation must name constraints"
                );
                assert!(
                    minimized,
                    "the witness-scale core must go through drop-restore minimization \
                     (with its UNSAT re-check)"
                );
                for label in &core {
                    assert!(
                        explain::family_of(label).is_some(),
                        "core label does not parse to a known family: {label}"
                    );
                }
            }
            _ => panic!("the deleteNode witness must be UNSAT under tracks ∪ selectors"),
        }
    })
    .unwrap_or_else(|e| e.raise());
}

/// §NB-R R2a REGRESSION fixture (frozen AFTER the diagnosis was confirmed —
/// deliberately separate from the mechanism-only test above). Pins the
/// verified family composition of the witness's minimal core: the free
/// sink's owning — since §NB-F a RETRACTABLE `sink-selector` literal, no
/// longer a hard `own-assume(=true)` — reaches a never-owning temp's
/// version-zero (`own-assume(=false)`, still the sole hard pole) through
/// kind-coherence over the `node.right` field slot and both `link-own`
/// biconditionals. Explain assumes ALL selectors, so the core is still UNSAT
/// (master lemma) even though the production relax path now accepts this
/// witness by dropping the sinks. If an emission change alters this
/// contradiction surface, this fails loudly and the diagnosis in
/// docs/agents/tasks/2026-07-04-nbr-unsat-root-cause.md must be re-derived.
/// (Family HISTOGRAM only — var indices shift with MIR details and are
/// deliberately not pinned.)
#[test]
fn nbr_witness_core_family_regression() {
    ::utils::compilation::run_compiler_on_str(DELETE_NODE_WITNESS, |tcx| {
        let explain::Explained::Unsat { core, minimized } = explain::explain_unsat(tcx) else {
            panic!("witness must be UNSAT");
        };
        assert!(minimized);
        eprintln!(
            "NBFOBS regression histogram: {}",
            explain::family_histogram(&core)
        );
        assert_eq!(
            explain::family_histogram(&core),
            "kind-equate:4/link-own:2/own-equal:2/own-assume:1/own-linear:1/sink-selector:1",
            "the witness diagnosis changed — re-derive the root-cause analysis"
        );
        let trues = core
            .iter()
            .filter(|l| l.contains("own-assume") && l.ends_with("=true)"))
            .count();
        let falses = core
            .iter()
            .filter(|l| l.contains("own-assume") && l.ends_with("=false)"))
            .count();
        // §NB-F re-derivation: the sink-owning pole is now the retractable
        // `sink-selector` literal (asserted in the histogram above), so the
        // remaining hard own-assume is the version-zero alone.
        assert_eq!(
            (trues, falses),
            (0, 1),
            "the version-zero remains the hard pole; the sink pole is the sink-selector"
        );
    })
    .unwrap_or_else(|e| e.raise());
}

/// §NB-R R2a — manual core printer for the deleteNode witness. `#[ignore]`d:
/// run explicitly to (re)produce the diagnosis recorded in the task doc.
#[test]
#[ignore = "NB-R diagnosis printer: run with --exact bo_c1::nbr_print_witness_core --ignored --nocapture"]
fn nbr_print_witness_core() {
    ::utils::compilation::run_compiler_on_str(DELETE_NODE_WITNESS, |tcx| {
        match explain::explain_unsat(tcx) {
            explain::Explained::Unsat { core, minimized } => {
                eprintln!(
                    "NBRCORE witness delete_node: {} literals (minimized={minimized})",
                    core.len()
                );
                let mut sorted = core.clone();
                sorted.sort();
                for label in &sorted {
                    eprintln!("NBRCORE   {label}");
                }
            }
            explain::Explained::Sat => eprintln!("NBRCORE witness: SAT?!"),
            explain::Explained::Unknown => eprintln!("NBRCORE witness: UNKNOWN"),
        }
    })
    .unwrap_or_else(|e| e.raise());
}

/// §NB-R tracked-instance guard: a tracked solver reaching a production solve
/// path is a hard error, not a silently-vacuous solve.
#[test]
#[should_panic(expected = "tracked KindSolver must not enter model_kinds_relaxing")]
fn nbr_tracked_solver_guard_panics() {
    use crate::analyses::borrow_ownership::{crate_slots::CrateSlots, solver::KindSolver};

    ::utils::compilation::run_compiler_on_str("pub unsafe fn f(p: *mut i32) { *p = 1; }", |tcx| {
        let program = collect_program(tcx);
        let slots = CrateSlots::build(&program);
        let solver = KindSolver::new_tracked(&slots);
        let _ = solver.model_kinds_relaxing(
            &crate::analyses::borrow_ownership::solver::Selectors::new(Vec::new(), Vec::new()),
        );
    })
    .unwrap_or_else(|e| e.raise());
}

// ---------------------------------------------------------------------------
// ---------------------------------------------------------------------------
// S2a-H — the ASSERTING corpus driver (Track 1, T1.2)
// ---------------------------------------------------------------------------

/// SHA-256 of a file via `shasum`, the tool that already guards the
/// frozen-corpus digest. Driver-side on purpose: a crypto dependency added for
/// one provenance stamp would be disproportionate.
#[cfg(test)]
fn shasum_of(path: &std::path::Path) -> String {
    let out = std::process::Command::new("shasum")
        .args(["-a", "256"])
        .arg(path)
        .output()
        .unwrap_or_else(|e| panic!("shasum not runnable for {path:?}: {e}"));
    assert!(out.status.success(), "shasum failed on {path:?}");
    String::from_utf8_lossy(&out.stdout)
        .split_whitespace()
        .next()
        .unwrap_or("")
        .to_owned()
}

/// **The yield label, verbatim.** Every aggregate this path reports carries it.
///
/// It is not decoration. `CallSiteNotAdapted` saturates the degraded side
/// pre-S3, so the emitted/degraded split measures S3's absence rather than M1's
/// ceiling, and a bare ratio lifted out of a table reads as the latter. Only the
/// M1-final report after S3 feeds the emission-guided-refinement decision.
#[cfg(test)]
const PRE_S3_LABEL: &str = "pre-S3 — measures S3's absence.";

/// Outcome counters over producer A's **decoded artifact rows**.
///
/// # Why the decoded rows and not the in-memory table
///
/// The same reason `run_m1_recon`'s verdict is computed from the files: an
/// encoder defect that never reaches a reader is a defect no number can see.
/// Counting the bytes the driver already digests into `a_sha256` gives one
/// stamp covering both the compared and the counted artifact — provenance for
/// the yield figures comes free rather than as a parallel derivation that could
/// drift from what was compared.
#[cfg(test)]
#[derive(Debug, Default, Clone, PartialEq, Eq)]
struct OutcomeCounts {
    rows: usize,
    ref_mut: usize,
    ref_shared: usize,
    degraded: usize,
    /// Rows carrying **no** outcome. Producer A sets one on every row it emits,
    /// so this is a schema violation rather than a category — recorded, never
    /// folded into `degraded`, which is how a decoding regression would present
    /// as a plausible yield shift instead of a failure.
    unclassified: usize,
    /// Degradation reasons by key. The distribution is the point: a single
    /// `degraded` total cannot show that one reason saturates it.
    by_reason: std::collections::BTreeMap<String, usize>,
}

#[cfg(test)]
impl OutcomeCounts {
    fn merge(&mut self, other: &Self) {
        self.rows += other.rows;
        self.ref_mut += other.ref_mut;
        self.ref_shared += other.ref_shared;
        self.degraded += other.degraded;
        self.unclassified += other.unclassified;
        for (reason, n) in &other.by_reason {
            *self.by_reason.entry(reason.clone()).or_default() += n;
        }
    }

    /// `ref_mut + ref_shared` — the `Ref`-DECIDED count, **in the artifact's frame**.
    ///
    /// # This is NOT `m1_emit_corpus`'s `emitted`, and the gap is exact
    ///
    /// The artifact is a **pre-revert decision snapshot**: `artifact_rows` runs
    /// off `decide_table`, which never sees the verify loop. `emitted` is
    /// **post-revert**. A subject the loop took back is `Ref` here and a
    /// `RevertedAfterVerifyFailure` degradation there, so
    ///
    /// ```text
    ///   decided_ref    = emitted   + reverted
    ///   degraded(here) = degraded(emit) - reverted
    /// ```
    ///
    /// and both frames sum to the same row count. Measured 2026-08-04 at
    /// `5bbde5ab`: **818 = 771 + 47**, holding on **every one of the 20
    /// programs**, not merely in aggregate.
    ///
    /// # Why the printed key says `decided_ref` and not `converted`
    ///
    /// The two figures get read side by side, and `converted 818` beside
    /// `emitted 771` reads as a discrepancy in one of them. It is neither: it is
    /// the revert loop, which is the entire subject of S2b.1. A note on this
    /// accessor cannot defend the misread, because the misread happens at the
    /// printed line — so the NAME carries the frame. The wire schema's field is
    /// untouched; this is the report's vocabulary, not the artifact's.
    fn decided_ref(&self) -> usize {
        self.ref_mut + self.ref_shared
    }
}

/// Count decoded rows by outcome.
///
/// **Exhaustive, with no `_` arm.** When S3 adds a `Box` disposition to
/// `Outcome`, this fails to compile rather than silently counting the new
/// variant as nothing — the same rule the artifact's construction site carries,
/// applied to the consumer, because totality that holds only on the way in is
/// half a guarantee.
#[cfg(test)]
fn count_outcomes(rows: &[crate::coverage_recon::schema::Row]) -> OutcomeCounts {
    use crate::coverage_recon::schema::Outcome;

    let mut c = OutcomeCounts { rows: rows.len(), ..OutcomeCounts::default() };
    for row in rows {
        match row.outcome {
            Some(Outcome::RefMut) => c.ref_mut += 1,
            Some(Outcome::RefShared) => c.ref_shared += 1,
            Some(Outcome::Degraded) => {
                c.degraded += 1;
                // A degraded row with no reason is counted under an explicit
                // key, not dropped: an unattributed degradation must be visible
                // in the distribution it distorts.
                let reason = row.degrade_reason.clone().unwrap_or_else(|| "<none>".to_owned());
                *c.by_reason.entry(reason).or_default() += 1;
            }
            None => c.unclassified += 1,
        }
    }
    c
}

/// One reported line, label attached.
///
/// Rendering is a function so the label can be *witnessed* rather than trusted
/// to a `println!` nobody asserts on.
#[cfg(test)]
fn count_line(scope: &str, c: &OutcomeCounts) -> String {
    format!(
        "M1COUNT {scope} rows={} decided_ref={} ref_mut={} ref_shared={} \
         degraded={} unclassified={} label={PRE_S3_LABEL:?}",
        c.rows,
        c.decided_ref(),
        c.ref_mut,
        c.ref_shared,
        c.degraded,
        c.unclassified,
    )
}

/// A row field that must read `0`, **fail-closed on absence**.
///
/// Missing and unparseable are failures, not zeros: an expected-zero check that
/// reads a missing key as satisfied passes hardest exactly when the instrument
/// has stopped reporting.
#[cfg(test)]
fn expected_zero_field(row: &report::Row, key: &str) -> Result<(), String> {
    let raw = row
        .get(key)
        .ok_or_else(|| format!("{key}=missing (expected 0)"))?;
    let n: usize = raw
        .parse()
        .map_err(|_| format!("{key}={raw:?} (unparseable; expected 0)"))?;
    if n == 0 {
        Ok(())
    } else {
        Err(format!("{key}={n} (expected 0)"))
    }
}

/// The finding-class aggregates — the same check over a derived key.
///
/// Delegated rather than reimplemented: two zero-checks are two places for the
/// fail-closed behaviour to drift apart, and this is a canonicalizer, not a
/// reconciliation. The rule of record says those are single.
#[cfg(test)]
fn expected_zero_aggregate(row: &report::Row, class: &str) -> Result<(), String> {
    expected_zero_field(row, &format!("agg_{}", class.replace('-', "_")))
}

/// **Ruling F — the per-program expected-N table for non-evaluable LOCALS.**
///
/// Parameters keep expected-ZERO (`expected_zero_aggregate`, Track 2's
/// calibration, untouched). Locals cannot: 2628 of 3142 corpus locals are
/// unannotated C2Rust bindings with no declared type, so producer A has no
/// splice target to offer and the evaluable conjunction cannot be satisfied.
///
/// **A fixed table rather than "nonzero is fine", because it catches BOTH
/// regression directions.** A DROP means spans appeared where none should exist
/// — annotation synthesis, or a producer emitting a non-splice-target. A RISE
/// means annotation detection broke and real declarations stopped resolving.
/// "Some number ≥ 0" would catch neither.
///
/// Measured by the E′ probe at code `75a2d8fe` (2026-08-05, digest
/// `9fc912af…0e621`), and cross-checked against an independent offline analyzer
/// that agreed exactly. **Values change only by ruling, and only re-measured.**
#[cfg(test)]
const EXPECTED_NOT_EVALUABLE_LOCAL: &[(&str, u64)] = &[
    ("avl", 16),
    ("binn", 132),
    ("brotli", 800),
    ("bst", 12),
    ("buffer", 40),
    ("bzip2", 15),
    ("genann", 61),
    ("heman", 378),
    ("ht", 12),
    ("json.h", 228),
    ("libcsv", 25),
    ("libtree", 59),
    ("libzahl", 67),
    ("lil", 303),
    ("lodepng", 248),
    ("quadtree", 40),
    ("rgba", 7),
    ("robotfindskitten", 1),
    ("tulipindicators", 115),
    ("urlparser", 69),
];

/// The locals aggregate against its per-program expectation.
///
/// Fail-closed on a missing program exactly as the zero-pin is on a missing
/// field: an unpinned program is a hole in the table, not a pass.
#[cfg(test)]
fn expected_not_evaluable_local(row: &report::Row, program: &str) -> Result<(), String> {
    let key = "agg_span_check_not_evaluable_local";
    let want = EXPECTED_NOT_EVALUABLE_LOCAL
        .iter()
        .find(|(name, _)| *name == program)
        .map(|(_, n)| *n)
        .ok_or_else(|| format!("{program}: absent from EXPECTED_NOT_EVALUABLE_LOCAL"))?;
    let raw = row
        .get(key)
        .ok_or_else(|| format!("{key}=missing (expected {want})"))?;
    let got: u64 = raw
        .parse()
        .map_err(|_| format!("{key}={raw:?} (unparseable; expected {want})"))?;
    if got == want {
        Ok(())
    } else {
        Err(format!(
            "{key}={got} (expected {want}) — a DROP means spans appeared where \
             no declaration exists; a RISE means annotation detection broke"
        ))
    }
}

#[test]
fn the_local_not_evaluable_pin_is_fail_closed() {
    let mut row = report::Row::default();
    // Missing field.
    assert!(
        expected_not_evaluable_local(&row, "bst")
            .expect_err("a missing aggregate must fail")
            .contains("missing"),
    );
    // Unpinned program.
    row.set("agg_span_check_not_evaluable_local", "12");
    assert!(
        expected_not_evaluable_local(&row, "not-a-program")
            .expect_err("an unpinned program must fail")
            .contains("absent from"),
    );
    // Exact match passes; either direction fails.
    assert!(expected_not_evaluable_local(&row, "bst").is_ok());
    row.set("agg_span_check_not_evaluable_local", "11");
    assert!(expected_not_evaluable_local(&row, "bst").is_err(), "a DROP must fail");
    row.set("agg_span_check_not_evaluable_local", "13");
    assert!(expected_not_evaluable_local(&row, "bst").is_err(), "a RISE must fail");
}

#[test]
fn a_missing_aggregate_fails_closed() {
    let row = report::Row::default();
    let err = expected_zero_aggregate(&row, "out-of-coverage")
        .expect_err("a missing expected-zero aggregate must fail");
    assert!(err.contains("missing"), "wrong failure: {err}");
}

#[test]
fn an_unparseable_aggregate_fails_closed() {
    let mut row = report::Row::default();
    row.set("agg_out_of_coverage", "not-a-number");
    let err = expected_zero_aggregate(&row, "out-of-coverage")
        .expect_err("an unparseable expected-zero aggregate must fail");
    assert!(err.contains("unparseable"), "wrong failure: {err}");
}

/// **S2b.3 Item 4 — `run_m1_emit` GRADUATES out of the ignored-only class.**
///
/// The instrument's only in-suite consumer was `#[ignore]`d, so `cargo test`
/// could not see it — the enabling condition behind both S2b.2-era instrument
/// failures, and the reason the class register exists. This is the fixture-scale
/// smoke that ends it for this member.
///
/// # Measured, not assumed: what this closes
///
/// Reverting `run_m1_emit`'s `unplaceable` read to the old `0usize` constant
/// **survived the entire suite** when Item 0 landed — 1062/6/25 either way. The
/// outcome-level witnesses cover the data path up to the instrument's read; this
/// covers the read.
///
/// The MACRO fixture rather than a clean one, deliberately. A clean crate has
/// `unplaceable == 0`, so a constant-zero mutation of the reporting line is
/// indistinguishable from the truth, and the smoke would pin nothing. This
/// fixture reports `unplaceable = 1` **and** `emitted = 0`, so one row
/// discriminates both S2b.3 counters at the instrument layer.
///
/// # Residual, registered rather than forced
///
/// The **FAIL arm's** read stays uncovered. Discriminating it needs a crate that
/// compiles, carries an unplaceable subject, AND fails the gate irrecoverably;
/// the revert loop recovers every fixture-scale breakage, and forcing escalation
/// needs a round cap `run_m1_emit` does not expose. A non-compiling crate
/// reaches the arm but through `OutcomeFacts::default()`, whose count is
/// genuinely zero — it exercises the line without discriminating it. Per the
/// self-limiting clause this is registered, not manufactured.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** delete the
/// `row.set("unplaceable", ..)` from the Emitted arm — the key goes missing and
/// this fails. Second, the faithful one: write `0usize` there, the exact
/// pre-S2b.3 defect, and this fails 0 vs 1. Third, for the `emitted`
/// assertion: delete the `unplaceable_subjects.contains(..)` skip in
/// `rewrite_core_injected` and this fails 1 vs 0.
///
/// Putting the decision count back at the tuple site **survives** this test,
/// and correctly so: the fixture takes the emitting path, where
/// `facts.emitted_count` is overwritten by the already-filtered `kept.len()`.
/// That site reaches a consumer only on a `Degraded` return, which is why it has
/// its own witness in `a_degraded_outcome_reports_placements_too` rather than
/// being claimed here.
#[test]
fn run_m1_emit_reports_its_counters_at_fixture_scale() {
    let dir = std::env::temp_dir().join(format!("crat-m1emit-smoke-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("smoke fixture dir");
    std::fs::write(
        dir.join("lib.rs"),
        "#![allow(dead_code, unused_unsafe)]\nmacro_rules! mk {\n    () => {\n        pub unsafe fn mac_bump(p: *mut i32) -> i32 {\n            *p += 1;\n            *p\n        }\n    };\n}\nmk!();\n",
    )
    .expect("smoke fixture source");

    let row = run::run_m1_emit(&dir.join("lib.rs"));
    let _ = std::fs::remove_dir_all(&dir);

    assert_eq!(row.get("status"), Some("ok"), "row: {row:?}");
    assert_eq!(row.get("verdict"), Some("PASS"), "row: {row:?}");
    assert_eq!(
        row.get("unplaceable"),
        Some("1"),
        "the instrument did not report the plan's unplaceable decision: {row:?}"
    );
    assert_eq!(
        row.get("emitted"),
        Some("0"),
        "the instrument counted a decision that placed no edit: {row:?}"
    );
    // The pin's own checker, over a real instrument row rather than a
    // hand-built one — a nonzero here is what the corpus sweep now fails on.
    assert!(
        expected_zero_field(&row, "unplaceable").is_err(),
        "the pin accepted a row carrying an unplaceable decision"
    );
}

/// A producer-A-shaped row, for the counter witnesses.
#[cfg(test)]
fn counted_row(
    local: u32,
    outcome: crate::coverage_recon::schema::Outcome,
    reason: Option<&str>,
) -> crate::coverage_recon::schema::Row {
    use crate::coverage_recon::schema::{DeclShape, PairingConfidence, Row};
    Row {
        fn_path: format!("k::f{local}"),
        mir_local: local,
        param_name: Some("p".to_owned()),
        arg_index: Some(1),
        ptr_depth: 1,
        pairing_confidence: PairingConfidence::High,
        decl_span: Some("<t>:1:1".to_owned()),
        decl_span_lo: Some(0),
        decl_span_hi: Some(1),
        binding_span_lo: None,
        binding_span_hi: None,
        decl_shape: Some(DeclShape::RawPtr),
        outcome: Some(outcome),
        degrade_reason: reason.map(str::to_owned),
    }
}

/// **S2b.3 Item 2 — the counters bucket DECODED rows.**
///
/// Encoded and decoded first, deliberately: the corpus path counts bytes read
/// back from disk, so a witness over in-memory rows would pass on a shape the
/// real path never sees. This is the same reason `run_m1_recon`'s verdict is
/// computed from the files.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** delete the
/// `Some(Outcome::RefShared)` arm — the match is exhaustive with no `_`, so the
/// BUILD fails. That is the totality property, and it is the arm S3 will add a
/// sibling to. The faithful behavioural mutation follows: fold `RefShared` into
/// `ref_mut` and this fails on both bucket counts.
#[test]
fn counters_bucket_decoded_rows_by_outcome() {
    use crate::coverage_recon::schema::{self, Outcome};

    let rows = vec![
        counted_row(1, Outcome::RefMut, None),
        counted_row(2, Outcome::RefShared, None),
        counted_row(3, Outcome::Degraded, Some("call-site-not-adapted")),
        counted_row(4, Outcome::Degraded, Some("call-site-not-adapted")),
        counted_row(5, Outcome::Degraded, Some("kind-raw")),
    ];
    let decoded = schema::decode(&schema::encode(&rows)).expect("round-trips");
    assert_eq!(decoded.len(), rows.len(), "the wire lost a row");

    let c = count_outcomes(&decoded);
    assert_eq!(
        (c.rows, c.ref_mut, c.ref_shared, c.degraded, c.unclassified),
        (5, 1, 1, 3, 0)
    );
    assert_eq!(c.decided_ref(), 2, "decided_ref is ref_mut + ref_shared");
    assert_eq!(c.by_reason.get("call-site-not-adapted"), Some(&2));
    assert_eq!(c.by_reason.get("kind-raw"), Some(&1));
    assert_eq!(
        c.by_reason.values().sum::<usize>(),
        c.degraded,
        "the reason distribution must account for every degraded row, or the \
         saturation figure is computed over a subset"
    );

    // Merging is what produces the corpus total.
    let mut total = OutcomeCounts::default();
    total.merge(&c);
    total.merge(&c);
    assert_eq!((total.rows, total.degraded), (10, 6));
    assert_eq!(total.by_reason.get("call-site-not-adapted"), Some(&4));
}

/// **S2b.3 Item 2 — a row with NO outcome is `unclassified`, never `degraded`.**
///
/// Producer A writes an outcome on every row, so this shape means the schema or
/// the decoder moved. Folding it into `degraded` would render a decoding
/// regression as a plausible yield shift; the corpus path fails the program on
/// a nonzero count.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** the `None` arm cannot
/// be deleted — the match is exhaustive and the build fails, which is itself the
/// guarantee. Faithful mutation: route `None` to `c.degraded += 1` and this
/// fails on both fields.
#[test]
fn a_row_with_no_outcome_is_unclassified_not_degraded() {
    use crate::coverage_recon::schema::Outcome;

    let mut orphan = counted_row(9, Outcome::RefMut, None);
    orphan.outcome = None;
    let c = count_outcomes(&[orphan]);
    assert_eq!(c.unclassified, 1, "an outcome-less row was silently bucketed");
    assert_eq!(c.degraded, 0, "it was folded into the degraded population");
}

/// **S2b.3 Item 2 — the pre-S3 label rides every reported aggregate, VERBATIM.**
///
/// The label is the reason the emitted/degraded split cannot be read as M1's
/// ceiling. A number reported without it is a number that will be quoted
/// without it.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** drop `label=` from
/// `count_line`'s format string and this fails. Second: reword the constant by
/// one character and the verbatim assertion fails.
#[test]
fn every_reported_aggregate_carries_the_pre_s3_label() {
    assert_eq!(
        PRE_S3_LABEL, "pre-S3 — measures S3's absence.",
        "the label is quoted verbatim from the S2b.0/S2b.1 records; rewording it \
         silently re-labels every yield figure this path has ever reported"
    );
    let line = count_line("program=x", &OutcomeCounts::default());
    assert!(
        line.contains(PRE_S3_LABEL),
        "a reported aggregate carried no yield label: {line}"
    );
    assert!(
        count_line("TOTAL", &OutcomeCounts::default()).contains(PRE_S3_LABEL),
        "the corpus TOTAL is the line most likely to be quoted alone"
    );
}

/// **S2b.3 — the `unplaceable` pin, all four verdicts.**
///
/// The pin's whole value is the two non-obvious cases: a sweep whose worker
/// stopped emitting the key, and one emitting garbage, must FAIL rather than
/// read as zero. The nonzero case is here too because nothing exercised the
/// `n != 0` arm of the shared checker — the aggregate tests cover only missing
/// and unparseable — and the accepting case because a pin that rejects a
/// measured zero can never let the corpus sweep pass.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** delete the
/// `ok_or_else` and default a missing key to `"0"` — this fails on the missing
/// case. Second: neuter the `n == 0` arm to an unconditional `Ok` — this fails
/// on the nonzero case.
#[test]
fn the_unplaceable_pin_is_fail_closed() {
    let missing = report::Row::default();
    let err = expected_zero_field(&missing, "unplaceable")
        .expect_err("a missing unplaceable count must fail, never read as zero");
    assert!(err.contains("missing"), "wrong failure: {err}");

    let mut garbage = report::Row::default();
    garbage.set("unplaceable", "not-a-number");
    let err = expected_zero_field(&garbage, "unplaceable")
        .expect_err("an unparseable unplaceable count must fail");
    assert!(err.contains("unparseable"), "wrong failure: {err}");

    let mut nonzero = report::Row::default();
    nonzero.set("unplaceable", 3usize);
    let err = expected_zero_field(&nonzero, "unplaceable")
        .expect_err("a nonzero unplaceable count must fail the pin");
    assert!(err.contains('3'), "the failure must name the count: {err}");

    let mut clean = report::Row::default();
    clean.set("unplaceable", 0usize);
    assert!(
        expected_zero_field(&clean, "unplaceable").is_ok(),
        "the pin must accept a measured zero, or the corpus sweep can never pass"
    );
}

#[test]
fn a_missing_worker_aggregate_fails_closed() {
    let mut verdict = crate::coverage_recon::compare::Verdict::default();
    for class in crate::coverage_recon::compare::FINDING_CLASSES {
        verdict.aggregates.insert(class, 0);
    }
    verdict.aggregates.remove("out-of-coverage");
    let mut row = report::Row::default();

    assert!(
        !run::record_expected_zero_aggregates(&mut row, &verdict),
        "the worker accepted a missing aggregate as zero"
    );
    assert_eq!(
        row.get("agg_out_of_coverage"),
        Some("missing"),
        "the worker did not carry the missing state to the driver"
    );
}

/// **The corpus reconciliation gate.**
///
/// Before Track 1 this sweep was report-only: the worker recorded `recon=FAIL`
/// and then set `status=ok`, no driver asserted anything, and a 20/20 PASS was
/// established by a human reading rows. This test is the enforcement.
///
/// It **continues past failures** and enumerates them all before asserting, so
/// one run yields full incidence rather than halting at the first program.
#[test]
#[ignore = "S2a-H corpus gate: spawns one worker per program"]
fn m1_recon_corpus() {
    use std::{fs, time::Duration};

    let root = orchestrate::workspace_root();
    let art = orchestrate::out_dir().join("m1-recon-artifacts");
    let _ = fs::remove_dir_all(&art);
    fs::create_dir_all(&art).expect("artifact dir");

    let timeout = Duration::from_secs(
        std::env::var("CRAT_BOC1_RECON_TIMEOUT_SECS")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(3000),
    );

    let mut failures: Vec<String> = Vec::new();
    let mut rows: Vec<report::Row> = Vec::new();
    let mut totals = OutcomeCounts::default();
    let mut counted = 0usize;

    for program in CORPUS {
        let input = program.input_path(&root);
        assert!(input.is_file(), "missing rs-crown input: {input:?}");
        let outcome = orchestrate::run_child_env(
            program.name,
            &input,
            "m1-recon",
            timeout,
            &[("CRAT_BOC1_ARTIFACT_DIR", art.display().to_string())],
        );

        let Some(row) = outcome.row.clone() else {
            failures.push(format!(
                "{}: no sentinel row (orchestrator status={})",
                program.name, outcome.status
            ));
            continue;
        };
        let recon = row.get("recon").unwrap_or("missing").to_owned();
        let status = row.get("status").unwrap_or("missing").to_owned();

        if status != "ok" {
            failures.push(format!("{}: status={status} recon={recon}", program.name));
        }
        if recon != "PASS" {
            failures.push(format!("{}: recon={recon}", program.name));
        }
        for class in crate::coverage_recon::compare::FINDING_CLASSES {
            // POPULATION-AWARE (ruling F). Every class keeps its expected-ZERO
            // pin except the locals non-evaluable one, which has a per-program
            // expectation instead — see `EXPECTED_NOT_EVALUABLE_LOCAL`. The
            // exclusion is by NAME rather than by index so reordering
            // `FINDING_CLASSES` cannot silently re-point it.
            if !crate::coverage_recon::compare::expects_zero(class) {
                continue;
            }
            if let Err(detail) = expected_zero_aggregate(&row, class) {
                // The expected-zero pin. A nonzero class is a gate-level
                // finding to rule on, never auto-green: attribution without
                // aggregation is how downgrades go silent.
                failures.push(format!("{}: {detail}", program.name));
            }
        }
        if let Err(detail) = expected_not_evaluable_local(&row, program.name) {
            failures.push(format!("{}: {detail}", program.name));
        }

        // Provenance: digests of the exact bytes the verdict was computed from.
        let mut stamped = row.clone();
        for (key, suffix) in [("a_sha256", "a"), ("b_sha256", "b")] {
            let path = art.join(format!("{}.{suffix}.jsonl", program.name));
            if path.is_file() {
                stamped.set(key, shasum_of(&path));
            }
        }

        // S2b.3 COUNTERS — from the decoded artifact, i.e. the same bytes
        // `a_sha256` above stamps. Read back from the file rather than counted
        // in the worker: the digest then covers the compared AND the counted
        // artifact, and a count computed in-process would be a second
        // derivation with nothing tying it to what was diffed.
        let a_path = art.join(format!("{}.a.jsonl", program.name));
        match fs::read_to_string(&a_path)
            .map_err(|e| e.to_string())
            .and_then(|text| crate::coverage_recon::schema::decode(&text))
        {
            Ok(decoded) => {
                let c = count_outcomes(&decoded);
                println!("{}", count_line(&format!("program={}", program.name), &c));
                // FAIL-CLOSED, not a bucket: producer A writes an outcome on
                // every row, so a row without one means the schema or the
                // decoder moved under us.
                if c.unclassified > 0 {
                    failures.push(format!(
                        "{}: {} artifact row(s) carry no outcome",
                        program.name, c.unclassified
                    ));
                }
                totals.merge(&c);
                counted += 1;
            }
            // An artifact that will not decode is a MISSING measurement. The
            // verdict above already read these bytes, so this can only fire on
            // a real regression — and a zero here would be indistinguishable
            // from a program with no rows.
            Err(why) => failures.push(format!(
                "{}: producer-A artifact not countable: {}",
                program.name,
                report::sanitize(&why)
            )),
        }
        rows.push(stamped);
    }

    for row in &rows {
        println!("{}", report::to_kv_line(row));
    }
    println!("{}", count_line("TOTAL", &totals));
    for (reason, n) in &totals.by_reason {
        println!("M1COUNT-REASON {reason}={n} label={PRE_S3_LABEL:?}");
    }
    assert_eq!(
        rows.len() + failures.iter().filter(|f| f.contains("no sentinel")).count(),
        CORPUS.len(),
        "every corpus program must be attempted"
    );
    assert!(
        failures.is_empty(),
        "S2a-H corpus reconciliation FAILED ({} finding(s)) — full incidence:\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
    // LAST, as a structural backstop. Every way counting can fail already
    // pushes a named failure above, so this fires only if one stopped doing so
    // — and putting it first would preempt that enumeration with a bare
    // arithmetic mismatch on exactly the runs where the names matter most.
    assert_eq!(
        counted,
        rows.len(),
        "a program produced a verdict but no counted artifact rows, without \
         recording why"
    );
}

/// **1.4 VALIDATION TRANSFER.** Structural extraction vs the rendered parser, on
/// the same diagnostics, both paths live for this one run.
///
/// Any mismatch is a FINDING and stops the run: the structural path is labelled
/// FIXTURE-VALIDATED until this passes, and it does not inherit the rendered
/// parser's 86-diagnostic corpus credit by assertion.
#[test]
#[ignore = "1.4 validation transfer: spawns one worker per program"]
fn m1_diag_transfer() {
    use std::{fs, time::Duration};

    let root = orchestrate::workspace_root();
    let timeout = Duration::from_secs(900);
    let mut mismatches: Vec<String> = Vec::new();
    let (mut total_struct, mut total_rendered) = (0usize, 0usize);

    for program in CORPUS {
        let input = program.input_path(&root);
        let outcome = orchestrate::run_child_env(program.name, &input, "m1-diag", timeout, &[]);
        let logs = orchestrate::out_dir().join("logs");
        let out_text = fs::read_to_string(logs.join(format!("{}.m1-diag.out", program.name)))
            .unwrap_or_default();
        let err_text = fs::read_to_string(logs.join(format!("{}.m1-diag.err", program.name)))
            .unwrap_or_default();

        // The frame both sides canonicalize against, from the worker itself.
        // FAIL-CLOSED: no root means no comparable keys, and the fallback this
        // replaced keyed distinct files alike by basename — it failed OPEN.
        let observed_root = diag_root(&out_text)
            .unwrap_or_else(|why| panic!("{}: {why}", program.name));
        let observed_root = std::path::Path::new(&observed_root);

        // STRUCTURAL: (crate-relative file, line)
        let mut structural: Vec<(String, usize)> = out_text
            .lines()
            .filter_map(|l| {
                let rest = l.strip_prefix("M1DIAG-STRUCT file=")?;
                let (file, rest) = rest.split_once(" line=")?;
                let (line, _) = rest.split_once(" dir=")?;
                Some((
                    crate::bo_rewriter::verify::crate_relative(file, observed_root),
                    line.parse().ok()?,
                ))
            })
            .collect();
        // RENDERED: the parser validated on 86 corpus diagnostics at S2b.0 —
        // INCLUDING its error-pairing. A rendered diagnostic emits a `-->` for
        // its primary span AND one per labelled note ("function defined here"),
        // so counting every `-->` over-counts: it reported 163 against
        // structural's 86, the extras being callee declaration sites. Pairing
        // each `error[` with only the FIRST following `-->` is what makes the
        // comparison 1:1, and is exactly what the S2b.0 driver does.
        let mut rendered: Vec<(String, usize)> = Vec::new();
        let mut pending = false;
        for l in err_text.lines() {
            let trimmed = l.trim_start();
            if trimmed.starts_with("error[") || trimmed.starts_with("error:") {
                pending = true;
                continue;
            }
            let Some(site) = trimmed.strip_prefix("--> ") else {
                continue;
            };
            if !pending {
                continue;
            }
            pending = false;
            let mut parts = site.rsplitn(3, ':');
            let (_c, line, path) = (parts.next(), parts.next(), parts.next());
            if let (Some(line), Some(path)) = (line, path)
                && let Ok(line) = line.parse::<usize>()
            {
                rendered.push((
                    crate::bo_rewriter::verify::crate_relative(path, observed_root),
                    line,
                ));
            }
        }
        structural.sort();
        rendered.sort();
        total_struct += structural.len();
        total_rendered += rendered.len();
        if structural != rendered {
            mismatches.push(format!(
                "{}: structural {} vs rendered {}\n    only-structural={:?}\n    only-rendered={:?}",
                program.name,
                structural.len(),
                rendered.len(),
                structural.iter().filter(|x| !rendered.contains(x)).collect::<Vec<_>>(),
                rendered.iter().filter(|x| !structural.contains(x)).collect::<Vec<_>>(),
            ));
        }
        println!(
            "M1DIAG program={} structural={} rendered={} status={}",
            program.name,
            structural.len(),
            rendered.len(),
            outcome.status
        );
    }

    println!("M1DIAG-TOTAL structural={total_struct} rendered={total_rendered}");
    assert!(
        mismatches.is_empty(),
        "the two extraction paths disagree — structural must not inherit the \
         rendered parser's credit:\n  {}",
        mismatches.join("\n  ")
    );
}

/// The observed root the worker compiled in, read from its own stdout.
///
/// # Fail-closed, and why the polarity is the whole point
///
/// This replaced a local canonicalizer that pattern-matched a `crat-verify`
/// temp prefix and, failing that, **fell back to the basename**. That fallback
/// failed OPEN: two distinct files sharing a basename keyed alike, so a genuine
/// structural-vs-rendered disagreement could read as agreement. Returning an
/// error when the frame is absent fails CLOSED — the transfer stops and says
/// so, rather than quietly comparing keys that mean nothing.
///
/// The rule of record this serves: reconciliation gates duplicate their
/// derivations, because disagreement is the signal; canonicalizers are single,
/// because disagreement is the defect. Both sides here canonicalize with
/// [`crate::bo_rewriter::verify::crate_relative`], the production one.
fn diag_root(out_text: &str) -> Result<String, String> {
    out_text
        .lines()
        .find_map(|l| l.strip_prefix("M1DIAG-ROOT dir="))
        .map(|dir| dir.trim().to_owned())
        .ok_or_else(|| {
            "no `M1DIAG-ROOT` line in the worker's stdout — the capture has no \
             frame, so its paths cannot be canonicalized"
                .to_owned()
        })
}

#[test]
fn the_transfer_refuses_a_capture_with_no_frame() {
    assert_eq!(
        diag_root("M1DIAG-ROOT dir=/tmp/crat-verify-1-0/src\nM1DIAG-STRUCT file=x\n").as_deref(),
        Ok("/tmp/crat-verify-1-0/src"),
        "the frame was not read from a well-formed capture"
    );
    // The shape that matters: structural output present, frame absent. The
    // deleted fallback turned this into basename keys and carried on.
    let err = diag_root("M1DIAG-STRUCT file=/a/b/node.rs line=4 dir=Other\n")
        .expect_err("a capture with no frame must be refused, never normalized by guesswork");
    assert!(err.contains("M1DIAG-ROOT"), "the error must name what is missing: {err}");
}

/// **S2b.0 — the pinned measurement.** Full M1 pipeline over all 20 programs.
///
/// # Measurement discipline
///
/// Verdicts are **DATA**. This driver asserts only that every program was
/// ATTEMPTED; it does not assert that any program passes, and nothing is
/// patched mid-run. A measurement run becomes a repair run only by ruling.
///
/// Counts carry the **pre-S3** label: `CallSiteNotAdapted` saturates at ≥69.4%
/// of corpus pointer params before S3 exists, so the emitted/degraded split here
/// is "pre-S3 — measures S3's absence". Only the M1-final report after S3 feeds
/// the emission-guided-refinement decision.
#[test]
#[ignore = "S2b.0 measurement: spawns one worker per program"]
fn m1_emit_corpus() {
    use std::{fs, time::Duration};

    let root = orchestrate::workspace_root();
    let timeout = Duration::from_secs(
        std::env::var("CRAT_BOC1_EMIT_TIMEOUT_SECS")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(900),
    );

    let mut attempted = 0usize;
    let mut missing: Vec<String> = Vec::new();
    let mut rows: Vec<report::Row> = Vec::new();
    // S2b.3: the sweep now ENFORCES one thing. Everything else it reports stays
    // measurement-only.
    let mut failures: Vec<String> = Vec::new();

    // S3.1′ E3c. Cleared per run, like the recon artifact dir: a stale file from
    // an earlier sweep reads as this run's data, which is the staleness rule.
    let revert_dir = orchestrate::out_dir().join("m1-emit-reverts");
    let _ = fs::remove_dir_all(&revert_dir);
    fs::create_dir_all(&revert_dir).expect("revert dir");

    for program in CORPUS {
        let input = program.input_path(&root);
        assert!(input.is_file(), "missing rs-crown input: {input:?}");
        attempted += 1;
        let outcome = orchestrate::run_child_env(
            program.name,
            &input,
            "m1-emit",
            timeout,
            &[("CRAT_BOC1_REVERT_DIR", revert_dir.display().to_string())],
        );
        let Some(mut row) = outcome.row.clone() else {
            // DEFERRAL IS RECORDED, NEVER ZEROED.
            missing.push(format!(
                "{}: no sentinel row (orchestrator status={})",
                program.name, outcome.status
            ));
            continue;
        };
        row.set("program", program.name);

        // Span buckets for the type errors the gate reported, read from the
        // child's own stderr. Empty when the verdict is PASS — in which case
        // "zero whole-crate failures pre-S3" is itself the datum.
        if row.get("verdict") == Some("FAIL") {
            let logs = orchestrate::out_dir().join("logs");
            let err_text =
                fs::read_to_string(logs.join(format!("{}.m1-emit.err", program.name)))
                    .unwrap_or_default();
            let out_text =
                fs::read_to_string(logs.join(format!("{}.m1-emit.out", program.name)))
                    .unwrap_or_default();
            row.set("type_errors", err_text.matches("error[").count());

            // Rewritten subjects' own functions, as (crate-relative file, lo, hi).
            let crate_dir = input.parent().expect("crate dir");
            let sites: Vec<(String, usize, usize)> = out_text
                .lines()
                .filter_map(|line| {
                    let rest = line.strip_prefix("M1EMIT-SITE file=")?;
                    let (file, rest) = rest.split_once(" lo=")?;
                    let (lo, rest) = rest.split_once(" hi=")?;
                    let (hi, _) = rest.split_once(" fn=")?;
                    let rel = std::path::Path::new(file)
                        .strip_prefix(crate_dir)
                        .map(|p| p.display().to_string())
                        .unwrap_or_else(|_| file.to_string());
                    Some((rel, lo.parse().ok()?, hi.parse().ok()?))
                })
                .collect();

            // Bucket each diagnostic. The verify compile runs on a TEMP COPY, so
            // its paths carry a `crat-verify-<pid>-<n>/` prefix; strip it to get
            // the same crate-relative key the sites use.
            let (mut own_fn, mut caller, mut elsewhere) = (0usize, 0usize, 0usize);
            let mut pending: Option<String> = None;
            for line in err_text.lines() {
                let trimmed = line.trim_start();
                if trimmed.starts_with("error[") || trimmed.starts_with("error:") {
                    pending = Some(trimmed.to_owned());
                    continue;
                }
                let Some(site) = trimmed.strip_prefix("--> ") else {
                    continue;
                };
                if pending.take().is_none() {
                    continue;
                }
                let mut parts = site.rsplitn(3, ':');
                let (_col, line_no, path) = (parts.next(), parts.next(), parts.next());
                let (Some(line_no), Some(path)) = (line_no, path) else {
                    continue;
                };
                let Ok(line_no) = line_no.parse::<usize>() else {
                    continue;
                };
                let rel = path
                    .split_once("crat-verify-")
                    .and_then(|(_, tail)| tail.split_once('/'))
                    .map(|(_, rest)| rest.to_string())
                    .unwrap_or_else(|| path.to_string());
                let in_own_fn = sites
                    .iter()
                    .any(|(f, lo, hi)| *f == rel && *lo <= line_no && line_no <= *hi);
                let same_file_rewritten = sites.iter().any(|(f, _, _)| *f == rel);
                if in_own_fn {
                    own_fn += 1;
                } else if same_file_rewritten {
                    caller += 1;
                } else {
                    elsewhere += 1;
                }
                println!(
                    "M1EMIT-DIAG program={} bucket={} site={rel}:{line_no}",
                    program.name,
                    if in_own_fn {
                        "own-fn"
                    } else if same_file_rewritten {
                        "same-file-other-fn"
                    } else {
                        "elsewhere"
                    }
                );
            }
            row.set("bucket_own_fn", own_fn);
            row.set("bucket_same_file_other_fn", caller);
            row.set("bucket_elsewhere", elsewhere);
        }
        // THE PIN (S2b.3). `unplaceable` was measured-zero on the corpus and
        // asserted nowhere; the plan doc read "aggregate-pinned" while nothing
        // was pinned. Enforced here on every row INCLUDING FAIL rows — which is
        // only meaningful because `RewriteOutcome::Degraded` now carries the
        // count instead of reporting a constant. Pinning before that repair
        // would have built a gate that cannot fail where it matters.
        //
        // Continues past a failure and enumerates, as the recon sweep does: one
        // run yields full incidence rather than halting at the first program.
        if let Err(detail) = expected_zero_field(&row, "unplaceable") {
            failures.push(format!("{}: {detail}", program.name));
        }
        rows.push(row);
    }

    for row in &rows {
        println!("{}", report::to_kv_line(row));
    }
    for note in &missing {
        println!("M1EMIT-DEFERRED {note}");
    }
    assert_eq!(
        rows.len() + missing.len(),
        attempted,
        "every corpus program must be attempted"
    );
    assert_eq!(attempted, CORPUS.len(), "the corpus is 20 programs");
    assert!(
        failures.is_empty(),
        "unplaceable is expected-zero corpus-wide ({} finding(s)) — a nonzero \
         count is a decision that reached `plan` and produced no edit, which is \
         a finding to rule on, never auto-green:\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
}

// Worker (one program, one mode, one process).
// ---------------------------------------------------------------------------

#[test]
#[ignore = "C1-lite worker: spawned per program by boc1_corpus (needs CRAT_BOC1_INPUT)"]
fn boc1_run_one() {
    use std::{path::Path, time::Instant};

    let Ok(input) = std::env::var("CRAT_BOC1_INPUT") else {
        eprintln!("BOC1 worker: CRAT_BOC1_INPUT unset; no-op (did you mean boc1_corpus?)");
        return;
    };
    let mode = std::env::var("CRAT_BOC1_MODE").unwrap_or_else(|_| "bo".to_string());
    let name = std::env::var("CRAT_BOC1_NAME").unwrap_or_else(|_| "unnamed".to_string());

    // §NB5-Z (2026-07-17): pin z3's random seeds for the BO sweep — HERE, at the ignored per-program
    // worker entry, before ANY z3 op in this fresh process. z3 0.19's `Context` is a per-thread
    // `thread_local!` built once as `Context::new(&Config::new())` and reused; `set_global_param` only
    // feeds a context created AFTER it fires, so the pin must precede this process's first z3 touch.
    // This is the ONLY correct site: `run_bo` and `solver.rs` are both reached by NON-ignored suite
    // tests (e.g. `origins_runs_once_per_program` calls `run_bo` directly), so pinning there would leak
    // this PROCESS-GLOBAL param into the PARALLEL test runner (Codex NB5-Z finding). `boc1_run_one` is
    // `#[ignore]` and spawned one-per-program as a fresh single-threaded process, so the pin fires once
    // per program and never under the parallel suite. The registered ownership-yield `prod-own`
    // worker is solver-backed, so it shares the same explicit seed contract; the frozen
    // production-borrow `prod` reference remains untouched. Expected behavior-neutral (z3's default
    // seed is already 0); the value is recorded through each solver-backed row's
    // `z3_full_version` stamp.
    if matches!(
        mode.as_str(),
        "bo" | "prod-own" | "prod-precision" | "prod-box" | "selector-core" | "selector-necessity"
    ) || mode.starts_with("selector-detail-")
    {
        z3::set_global_param("smt.random_seed", "0");
        z3::set_global_param("sat.random_seed", "0");
    }

    if mode == "m1-diag" {
        let mut row = run::run_m1_diag(Path::new(&input));
        row.set("program", name.clone());
        println!("{}", report::to_kv_line(&row));
        return;
    }

    if mode == "m1-emit" {
        let mut row = run::run_m1_emit(Path::new(&input));
        row.set("program", name.clone());
        println!("{}", report::to_kv_line(&row));
        return;
    }

    let t0 = Instant::now();
    let result = ::utils::compilation::run_compiler_on_path(Path::new(&input), |tcx| {
        let t_tcx = t0.elapsed();
        match mode.as_str() {
            "bo" => run::run_bo(tcx, t_tcx),
            "prod" => run::run_prod(tcx, t_tcx),
            "prod-own" => run::run_prod_ownership(tcx, t_tcx),
            "prod-precision" => run::run_prod_ownership(tcx, t_tcx),
            "prod-box" => run::run_prod_box(tcx, t_tcx),
            "m1-census" => run::run_m1_census(tcx, t_tcx),
            "m1-recon" => run::run_m1_recon(tcx, t_tcx),
            "selector-core" => run::run_selector_core(tcx, t_tcx),
            "selector-necessity" => run::run_selector_necessity(tcx, t_tcx),
            detail if detail.starts_with("selector-detail-") => {
                run::run_selector_core_detail(tcx, t_tcx)
            }
            other => panic!("unknown CRAT_BOC1_MODE `{other}`"),
        }
    });

    let mut row = match result {
        Ok(row) => row,
        Err(_fatal) => {
            // rustc reported fatal diagnostics on stderr (in the child log).
            let mut row = report::Row::default();
            row.set("status", "compile-error");
            row.set("t_total_s", format!("{:.3}", t0.elapsed().as_secs_f64()));
            row
        }
    };
    // Prepend identity keys so every sentinel line is self-describing.
    let mut ident = report::Row::default();
    ident.set("program", &name);
    ident.set("mode", &mode);
    ident.0.extend(row.0.drain(..));
    println!("{}", report::to_kv_line(&ident));

    // T1.2b — the worker PROCESS fails when the reconciliation does.
    //
    // Deliberately scoped to `m1-recon`. Applying it to every mode would change
    // how the solver sweeps treat `compile-error` and `decline`, silently
    // shifting results the ledger already cites — a blast radius well outside
    // this repair.
    //
    // The panic comes AFTER the sentinel line, so a failing program still
    // reports its row and the driver still sees full incidence.
    if mode == "m1-recon" {
        let status = ident.get("status").unwrap_or("missing");
        assert_eq!(
            status, "ok",
            "m1-recon: {name} did not reconcile (status={status}). The verdict \
             is the process result — a run that reports FAIL and exits green is \
             report-only, which is exactly the defect this scoping repairs."
        );
    }
}

// ---------------------------------------------------------------------------
// Orchestrator (spawns one worker process per program × mode).
// ---------------------------------------------------------------------------

/// Evaluation corpus under `benchmarks/rs-crown/`, smallest-first by measured Rust SLOC.
/// SLOC is cloc 2.00's `code` total over each program's `.rs` files, excluding `build.rs` and
/// `target/`, with duplicate files counted. The development boundary is inclusive of brotli.
#[derive(Clone, Copy, Debug)]
struct CorpusProgram {
    name: &'static str,
    lib_root: &'static str,
    sloc: usize,
}

impl CorpusProgram {
    fn input_path(self, root: &std::path::Path) -> std::path::PathBuf {
        root.join("benchmarks/rs-crown")
            .join(self.name)
            .join(self.lib_root)
    }
}

const BROTLI_SLOC: usize = 537_692;

const fn is_resource_deferred(sloc: usize) -> bool {
    sloc > BROTLI_SLOC
}

const CORPUS: &[CorpusProgram] = &[
    CorpusProgram {
        name: "bst",
        lib_root: "lib.rs",
        sloc: 102,
    },
    CorpusProgram {
        name: "avl",
        lib_root: "lib.rs",
        sloc: 133,
    },
    CorpusProgram {
        name: "ht",
        lib_root: "lib.rs",
        sloc: 251,
    },
    CorpusProgram {
        name: "libcsv",
        lib_root: "lib.rs",
        sloc: 963,
    },
    CorpusProgram {
        name: "buffer",
        lib_root: "lib.rs",
        sloc: 1_104,
    },
    CorpusProgram {
        name: "quadtree",
        lib_root: "lib.rs",
        sloc: 1_184,
    },
    CorpusProgram {
        name: "urlparser",
        lib_root: "lib.rs",
        sloc: 1_363,
    },
    CorpusProgram {
        name: "robotfindskitten",
        lib_root: "lib.rs",
        sloc: 1_476,
    },
    CorpusProgram {
        name: "rgba",
        lib_root: "lib.rs",
        sloc: 1_823,
    },
    CorpusProgram {
        name: "genann",
        lib_root: "lib.rs",
        sloc: 2_302,
    },
    CorpusProgram {
        name: "libtree",
        lib_root: "lib.rs",
        sloc: 2_578,
    },
    CorpusProgram {
        name: "json.h",
        lib_root: "lib.rs",
        sloc: 3_847,
    },
    CorpusProgram {
        name: "binn",
        lib_root: "lib.rs",
        sloc: 4_413,
    },
    CorpusProgram {
        name: "libzahl",
        lib_root: "lib.rs",
        sloc: 4_642,
    },
    CorpusProgram {
        name: "lil",
        lib_root: "lib.rs",
        sloc: 5_638,
    },
    CorpusProgram {
        name: "heman",
        lib_root: "lib.rs",
        sloc: 13_750,
    },
    CorpusProgram {
        name: "bzip2",
        lib_root: "c2rust-lib.rs",
        sloc: 13_967,
    },
    CorpusProgram {
        name: "lodepng",
        lib_root: "lib.rs",
        sloc: 14_140,
    },
    CorpusProgram {
        name: "tulipindicators",
        lib_root: "c2rust-lib.rs",
        sloc: 19_760,
    },
    CorpusProgram {
        name: "brotli",
        lib_root: "lib.rs",
        sloc: BROTLI_SLOC,
    },
];

const PAIRWISE_EXPECTED_JOINT_BY_PROGRAM: [(&str, usize); 20] = [
    ("bst", 0),
    ("avl", 0),
    ("ht", 0),
    ("libcsv", 0),
    ("buffer", 5),
    ("quadtree", 0),
    ("urlparser", 0),
    ("robotfindskitten", 0),
    ("rgba", 0),
    ("genann", 0),
    ("libtree", 7),
    ("json.h", 2),
    ("binn", 0),
    ("libzahl", 4),
    ("lil", 33),
    ("heman", 6),
    ("bzip2", 4),
    ("lodepng", 0),
    ("tulipindicators", 0),
    ("brotli", 2),
];

#[test]
fn rs_crown_catalog_contract() {
    let expected = [
        ("bst", "lib.rs", 102),
        ("avl", "lib.rs", 133),
        ("ht", "lib.rs", 251),
        ("libcsv", "lib.rs", 963),
        ("buffer", "lib.rs", 1_104),
        ("quadtree", "lib.rs", 1_184),
        ("urlparser", "lib.rs", 1_363),
        ("robotfindskitten", "lib.rs", 1_476),
        ("rgba", "lib.rs", 1_823),
        ("genann", "lib.rs", 2_302),
        ("libtree", "lib.rs", 2_578),
        ("json.h", "lib.rs", 3_847),
        ("binn", "lib.rs", 4_413),
        ("libzahl", "lib.rs", 4_642),
        ("lil", "lib.rs", 5_638),
        ("heman", "lib.rs", 13_750),
        ("bzip2", "c2rust-lib.rs", 13_967),
        ("lodepng", "lib.rs", 14_140),
        ("tulipindicators", "c2rust-lib.rs", 19_760),
        ("brotli", "lib.rs", 537_692),
    ];
    let actual: Vec<_> = CORPUS
        .iter()
        .map(|program| (program.name, program.lib_root, program.sloc))
        .collect();

    assert_eq!(CORPUS.len(), 20);
    assert_eq!(actual.as_slice(), expected.as_slice());
    assert_eq!(BROTLI_SLOC, 537_692);
    assert!(!is_resource_deferred(BROTLI_SLOC));
    assert!(is_resource_deferred(BROTLI_SLOC + 1));
    assert!(
        CORPUS
            .iter()
            .all(|program| !is_resource_deferred(program.sloc))
    );

    let root = orchestrate::workspace_root();
    for program in CORPUS {
        let input = program.input_path(&root);
        assert!(
            input.is_file(),
            "missing rs-crown input for {}: {input:?}",
            program.name
        );
        assert!(input.starts_with(root.join("benchmarks/rs-crown")));

        let expected_root = if matches!(program.name, "bzip2" | "tulipindicators") {
            "c2rust-lib.rs"
        } else {
            "lib.rs"
        };
        assert_eq!(
            input.file_name().and_then(|name| name.to_str()),
            Some(expected_root)
        );
    }
}

#[test]
fn pairwise_joint_anchor_covers_exact_catalog() {
    assert_eq!(
        PAIRWISE_EXPECTED_JOINT_BY_PROGRAM
            .iter()
            .map(|(program, _)| *program)
            .collect::<std::collections::BTreeSet<_>>(),
        CORPUS
            .iter()
            .map(|program| program.name)
            .collect::<std::collections::BTreeSet<_>>()
    );
    assert_eq!(
        PAIRWISE_EXPECTED_JOINT_BY_PROGRAM
            .iter()
            .map(|(_, rows)| *rows)
            .sum::<usize>(),
        63
    );
}

#[test]
fn rs_crown_report_contract() {
    let mut row = report::Row::default();
    row.set("program", "bst");
    row.set("status", "ok");
    row.set("repair", "mode_a");
    row.set("z3_full_version", "test-version");
    row.set("sources_leaked_sel", 1);
    row.set("sinks_leaked", 2);
    row.set("s23_stores_owned", 3);
    row.set("s23_owning_model", 4);

    let rendered = render_report(&[row]);
    assert!(rendered.contains("repair=mode_a; smt.random_seed=0; sat.random_seed=0"));
    assert!(rendered.contains("z3_full_version=test-version"));
    for column in [
        "sources_leaked_sel",
        "sinks_leaked",
        "s23_stores_owned",
        "s23_owning_model",
    ] {
        assert!(
            rendered.contains(column),
            "missing report column {column}:\n{rendered}"
        );
    }
}

#[cfg(test)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum DiagnosticWorkerDisposition {
    Complete,
    ResourceDeferred,
    CorrectnessFailure,
}

#[cfg(test)]
fn diagnostic_worker_disposition(status: &str) -> DiagnosticWorkerDisposition {
    match status {
        "ok" => DiagnosticWorkerDisposition::Complete,
        "timeout" | "oom-kill" => DiagnosticWorkerDisposition::ResourceDeferred,
        _ => DiagnosticWorkerDisposition::CorrectnessFailure,
    }
}

#[cfg(test)]
fn representative_case_limit(available: usize) -> usize {
    available.min(2)
}

#[test]
fn selector_leak_resource_walls_defer_but_correctness_failures_stop() {
    assert_eq!(
        diagnostic_worker_disposition("ok"),
        DiagnosticWorkerDisposition::Complete
    );
    for status in ["timeout", "oom-kill"] {
        assert_eq!(
            diagnostic_worker_disposition(status),
            DiagnosticWorkerDisposition::ResourceDeferred,
            "{status} is a resource wall, not a correctness stop"
        );
    }
    for status in ["panic", "crash", "compile-error", "no-output"] {
        assert_eq!(
            diagnostic_worker_disposition(status),
            DiagnosticWorkerDisposition::CorrectnessFailure,
            "{status} must still stop the diagnosis"
        );
    }
}

#[test]
fn selector_leak_representatives_use_available_coverage_up_to_two() {
    assert_eq!(representative_case_limit(0), 0);
    assert_eq!(representative_case_limit(1), 1);
    assert_eq!(representative_case_limit(2), 2);
    assert_eq!(representative_case_limit(3), 2);
}

#[cfg(test)]
mod orchestrate {
    use std::{
        fs,
        path::{Path, PathBuf},
        process::{Command, Stdio},
        time::{Duration, Instant},
    };

    use super::{
        ownership_diagnostic_package, ownership_yield,
        report::{self, Row},
        selector_leak_diagnosis,
    };

    pub struct ChildOutcome {
        /// Orchestrator-level classification: ok | decline | compile-error |
        /// emit-error (from the sentinel), or timeout | oom-kill | panic |
        /// crash | no-output (from process supervision).
        pub status: String,
        pub row: Option<Row>,
        pub wall_s: f64,
        pub note: String,
        pub stderr: String,
    }

    fn env_u64(key: &str, default: u64) -> u64 {
        std::env::var(key)
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(default)
    }

    pub fn workspace_root() -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
    }

    pub fn out_dir() -> PathBuf {
        std::env::var("CRAT_BOC1_OUT")
            .map(PathBuf::from)
            .unwrap_or_else(|_| workspace_root().join("target/boc1"))
    }

    pub fn yield_snapshot_path(program: &str, mode: &str) -> PathBuf {
        out_dir()
            .join("ownership-yield-snapshots")
            .join(format!("{program}.{mode}.tsv"))
    }

    pub fn selector_trace_path(program: &str) -> PathBuf {
        out_dir()
            .join("selector-traces")
            .join(format!("{program}.official.json"))
    }

    pub fn selector_evidence_path(program: &str) -> PathBuf {
        out_dir()
            .join("selector-cores")
            .join(format!("{program}.jsonl"))
    }

    pub fn selector_detail_path(program: &str, case: &str) -> PathBuf {
        out_dir()
            .join("selector-details")
            .join(format!("{program}.{case}.json"))
    }

    pub fn necessity_evidence_path(program: &str) -> PathBuf {
        out_dir()
            .join("selector-family-necessity")
            .join(format!("{program}.json"))
    }

    pub fn production_precision_path(program: &str) -> PathBuf {
        out_dir()
            .join("production-precision")
            .join(format!("{program}.json"))
    }

    pub fn production_box_path(program: &str) -> PathBuf {
        out_dir()
            .join("production-box")
            .join(format!("{program}.json"))
    }

    pub fn projection_snapshot_path(program: &str) -> PathBuf {
        out_dir()
            .join("model-projection")
            .join(format!("{program}.tsv"))
    }

    pub fn legacy_projection_path(program: &str) -> PathBuf {
        out_dir()
            .join("legacy-projection")
            .join(format!("{program}.tsv"))
    }

    /// Current commit SHA of the parent code repo, for the `results.jsonl` provenance stamp.
    /// Best-effort: `unknown` if git is unavailable.
    pub fn git_sha() -> String {
        Command::new("git")
            .args(["rev-parse", "HEAD"])
            .current_dir(workspace_root())
            .output()
            .ok()
            .filter(|o| o.status.success())
            .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
            .filter(|s| !s.is_empty())
            .unwrap_or_else(|| "unknown".to_string())
    }

    /// Whether the working tree is dirty (informational — sweeps often run on WIP branches,
    /// so this warns rather than refuses).
    pub fn git_dirty() -> bool {
        Command::new("git")
            .args(["status", "--porcelain"])
            .current_dir(workspace_root())
            .output()
            .ok()
            .filter(|o| o.status.success())
            .map(|o| !String::from_utf8_lossy(&o.stdout).trim().is_empty())
            .unwrap_or(false)
    }

    pub fn now_unix() -> u64 {
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_secs())
            .unwrap_or(0)
    }

    fn rss_kb(pid: u32) -> Option<u64> {
        let out = Command::new("ps")
            .args(["-o", "rss=", "-p", &pid.to_string()])
            .output()
            .ok()?;
        String::from_utf8_lossy(&out.stdout).trim().parse().ok()
    }

    /// Spawn one worker (this test binary, `--exact bo_c1::boc1_run_one`) with
    /// file-redirected stdio; supervise with deadline + RSS cap; classify.
    pub fn run_child(program: &str, input: &Path, mode: &str, timeout: Duration) -> ChildOutcome {
        run_child_labeled(program, input, mode, mode, timeout, &[])
    }

    /// `run_child` with extra environment for the child.
    ///
    /// Added for S2a-H's corpus gate: `m1-recon` computes its verdict from
    /// written artifacts, so the child needs a directory to write them into.
    pub fn run_child_env(
        program: &str,
        input: &Path,
        mode: &str,
        timeout: Duration,
        extra: &[(&str, String)],
    ) -> ChildOutcome {
        run_child_labeled(program, input, mode, mode, timeout, extra)
    }

    pub fn run_child_labeled(
        program: &str,
        input: &Path,
        mode: &str,
        log_label: &str,
        timeout: Duration,
        extra: &[(&str, String)],
    ) -> ChildOutcome {
        let mem_cap_kb = env_u64("CRAT_BOC1_MEM_MB", 8192) * 1024;
        let logs = out_dir().join("logs");
        fs::create_dir_all(&logs).expect("create log dir");
        let out_path = logs.join(format!("{program}.{log_label}.out"));
        let err_path = logs.join(format!("{program}.{log_label}.err"));
        let out_file = fs::File::create(&out_path).expect("create .out log");
        let err_file = fs::File::create(&err_path).expect("create .err log");

        let exe = std::env::current_exe().expect("current_exe");
        let t0 = Instant::now();
        let mut command = Command::new(exe);
        command
            .args(["bo_c1::boc1_run_one", "--exact", "--ignored", "--nocapture"])
            .env("CRAT_BOC1_INPUT", input)
            .env("CRAT_BOC1_MODE", mode)
            .env("CRAT_BOC1_NAME", program)
            .env("DIR", workspace_root())
            .stdin(Stdio::null())
            .stdout(Stdio::from(out_file))
            .stderr(Stdio::from(err_file));
        for (key, value) in extra {
            command.env(key, value);
        }
        if ownership_yield::enabled() {
            let snapshot = yield_snapshot_path(program, mode);
            fs::create_dir_all(snapshot.parent().expect("snapshot parent"))
                .expect("create ownership-yield snapshot dir");
            if snapshot.is_file() {
                fs::remove_file(&snapshot).expect("remove stale ownership-yield snapshot");
            }
            command.env("CRAT_BOC1_YIELD_SNAPSHOT", snapshot);
        }
        if std::env::var_os("CRAT_BOC1_CROWN_PROJECTION").is_some() {
            command.env(
                "CRAT_BOC1_CROWN_ARTIFACT",
                std::env::var_os("CRAT_BOC1_CROWN_ARTIFACT")
                    .expect("projection requires CRAT_BOC1_CROWN_ARTIFACT"),
            );
            if mode == "bo" {
                let snapshot = projection_snapshot_path(program);
                fs::create_dir_all(snapshot.parent().expect("projection snapshot parent"))
                    .expect("create projection snapshot dir");
                if snapshot.is_file() {
                    fs::remove_file(&snapshot).expect("remove stale projection snapshot");
                }
                command.env("CRAT_BOC1_PROJECTION_SNAPSHOT", snapshot);
            } else if mode == "prod-box" {
                command
                    .env("CRAT_POINTER_DECISION_DIAGNOSTICS", "full")
                    .env("CRAT_POINTER_DECISION_SNAPSHOT_PRE_TRANSFORM", "1");
            }
        }
        if selector_leak_diagnosis::enabled() {
            let trace = selector_trace_path(program);
            let evidence = selector_evidence_path(program);
            fs::create_dir_all(trace.parent().expect("selector trace parent"))
                .expect("create selector trace dir");
            fs::create_dir_all(evidence.parent().expect("selector evidence parent"))
                .expect("create selector evidence dir");
            command
                .env("CRAT_BOC1_SELECTOR_TRACE", &trace)
                .env("CRAT_BOC1_SELECTOR_EVIDENCE", &evidence);
            if mode == "bo" {
                if trace.is_file() {
                    fs::remove_file(&trace).expect("remove stale selector trace");
                }
                command.env("CRAT_BOC1_SELECTOR_CORE", "official");
            } else if mode == "selector-core" && evidence.is_file() {
                fs::remove_file(&evidence).expect("remove stale selector evidence");
            } else if let Some(case) = mode.strip_prefix("selector-detail-") {
                let case = case.replacen('-', ":", 1);
                let detail = selector_detail_path(program, &case.replace(':', "-"));
                fs::create_dir_all(detail.parent().expect("selector detail parent"))
                    .expect("create selector detail dir");
                if detail.is_file() {
                    fs::remove_file(&detail).expect("remove stale selector detail evidence");
                }
                command
                    .env("CRAT_BOC1_SELECTOR_DETAIL_CASE", &case)
                    .env("CRAT_BOC1_SELECTOR_DETAIL_EVIDENCE", detail);
            }
        }
        if ownership_diagnostic_package::enabled()
            || ownership_diagnostic_package::pairwise_enabled()
        {
            let trace = selector_trace_path(program);
            let necessity = necessity_evidence_path(program);
            for path in [&trace, &necessity] {
                fs::create_dir_all(path.parent().expect("diagnostic package artifact parent"))
                    .expect("create diagnostic package artifact dir");
            }
            command.env("CRAT_BOC1_SELECTOR_TRACE", &trace);
            if mode == "bo" {
                if trace.is_file() {
                    fs::remove_file(&trace).expect("remove stale selector trace");
                }
                command.env("CRAT_BOC1_SELECTOR_CORE", "official");
            } else if mode == "selector-necessity" {
                if necessity.is_file() {
                    fs::remove_file(&necessity).expect("remove stale necessity evidence");
                }
                command
                    .env(
                        "CRAT_BOC1_SELECTOR_FAMILY_MATRIX",
                        std::env::var("CRAT_BOC1_SELECTOR_FAMILY_MATRIX")
                            .expect("diagnostic package family matrix"),
                    )
                    .env("CRAT_BOC1_NECESSITY_EVIDENCE", necessity);
            } else if let Some(case) = mode.strip_prefix("selector-detail-") {
                let case = case.replacen('-', ":", 1);
                let detail = selector_detail_path(program, &case.replace(':', "-"));
                fs::create_dir_all(detail.parent().expect("selector detail parent"))
                    .expect("create selector detail dir");
                if detail.is_file() {
                    fs::remove_file(&detail).expect("remove stale selector detail evidence");
                }
                command
                    .env("CRAT_BOC1_SELECTOR_DETAIL_CASE", &case)
                    .env("CRAT_BOC1_SELECTOR_DETAIL_EVIDENCE", detail);
            }
            if ownership_diagnostic_package::enabled() {
                let precision = production_precision_path(program);
                let boxes = production_box_path(program);
                for path in [&precision, &boxes] {
                    fs::create_dir_all(path.parent().expect("diagnostic package artifact parent"))
                        .expect("create diagnostic package artifact dir");
                }
                if mode == "prod-precision" {
                    if precision.is_file() {
                        fs::remove_file(&precision).expect("remove stale precision evidence");
                    }
                    command.env("CRAT_BOC1_PROD_PRECISION_EVIDENCE", precision);
                } else if mode == "prod-box" {
                    command
                        .env("CRAT_POINTER_DECISION_DIAGNOSTICS", "full")
                        .env("CRAT_POINTER_DECISION_SNAPSHOT_PRE_TRANSFORM", "1");
                }
            }
        }
        let mut child = command.spawn().expect("spawn worker");

        let mut killed_for: Option<&str> = None;
        let status = loop {
            match child.try_wait().expect("try_wait") {
                Some(status) => break status,
                None => {
                    if t0.elapsed() >= timeout && killed_for.is_none() {
                        killed_for = Some("timeout");
                        let _ = child.kill();
                    } else if killed_for.is_none()
                        && t0.elapsed().as_millis() % 1000 < 200
                        && rss_kb(child.id()).is_some_and(|kb| kb > mem_cap_kb)
                    {
                        killed_for = Some("oom-kill");
                        let _ = child.kill();
                    }
                    std::thread::sleep(Duration::from_millis(200));
                }
            }
        };
        let wall_s = t0.elapsed().as_secs_f64();

        let stdout = fs::read_to_string(&out_path).unwrap_or_default();
        let stderr = fs::read_to_string(&err_path).unwrap_or_default();
        let row = stdout.lines().rev().find_map(report::parse_kv_line);
        let last_phase = stderr
            .lines()
            .filter(|l| l.starts_with("BOC1PHASE"))
            .next_back()
            .unwrap_or("BOC1PHASE none")
            .to_string();

        // A child that completed (exit 0 + sentinel) beats a raced kill: the
        // deadline/RSS branch can fire in the same poll window in which the
        // child exits, leaving `killed_for` set on an already-dead process.
        let classification = if status.code() == Some(0) && row.is_some() {
            row.as_ref()
                .and_then(|r| r.get("status"))
                .unwrap_or("no-status")
                .to_string()
        } else if let Some(reason) = killed_for {
            reason.to_string()
        } else if let Some(row) = &row {
            row.get("status").unwrap_or("no-status").to_string()
        } else {
            match status.code() {
                Some(0) => "no-output".to_string(),
                Some(_) => "panic".to_string(),
                None => "crash".to_string(),
            }
        };
        let note = if matches!(
            classification.as_str(),
            "timeout" | "oom-kill" | "panic" | "crash"
        ) {
            let tail: String = stderr
                .lines()
                .rev()
                .take(3)
                .collect::<Vec<_>>()
                .into_iter()
                .rev()
                .collect::<Vec<_>>()
                .join(" | ");
            format!("{last_phase} ;; {tail}")
        } else {
            String::new()
        };

        ChildOutcome {
            status: classification,
            row,
            wall_s,
            note,
            stderr,
        }
    }
}

#[test]
#[ignore = "official CROWN-metric projection sweep; run once for Mode-A and once for L2"]
fn boc1_crown_projection_corpus() {
    use std::{fs, path::PathBuf, time::Duration};

    use crown_projection::{
        load_official_program, parse_legacy_decisions, project_legacy_for_universe,
        write_legacy_snapshot,
    };
    use orchestrate::{
        legacy_projection_path, out_dir, projection_snapshot_path, run_child, workspace_root,
    };

    assert_eq!(
        std::env::var("CRAT_BO_REPAIR").as_deref(),
        Ok("mode_a"),
        "projection sweep requires Mode-A"
    );
    assert_eq!(
        std::env::var("CRAT_BOC1_TIMEOUT_SECS").as_deref(),
        Ok("900"),
        "projection sweep requires the official 900-second cap"
    );
    assert_eq!(
        std::env::var("CRAT_BOC1_MEM_MB").as_deref(),
        Ok("8192"),
        "projection sweep requires the official 8192-MiB cap"
    );
    assert!(
        std::env::var_os("CRAT_BOC1_PROGRAMS").is_none(),
        "projection sweep must cover all 20 frozen programs"
    );
    assert_eq!(CORPUS.len(), 20);

    let root = workspace_root();
    let deps = root.join("deps_crate/target/debug/deps");
    assert!(
        deps.is_dir(),
        "deps_crate not built at {deps:?} — run its build first"
    );
    let artifact_root = PathBuf::from(
        std::env::var_os("CRAT_BOC1_CROWN_ARTIFACT")
            .expect("projection sweep requires CRAT_BOC1_CROWN_ARTIFACT"),
    );
    let l2_value = std::env::var("CRAT_BO_L2_GUARDED_COMMITS")
        .expect("projection sweep requires an explicit L2 value");
    assert!(
        matches!(l2_value.as_str(), "0" | "1"),
        "projection sweep L2 value must be exactly 0 or 1"
    );
    let l2_on = l2_value == "1";
    assert_eq!(
        crate::analyses::borrow_ownership::l2::enabled_from_env(),
        l2_on,
        "projection sweep L2 environment disagrees with the analysis gate"
    );
    let legacy = std::env::var("CRAT_BOC1_PROJECTION_LEGACY").as_deref() == Ok("1");
    if legacy {
        assert!(!l2_on, "legacy snapshot belongs only to the Mode-A sweep");
    }

    fs::create_dir_all(out_dir()).expect("create projection output");
    let mut run_contract = String::from(
        "program\tsystem\tstatus\twall_seconds\trepair\tl2\tseed_smt\tseed_sat\ttimeout_seconds\tmemory_mib\tn_ref\tn_own\tuniverse_rows\tnote\n",
    );
    let mut ok = 0usize;
    let mut total_ref = 0usize;
    let mut total_own = 0usize;
    let mut legacy_measurable = 0usize;
    for program in CORPUS {
        let official = load_official_program(&artifact_root, program.name)
            .unwrap_or_else(|error| panic!("{}: {error}", program.name));
        let input = program.input_path(&root);
        let outcome = run_child(program.name, &input, "bo", Duration::from_secs(900));
        let row = outcome
            .row
            .as_ref()
            .unwrap_or_else(|| panic!("{}: BO worker lacks sentinel", program.name));
        let n_ref = row
            .get("n_ref")
            .expect("BO row n_ref")
            .parse::<usize>()
            .expect("numeric n_ref");
        let n_own = row
            .get("n_own")
            .expect("BO row n_own")
            .parse::<usize>()
            .expect("numeric n_own");
        run_contract.push_str(&format!(
            "{}\tBO\t{}\t{:.3}\tmode_a\t{}\t0\t0\t900\t8192\t{}\t{}\t{}\t{}\n",
            program.name,
            outcome.status,
            outcome.wall_s,
            u8::from(l2_on),
            n_ref,
            n_own,
            official.universe.len(),
            outcome.note.replace(['\t', '\n'], " "),
        ));
        if outcome.status == "ok" {
            ok += 1;
            total_ref += n_ref;
            total_own += n_own;
        }
        assert_eq!(
            outcome.status, "ok",
            "{}: BO projection worker failed: {}",
            program.name, outcome.note
        );
        let snapshot =
            crown_projection::read_model_snapshot(&projection_snapshot_path(program.name))
                .unwrap_or_else(|error| panic!("{}: {error}", program.name));
        assert_eq!(
            snapshot.keys().collect::<Vec<_>>(),
            official.universe.iter().collect::<Vec<_>>(),
            "{}: model snapshot keys must equal the official universe",
            program.name
        );

        if legacy {
            let legacy_outcome =
                run_child(program.name, &input, "prod-box", Duration::from_secs(900));
            let expected_unmeasurable = program.name == "urlparser";
            if legacy_outcome.status == "ok" {
                assert!(
                    !expected_unmeasurable,
                    "urlparser unexpectedly crossed the recorded pre-seam parser panic"
                );
                let decisions = parse_legacy_decisions(&legacy_outcome.stderr)
                    .unwrap_or_else(|error| panic!("{}: {error}", program.name));
                let evidence = project_legacy_for_universe(&official.universe, &decisions);
                let path = legacy_projection_path(program.name);
                fs::create_dir_all(path.parent().expect("legacy projection parent"))
                    .expect("create legacy projection dir");
                write_legacy_snapshot(&path, &evidence);
                legacy_measurable += 1;
            } else {
                assert!(
                    expected_unmeasurable,
                    "{}: unexpected legacy worker failure {}: {}",
                    program.name, legacy_outcome.status, legacy_outcome.note
                );
            }
            run_contract.push_str(&format!(
                "{}\tlegacy\t{}\t{:.3}\tproduction-decision\t-\t0\t0\t900\t8192\t\t\t{}\t{}\n",
                program.name,
                if expected_unmeasurable {
                    "unmeasurable-parser-panic"
                } else {
                    &legacy_outcome.status
                },
                legacy_outcome.wall_s,
                official.universe.len(),
                crown_projection::audit_text(legacy_outcome.note.replace(['\t', '\n'], " ")),
            ));
        }
    }
    assert_eq!(ok, 20, "projection BO sweep must accept 20/20");
    if l2_on {
        assert_eq!(
            total_ref, 53_041,
            "L2 projection sweep must reproduce n_ref=53,041"
        );
    } else {
        assert_eq!(
            total_ref, 52_810,
            "Mode-A projection sweep must reproduce n_ref=52,810"
        );
        assert_eq!(
            total_own, 230,
            "Mode-A projection sweep must reproduce n_own=230"
        );
    }
    if legacy {
        assert_eq!(
            legacy_measurable, 19,
            "legacy snapshot must be measurable on 19/20"
        );
    }
    fs::write(out_dir().join("projection-run.tsv"), run_contract)
        .expect("write projection run contract");
    eprintln!(
        "CROWNPROJECTION mode={} ok={ok}/20 n_ref={total_ref} n_own={total_own} legacy={legacy_measurable}/20",
        if l2_on { "l2-on" } else { "mode-a" }
    );
}

#[test]
#[ignore = "combine completed Mode-A/L2 projection sweeps into the three review CSVs"]
fn boc1_crown_projection_combine() {
    use std::{collections::BTreeMap, fs, path::PathBuf};

    use crown_projection::{
        BO_FULL_SCOPE_CSV_HEADER, BoFullScopeCounts, CROWN_LABEL, CrownRealizedKind,
        LEGACY_FULL_SCOPE_CSV_HEADER, LEGACY_LABEL, LegacyBackingKind, LegacyEvidence,
        LegacyFullScopeHistogram, MODEL_LABEL, ModelEvidence, ProjectionOutcome,
        bo_full_scope_csv_rows, classify_legacy_safe_backing, csv_cell, legacy_full_scope_csv_row,
        load_official_program, parse_bo_full_scope_counts, parse_legacy_full_scope_histogram,
        read_legacy_snapshot, read_model_snapshot,
    };

    #[derive(Default)]
    struct Counts {
        eliminated: usize,
        ref_backed: usize,
        owning_backed: usize,
        remaining: usize,
        unmapped: usize,
    }

    #[derive(Default)]
    struct LegacyCounts {
        ref_slice_backed: usize,
        box_family_backed: usize,
        remaining: usize,
        unmapped: usize,
    }

    impl LegacyCounts {
        fn eliminated(&self) -> usize {
            self.ref_slice_backed + self.box_family_backed
        }
    }

    fn model_counts(records: &BTreeMap<String, ModelEvidence>) -> Counts {
        let mut counts = Counts::default();
        for record in records.values() {
            match record.outcome {
                ProjectionOutcome::RefBacked => {
                    counts.eliminated += 1;
                    counts.ref_backed += 1;
                }
                ProjectionOutcome::OwningBacked => {
                    counts.eliminated += 1;
                    counts.owning_backed += 1;
                }
                ProjectionOutcome::Remaining => counts.remaining += 1,
                ProjectionOutcome::Unmapped => counts.unmapped += 1,
                ProjectionOutcome::Eliminated => unreachable!("BO has split eliminated kinds"),
            }
        }
        counts
    }

    fn legacy_counts(records: &BTreeMap<String, LegacyEvidence>) -> LegacyCounts {
        let mut counts = LegacyCounts::default();
        for record in records.values() {
            match record.outcome {
                ProjectionOutcome::Eliminated => {
                    match classify_legacy_safe_backing(&record.kinds)
                        .expect("eliminated legacy record must have only safe backing kinds")
                    {
                        LegacyBackingKind::BoxFamily => counts.box_family_backed += 1,
                        LegacyBackingKind::RefSlice => counts.ref_slice_backed += 1,
                    }
                }
                ProjectionOutcome::Remaining => counts.remaining += 1,
                ProjectionOutcome::Unmapped => counts.unmapped += 1,
                _ => unreachable!("legacy uses unsplit safe outcome"),
            }
        }
        counts
    }

    fn percent(numerator: usize, denominator: usize) -> String {
        if denominator == 0 {
            "0.00".to_owned()
        } else {
            format!("{:.2}", numerator as f64 * 100.0 / denominator as f64)
        }
    }

    let artifact_root = PathBuf::from(
        std::env::var_os("CRAT_BOC1_CROWN_ARTIFACT")
            .expect("combine requires CRAT_BOC1_CROWN_ARTIFACT"),
    );
    let mode_a_root = PathBuf::from(
        std::env::var_os("CRAT_BOC1_MODE_A_OUT").expect("combine requires CRAT_BOC1_MODE_A_OUT"),
    );
    let l2_root = PathBuf::from(
        std::env::var_os("CRAT_BOC1_L2_OUT").expect("combine requires CRAT_BOC1_L2_OUT"),
    );
    let output = orchestrate::out_dir();
    fs::create_dir_all(&output).expect("create combined output");

    let mut comparison = String::from(
        "program,metric_scope,universe_before,CROWN_epistemic_status,CROWN_after,CROWN_realized_eliminated,CROWN_realized_reference,CROWN_realized_Box,CROWN_usage_before,CROWN_usage_after,CROWN_usage_reduction_percent,legacy_epistemic_status,legacy_predicted_eliminated,legacy_predicted_ref_slice_backed,legacy_predicted_Box_family_backed,legacy_predicted_remaining_mapped,legacy_unmapped_counted_remaining,legacy_predicted_remaining_including_unmapped,legacy_unmapped_percent,legacy_validity_flag,BO_Mode_A_epistemic_status,BO_Mode_A_predicted_eliminated,BO_Mode_A_predicted_ref_backed,BO_Mode_A_predicted_owning_backed,BO_Mode_A_predicted_remaining_mapped,BO_Mode_A_unmapped_counted_remaining,BO_Mode_A_predicted_remaining_including_unmapped,BO_Mode_A_unmapped_percent,BO_Mode_A_validity_flag,BO_L2_on_epistemic_status,BO_L2_on_predicted_eliminated,BO_L2_on_predicted_ref_backed,BO_L2_on_predicted_owning_backed,BO_L2_on_predicted_remaining_mapped,BO_L2_on_unmapped_counted_remaining,BO_L2_on_predicted_remaining_including_unmapped,BO_L2_on_unmapped_percent,BO_L2_on_validity_flag\n",
    );
    let mut evidence = String::from(
        "program,declaration_key,CROWN_epistemic_status,CROWN_realized_status,legacy_epistemic_status,legacy_mapping,legacy_prediction,legacy_mapped_subjects,legacy_final_kinds,BO_Mode_A_epistemic_status,BO_Mode_A_mapping,BO_Mode_A_prediction,BO_Mode_A_mapped_MIR_locals,BO_Mode_A_mapped_d0_slots,BO_Mode_A_raw_slots,BO_Mode_A_ref_slots,BO_Mode_A_owning_slots,BO_Mode_A_slot_keys,BO_L2_on_epistemic_status,BO_L2_on_mapping,BO_L2_on_prediction,BO_L2_on_mapped_MIR_locals,BO_L2_on_mapped_d0_slots,BO_L2_on_raw_slots,BO_L2_on_ref_slots,BO_L2_on_owning_slots,BO_L2_on_slot_keys\n",
    );

    let mut corpus_universe = 0usize;
    let mut corpus_crown_after = 0usize;
    let mut corpus_crown_ref = 0usize;
    let mut corpus_crown_box = 0usize;
    let mut corpus_usage_before = 0u64;
    let mut corpus_usage_after = 0u64;
    let mut corpus_mode_a = Counts::default();
    let mut corpus_l2 = Counts::default();
    let mut legacy_19_universe = 0usize;
    let mut legacy_19 = LegacyCounts::default();
    let mut crown_19_after = 0usize;
    let mut crown_19_ref = 0usize;
    let mut crown_19_box = 0usize;
    let mut mode_a_19 = Counts::default();
    let mut l2_19 = Counts::default();

    for program in CORPUS {
        let official = load_official_program(&artifact_root, program.name)
            .unwrap_or_else(|error| panic!("{}: {error}", program.name));
        let mode_a = read_model_snapshot(
            &mode_a_root
                .join("model-projection")
                .join(format!("{}.tsv", program.name)),
        )
        .unwrap_or_else(|error| panic!("{} Mode-A: {error}", program.name));
        let l2 = read_model_snapshot(
            &l2_root
                .join("model-projection")
                .join(format!("{}.tsv", program.name)),
        )
        .unwrap_or_else(|error| panic!("{} L2: {error}", program.name));
        assert_eq!(
            mode_a.keys().collect::<Vec<_>>(),
            official.universe.iter().collect::<Vec<_>>(),
            "{}: Mode-A evidence is not the official universe",
            program.name
        );
        assert_eq!(
            l2.keys().collect::<Vec<_>>(),
            official.universe.iter().collect::<Vec<_>>(),
            "{}: L2 evidence is not the official universe",
            program.name
        );
        let mode_a_counts = model_counts(&mode_a);
        let l2_counts = model_counts(&l2);
        for (label, counts) in [("Mode-A", &mode_a_counts), ("L2", &l2_counts)] {
            assert_eq!(
                counts.eliminated + counts.remaining + counts.unmapped,
                official.universe.len(),
                "{}: {label} eliminated + remaining + unmapped != BEFORE",
                program.name
            );
            assert_eq!(
                counts.ref_backed + counts.owning_backed,
                counts.eliminated,
                "{}: {label} safe-kind split does not reconcile",
                program.name
            );
        }

        let legacy = if program.name == "urlparser" {
            None
        } else {
            let records = read_legacy_snapshot(
                &mode_a_root
                    .join("legacy-projection")
                    .join(format!("{}.tsv", program.name)),
            )
            .unwrap_or_else(|error| panic!("{} legacy: {error}", program.name));
            assert_eq!(
                records.keys().collect::<Vec<_>>(),
                official.universe.iter().collect::<Vec<_>>(),
                "{}: legacy evidence is not the official universe",
                program.name
            );
            Some(records)
        };
        let legacy_counts = legacy.as_ref().map(|records| {
            let counts = legacy_counts(records);
            assert_eq!(
                counts.eliminated() + counts.remaining + counts.unmapped,
                official.universe.len(),
                "{}: legacy eliminated + remaining + unmapped != BEFORE",
                program.name
            );
            counts
        });

        let crown_ref = official
            .crown_kinds
            .values()
            .filter(|kind| **kind == CrownRealizedKind::Reference)
            .count();
        let crown_box = official
            .crown_kinds
            .values()
            .filter(|kind| **kind == CrownRealizedKind::Box)
            .count();
        let crown_eliminated = crown_ref + crown_box;
        assert_eq!(
            crown_eliminated + official.evaluation.declaration_after as usize,
            official.universe.len(),
            "{}: CROWN realized partition does not reconcile",
            program.name
        );

        let legacy_cells = if let Some(counts) = &legacy_counts {
            vec![
                LEGACY_LABEL.to_owned(),
                counts.eliminated().to_string(),
                counts.ref_slice_backed.to_string(),
                counts.box_family_backed.to_string(),
                counts.remaining.to_string(),
                counts.unmapped.to_string(),
                (counts.remaining + counts.unmapped).to_string(),
                percent(counts.unmapped, official.universe.len()),
                if counts.unmapped * 100 > official.universe.len() * 3 {
                    "VALIDITY-LIMIT: unmapped >3.0%".to_owned()
                } else {
                    "within 3.0% threshold".to_owned()
                },
            ]
        } else {
            vec![
                "unmeasurable: urlparser pre-seam parser panic".to_owned(),
                String::new(),
                String::new(),
                String::new(),
                String::new(),
                String::new(),
                String::new(),
                String::new(),
                "unmeasurable".to_owned(),
            ]
        };
        let model_cells = |counts: &Counts| {
            vec![
                MODEL_LABEL.to_owned(),
                counts.eliminated.to_string(),
                counts.ref_backed.to_string(),
                counts.owning_backed.to_string(),
                counts.remaining.to_string(),
                counts.unmapped.to_string(),
                (counts.remaining + counts.unmapped).to_string(),
                percent(counts.unmapped, official.universe.len()),
                if counts.unmapped * 100 > official.universe.len() * 3 {
                    "VALIDITY-LIMIT: unmapped >3.0%".to_owned()
                } else {
                    "within 3.0% threshold".to_owned()
                },
            ]
        };
        let mut row = vec![
            program.name.to_owned(),
            "function declaration d0 Mut ∩ Ptr; fields/deeper/const/array excluded".to_owned(),
            official.universe.len().to_string(),
            CROWN_LABEL.to_owned(),
            official.evaluation.declaration_after.to_string(),
            crown_eliminated.to_string(),
            crown_ref.to_string(),
            crown_box.to_string(),
            official.evaluation.usage_before.to_string(),
            official.evaluation.usage_after.to_string(),
            official.evaluation.usage_rate.clone(),
        ];
        row.extend(legacy_cells);
        row.extend(model_cells(&mode_a_counts));
        row.extend(model_cells(&l2_counts));
        comparison.push_str(&row.into_iter().map(csv_cell).collect::<Vec<_>>().join(","));
        comparison.push('\n');

        for key in &official.universe {
            let crown = official.crown_kinds[key].as_str();
            let mode_a_record = &mode_a[key];
            let l2_record = &l2[key];
            let legacy_fields = if let Some(records) = &legacy {
                let record = &records[key];
                vec![
                    LEGACY_LABEL.to_owned(),
                    record.completeness.as_str().to_owned(),
                    record.outcome.as_str().to_owned(),
                    record.mapped_subjects.to_string(),
                    record
                        .kinds
                        .iter()
                        .map(|kind| format!("{kind:?}"))
                        .collect::<Vec<_>>()
                        .join(";"),
                ]
            } else {
                vec![
                    "unmeasurable: urlparser pre-seam parser panic".to_owned(),
                    String::new(),
                    "unmeasurable".to_owned(),
                    String::new(),
                    String::new(),
                ]
            };
            let model_fields = |record: &ModelEvidence| {
                vec![
                    MODEL_LABEL.to_owned(),
                    record.completeness.as_str().to_owned(),
                    record.outcome.as_str().to_owned(),
                    record.mapped_mir_locals.to_string(),
                    record.mapped_slots.to_string(),
                    record.raw_slots.to_string(),
                    record.ref_slots.to_string(),
                    record.owning_slots.to_string(),
                    record.slot_keys.join(";"),
                ]
            };
            let mut row = vec![
                program.name.to_owned(),
                key.clone(),
                CROWN_LABEL.to_owned(),
                crown.to_owned(),
            ];
            row.extend(legacy_fields);
            row.extend(model_fields(mode_a_record));
            row.extend(model_fields(l2_record));
            evidence.push_str(&row.into_iter().map(csv_cell).collect::<Vec<_>>().join(","));
            evidence.push('\n');
        }

        corpus_universe += official.universe.len();
        corpus_crown_after += official.evaluation.declaration_after as usize;
        corpus_crown_ref += crown_ref;
        corpus_crown_box += crown_box;
        corpus_usage_before += official.evaluation.usage_before;
        corpus_usage_after += official.evaluation.usage_after;
        for (total, counts) in [
            (&mut corpus_mode_a, &mode_a_counts),
            (&mut corpus_l2, &l2_counts),
        ] {
            total.eliminated += counts.eliminated;
            total.ref_backed += counts.ref_backed;
            total.owning_backed += counts.owning_backed;
            total.remaining += counts.remaining;
            total.unmapped += counts.unmapped;
        }
        if let Some(counts) = legacy_counts {
            legacy_19_universe += official.universe.len();
            legacy_19.ref_slice_backed += counts.ref_slice_backed;
            legacy_19.box_family_backed += counts.box_family_backed;
            legacy_19.remaining += counts.remaining;
            legacy_19.unmapped += counts.unmapped;
            crown_19_after += official.evaluation.declaration_after as usize;
            crown_19_ref += crown_ref;
            crown_19_box += crown_box;
            for (total, counts) in [(&mut mode_a_19, &mode_a_counts), (&mut l2_19, &l2_counts)] {
                total.eliminated += counts.eliminated;
                total.ref_backed += counts.ref_backed;
                total.owning_backed += counts.owning_backed;
                total.remaining += counts.remaining;
                total.unmapped += counts.unmapped;
            }
        }
    }

    assert_eq!(corpus_universe, 2_414);
    assert_eq!(corpus_crown_after, 1_711);
    assert_eq!(corpus_crown_ref, 650);
    assert_eq!(corpus_crown_box, 53);
    assert_eq!(
        corpus_mode_a.eliminated + corpus_mode_a.remaining + corpus_mode_a.unmapped,
        2_414
    );
    assert_eq!(
        corpus_l2.eliminated + corpus_l2.remaining + corpus_l2.unmapped,
        2_414
    );
    assert_eq!(legacy_19.eliminated(), 1_457);
    assert_eq!(legacy_19.ref_slice_backed, 1_438);
    assert_eq!(legacy_19.box_family_backed, 19);

    let aggregate_model_cells = |counts: &Counts, denominator: usize| {
        vec![
            MODEL_LABEL.to_owned(),
            counts.eliminated.to_string(),
            counts.ref_backed.to_string(),
            counts.owning_backed.to_string(),
            counts.remaining.to_string(),
            counts.unmapped.to_string(),
            (counts.remaining + counts.unmapped).to_string(),
            percent(counts.unmapped, denominator),
            if counts.unmapped * 100 > denominator * 3 {
                "VALIDITY-LIMIT: unmapped >3.0%".to_owned()
            } else {
                "within 3.0% threshold".to_owned()
            },
        ]
    };
    let mut subtotal = vec![
        "LEGACY_MEASURABLE_19_SUBTOTAL".to_owned(),
        "same official universe, excluding unmeasurable urlparser".to_owned(),
        legacy_19_universe.to_string(),
        CROWN_LABEL.to_owned(),
        crown_19_after.to_string(),
        (crown_19_ref + crown_19_box).to_string(),
        crown_19_ref.to_string(),
        crown_19_box.to_string(),
        String::new(),
        String::new(),
        String::new(),
        LEGACY_LABEL.to_owned(),
        legacy_19.eliminated().to_string(),
        legacy_19.ref_slice_backed.to_string(),
        legacy_19.box_family_backed.to_string(),
        legacy_19.remaining.to_string(),
        legacy_19.unmapped.to_string(),
        (legacy_19.remaining + legacy_19.unmapped).to_string(),
        percent(legacy_19.unmapped, legacy_19_universe),
        if legacy_19.unmapped * 100 > legacy_19_universe * 3 {
            "VALIDITY-LIMIT: unmapped >3.0%".to_owned()
        } else {
            "within 3.0% threshold".to_owned()
        },
    ];
    subtotal.extend(aggregate_model_cells(&mode_a_19, legacy_19_universe));
    subtotal.extend(aggregate_model_cells(&l2_19, legacy_19_universe));
    comparison.push_str(
        &subtotal
            .into_iter()
            .map(csv_cell)
            .collect::<Vec<_>>()
            .join(","),
    );
    comparison.push('\n');

    let usage_rate = format!(
        "{:.1}%",
        (corpus_usage_before - corpus_usage_after) as f64 * 100.0 / corpus_usage_before as f64
    );
    let mut corpus = vec![
        "CORPUS_20".to_owned(),
        "function declaration d0 Mut ∩ Ptr; fields/deeper/const/array excluded".to_owned(),
        corpus_universe.to_string(),
        CROWN_LABEL.to_owned(),
        corpus_crown_after.to_string(),
        (corpus_crown_ref + corpus_crown_box).to_string(),
        corpus_crown_ref.to_string(),
        corpus_crown_box.to_string(),
        corpus_usage_before.to_string(),
        corpus_usage_after.to_string(),
        usage_rate,
        "unmeasurable corpus-wide: urlparser pre-seam parser panic; see 19-program subtotal"
            .to_owned(),
        String::new(),
        String::new(),
        String::new(),
        String::new(),
        String::new(),
        String::new(),
        String::new(),
        "unmeasurable".to_owned(),
    ];
    corpus.extend(aggregate_model_cells(&corpus_mode_a, corpus_universe));
    corpus.extend(aggregate_model_cells(&corpus_l2, corpus_universe));
    comparison.push_str(
        &corpus
            .into_iter()
            .map(csv_cell)
            .collect::<Vec<_>>()
            .join(","),
    );
    comparison.push('\n');

    let mut bo_full_scope = String::from(BO_FULL_SCOPE_CSV_HEADER);
    for (root, profile, expected_ref, expected_own, expected_raw) in [
        (&mode_a_root, "Mode-A L2-off", 52_810, 230, 9_742),
        (&l2_root, "Mode-A L2-on", 53_041, 240, 9_501),
    ] {
        let mut total = BoFullScopeCounts {
            program: "CORPUS_20".to_owned(),
            slots_total: 0,
            n_ref: 0,
            n_own: 0,
            n_raw: 0,
            n_ref_d0: 0,
            n_own_d0: 0,
            n_raw_d0: 0,
        };
        for program in CORPUS {
            let log_path = root.join("logs").join(format!("{}.bo.out", program.name));
            let counts = parse_bo_full_scope_counts(
                &fs::read_to_string(&log_path)
                    .unwrap_or_else(|error| panic!("{}: {error}", log_path.display())),
            )
            .unwrap_or_else(|error| panic!("{} {profile}: {error}", program.name));
            assert_eq!(counts.program, program.name);
            bo_full_scope.push_str(
                &bo_full_scope_csv_rows(profile, &counts).unwrap_or_else(|error| panic!("{error}")),
            );
            total.slots_total += counts.slots_total;
            total.n_ref += counts.n_ref;
            total.n_own += counts.n_own;
            total.n_raw += counts.n_raw;
            total.n_ref_d0 += counts.n_ref_d0;
            total.n_own_d0 += counts.n_own_d0;
            total.n_raw_d0 += counts.n_raw_d0;
        }
        assert_eq!(total.slots_total, 62_782, "{profile}: slots_total drifted");
        assert_eq!(total.n_ref, expected_ref, "{profile}: n_ref drifted");
        assert_eq!(total.n_own, expected_own, "{profile}: n_own drifted");
        assert_eq!(total.n_raw, expected_raw, "{profile}: n_raw drifted");
        bo_full_scope.push_str(
            &bo_full_scope_csv_rows(profile, &total).unwrap_or_else(|error| panic!("{error}")),
        );
    }

    let mut legacy_full_scope = String::from(LEGACY_FULL_SCOPE_CSV_HEADER);
    let mut legacy_corpus = LegacyFullScopeHistogram::default();
    for program in CORPUS {
        if program.name == "urlparser" {
            legacy_full_scope.push_str(
                &legacy_full_scope_csv_row(
                    program.name,
                    "unmeasurable: urlparser pre-seam parser panic",
                    None,
                )
                .unwrap_or_else(|error| panic!("{error}")),
            );
            continue;
        }
        let log_path = mode_a_root
            .join("logs")
            .join(format!("{}.prod-box.err", program.name));
        let counts = parse_legacy_full_scope_histogram(
            &fs::read_to_string(&log_path)
                .unwrap_or_else(|error| panic!("{}: {error}", log_path.display())),
        )
        .unwrap_or_else(|error| panic!("{} legacy full-scope: {error}", program.name));
        assert!(
            counts.subjects_total() > 0,
            "{}: legacy diagnostic contains no decision subjects",
            program.name
        );
        legacy_full_scope.push_str(
            &legacy_full_scope_csv_row(program.name, "measured", Some(&counts))
                .unwrap_or_else(|error| panic!("{error}")),
        );
        legacy_corpus.add_assign(&counts);
    }
    assert_eq!(legacy_corpus.subjects_total(), 8_335);
    assert_eq!(legacy_corpus.box_family_count(), 84);
    legacy_full_scope.push_str(
        &legacy_full_scope_csv_row(
            "CORPUS_19_MEASURABLE",
            "measured; urlparser excluded as unmeasurable",
            Some(&legacy_corpus),
        )
        .unwrap_or_else(|error| panic!("{error}")),
    );

    let mut runs = String::from(
        "program,system,epistemic_status,worker_status,wall_seconds,repair,L2_guarded_commits,smt_random_seed,sat_random_seed,timeout_seconds,memory_mib,n_ref_internal,n_own_internal,official_universe_rows,unmapped_rows,unmapped_percent,validity_flag,note\n",
    );
    for (root, profile) in [(&mode_a_root, "Mode-A L2-off"), (&l2_root, "Mode-A L2-on")] {
        let source = fs::read_to_string(root.join("projection-run.tsv"))
            .unwrap_or_else(|error| panic!("{}: {error}", root.display()));
        let mut lines = source.lines();
        let header = lines
            .next()
            .expect("run TSV header")
            .split('\t')
            .collect::<Vec<_>>();
        for line in lines {
            let fields = line.split('\t').collect::<Vec<_>>();
            let get = |name: &str| {
                fields[header
                    .iter()
                    .position(|column| *column == name)
                    .expect("run column")]
            };
            if root == &l2_root && get("system") == "legacy" {
                continue;
            }
            let program = get("program");
            let (epistemic, unmapped, denominator) = if get("system") == "legacy" {
                if program == "urlparser" {
                    (
                        "unmeasurable: urlparser pre-seam parser panic",
                        None,
                        get("universe_rows").parse::<usize>().expect("universe"),
                    )
                } else {
                    let records = read_legacy_snapshot(
                        &mode_a_root
                            .join("legacy-projection")
                            .join(format!("{program}.tsv")),
                    )
                    .expect("legacy run coverage");
                    (
                        LEGACY_LABEL,
                        Some(
                            records
                                .values()
                                .filter(|record| record.outcome == ProjectionOutcome::Unmapped)
                                .count(),
                        ),
                        records.len(),
                    )
                }
            } else {
                let records = read_model_snapshot(
                    &root.join("model-projection").join(format!("{program}.tsv")),
                )
                .expect("model run coverage");
                (
                    MODEL_LABEL,
                    Some(
                        records
                            .values()
                            .filter(|record| record.outcome == ProjectionOutcome::Unmapped)
                            .count(),
                    ),
                    records.len(),
                )
            };
            let unmapped_percent = unmapped.map(|value| percent(value, denominator));
            let validity = match unmapped {
                None => "unmeasurable".to_owned(),
                Some(value) if value * 100 > denominator * 3 => {
                    "VALIDITY-LIMIT: unmapped >3.0%".to_owned()
                }
                Some(_) => "within 3.0% threshold".to_owned(),
            };
            let row = [
                program.to_owned(),
                if get("system") == "BO" {
                    profile.to_owned()
                } else {
                    "legacy".to_owned()
                },
                epistemic.to_owned(),
                get("status").to_owned(),
                get("wall_seconds").to_owned(),
                get("repair").to_owned(),
                get("l2").to_owned(),
                get("seed_smt").to_owned(),
                get("seed_sat").to_owned(),
                get("timeout_seconds").to_owned(),
                get("memory_mib").to_owned(),
                get("n_ref").to_owned(),
                get("n_own").to_owned(),
                denominator.to_string(),
                unmapped.map(|value| value.to_string()).unwrap_or_default(),
                unmapped_percent.unwrap_or_default(),
                validity,
                get("note").to_owned(),
            ];
            runs.push_str(&row.into_iter().map(csv_cell).collect::<Vec<_>>().join(","));
            runs.push('\n');
        }
    }

    let comparison_path = output.join("2026-07-27-crown-official-metric-projection.csv");
    let evidence_path = output.join("2026-07-27-crown-official-metric-declarations.csv");
    let runs_path = output.join("2026-07-27-crown-official-metric-runs.csv");
    let bo_full_scope_path = output.join("2026-07-27-bo-full-scope-kind-distribution.csv");
    let legacy_full_scope_path = output.join("2026-07-27-legacy-full-scope-decision-histogram.csv");
    fs::write(&comparison_path, comparison).expect("write comparison CSV");
    fs::write(&evidence_path, evidence).expect("write evidence CSV");
    fs::write(&runs_path, runs).expect("write runs CSV");
    fs::write(&bo_full_scope_path, bo_full_scope).expect("write BO full-scope CSV");
    fs::write(&legacy_full_scope_path, legacy_full_scope).expect("write legacy full-scope CSV");
    eprintln!(
        "CROWNPROJECTION combined universe=2414 CROWN=703({}+{}) legacy={}({}+{}) mode_a={} l2={} files={},{},{},{},{}",
        corpus_crown_ref,
        corpus_crown_box,
        legacy_19.eliminated(),
        legacy_19.ref_slice_backed,
        legacy_19.box_family_backed,
        corpus_mode_a.eliminated,
        corpus_l2.eliminated,
        comparison_path.display(),
        evidence_path.display(),
        runs_path.display(),
        bo_full_scope_path.display(),
        legacy_full_scope_path.display(),
    );
}

#[test]
#[ignore = "C1-lite corpus sweep: run explicitly with --exact bo_c1::boc1_corpus --ignored --nocapture"]
fn boc1_corpus() {
    use std::{
        collections::{BTreeMap, BTreeSet},
        fs,
        time::Duration,
    };

    use orchestrate::{
        necessity_evidence_path, out_dir, production_box_path, production_precision_path,
        run_child, run_child_labeled, selector_detail_path, selector_evidence_path,
        selector_trace_path, workspace_root, yield_snapshot_path,
    };
    use report::Row;

    let root = workspace_root();
    let deps = root.join("deps_crate/target/debug/deps");
    assert!(
        deps.is_dir(),
        "deps_crate not built at {deps:?} — run `cargo build --manifest-path deps_crate/Cargo.toml` first"
    );

    let timeout = Duration::from_secs(
        std::env::var("CRAT_BOC1_TIMEOUT_SECS")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(900),
    );
    let prod_timeout = Duration::from_secs(
        std::env::var("CRAT_BOC1_PROD_TIMEOUT_SECS")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(900),
    );
    let diagnostic_timeout = Duration::from_secs(
        std::env::var("CRAT_BOC1_DIAG_TIMEOUT_SECS")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(1800),
    );
    let prod_enabled = std::env::var("CRAT_BOC1_PROD")
        .map(|v| v != "0")
        .unwrap_or(true);
    let ownership_yield_enabled = ownership_yield::enabled();
    let selector_leak_diag = selector_leak_diagnosis::enabled();
    let diagnostic_package = ownership_diagnostic_package::enabled();
    let pairwise_probe = ownership_diagnostic_package::pairwise_enabled();
    let prod_box_snapshot_only = ownership_diagnostic_package::snapshot_only_enabled();
    let only: Option<Vec<String>> = std::env::var("CRAT_BOC1_PROGRAMS")
        .ok()
        .map(|v| v.split(',').map(|s| s.trim().to_string()).collect());
    let l2_gate = l2_red_gate::enabled();
    if selector_leak_diag {
        assert_eq!(
            std::env::var("CRAT_BO_REPAIR").as_deref(),
            Ok("mode_a"),
            "selector-leak diagnosis requires Mode-A"
        );
        assert_eq!(
            std::env::var("CRAT_BO_L2_GUARDED_COMMITS").as_deref(),
            Ok("0"),
            "selector-leak diagnosis requires L2 explicitly off"
        );
        assert!(
            !crate::analyses::borrow_ownership::l2::enabled_from_env(),
            "selector-leak diagnosis resolved L2 on"
        );
        assert_eq!(
            timeout,
            Duration::from_secs(900),
            "selector-leak official worker timeout must be 900 seconds"
        );
        assert_eq!(
            diagnostic_timeout,
            Duration::from_secs(1800),
            "selector-leak tracked worker timeout must be 1800 seconds"
        );
        assert_eq!(
            std::env::var("CRAT_BOC1_MEM_MB").as_deref(),
            Ok("8192"),
            "selector-leak diagnosis requires the 8192-MiB worker cap"
        );
        assert!(
            !prod_enabled,
            "selector-leak diagnosis must disable production workers"
        );
        assert!(
            only.is_none(),
            "selector-leak diagnosis must cover all 20 frozen programs"
        );
        assert_eq!(CORPUS.len(), 20);
    }
    if diagnostic_package {
        assert_eq!(
            std::env::var("CRAT_BO_REPAIR").as_deref(),
            Ok("mode_a"),
            "ownership diagnostic package requires Mode-A"
        );
        assert_eq!(
            std::env::var("CRAT_BO_L2_GUARDED_COMMITS").as_deref(),
            Ok("0"),
            "ownership diagnostic package requires L2 explicitly off"
        );
        assert!(
            !crate::analyses::borrow_ownership::l2::enabled_from_env(),
            "ownership diagnostic package resolved L2 on"
        );
        assert_eq!(
            timeout,
            Duration::from_secs(900),
            "ownership diagnostic official timeout must be 900 seconds"
        );
        assert_eq!(
            diagnostic_timeout,
            Duration::from_secs(1800),
            "ownership diagnostic worker timeout must be 1800 seconds"
        );
        assert_eq!(
            prod_timeout,
            Duration::from_secs(1800),
            "ownership diagnostic production timeout must be 1800 seconds"
        );
        assert_eq!(
            std::env::var("CRAT_BOC1_MEM_MB").as_deref(),
            Ok("8192"),
            "ownership diagnostic package requires the 8192-MiB worker cap"
        );
        assert!(
            !prod_enabled,
            "ownership diagnostic package owns its production workers"
        );
        assert!(
            only.is_none(),
            "ownership diagnostic package must cover all 20 frozen programs"
        );
        assert!(
            !selector_leak_diag && !ownership_yield_enabled && !l2_gate,
            "ownership diagnostic package is mutually exclusive with other corpus modes"
        );
        if !prod_box_snapshot_only {
            let family_matrix = std::env::var("CRAT_BOC1_SELECTOR_FAMILY_MATRIX")
                .expect("ownership diagnostic package requires the accepted family matrix");
            assert!(
                std::path::Path::new(&family_matrix).is_file(),
                "accepted family matrix does not exist: {family_matrix}"
            );
        }
        assert_eq!(CORPUS.len(), 20);
    }
    if pairwise_probe {
        assert_eq!(
            std::env::var("CRAT_BO_REPAIR").as_deref(),
            Ok("mode_a"),
            "pairwise family removal requires Mode-A"
        );
        assert_eq!(
            std::env::var("CRAT_BO_L2_GUARDED_COMMITS").as_deref(),
            Ok("0"),
            "pairwise family removal requires L2 explicitly off"
        );
        assert!(
            !crate::analyses::borrow_ownership::l2::enabled_from_env(),
            "pairwise family removal resolved L2 on"
        );
        assert_eq!(
            timeout,
            Duration::from_secs(900),
            "pairwise official timeout must be 900 seconds"
        );
        assert_eq!(
            diagnostic_timeout,
            Duration::from_secs(900),
            "pairwise diagnostic first-pass timeout must be 900 seconds"
        );
        assert_eq!(
            std::env::var("CRAT_BOC1_MEM_MB").as_deref(),
            Ok("8192"),
            "pairwise family removal requires the 8192-MiB worker cap"
        );
        assert!(
            !prod_enabled,
            "pairwise family removal must disable production workers"
        );
        assert!(
            only.is_none(),
            "pairwise family removal must cover all 20 frozen programs"
        );
        assert!(
            !diagnostic_package
                && !selector_leak_diag
                && !ownership_yield_enabled
                && !l2_gate
                && !prod_box_snapshot_only,
            "pairwise family removal is mutually exclusive with other corpus modes"
        );
        let family_matrix = std::env::var("CRAT_BOC1_SELECTOR_FAMILY_MATRIX")
            .expect("pairwise family removal requires the accepted family matrix");
        assert!(
            std::path::Path::new(&family_matrix).is_file(),
            "accepted family matrix does not exist: {family_matrix}"
        );
        assert_eq!(CORPUS.len(), 20);
        assert_eq!(
            PAIRWISE_EXPECTED_JOINT_BY_PROGRAM
                .iter()
                .map(|(program, _)| *program)
                .collect::<BTreeSet<_>>(),
            CORPUS
                .iter()
                .map(|program| program.name)
                .collect::<BTreeSet<_>>(),
            "pairwise joint anchor must cover the exact frozen catalog"
        );
    }
    assert!(
        !prod_box_snapshot_only || diagnostic_package,
        "{} requires {}=1",
        ownership_diagnostic_package::SNAPSHOT_ONLY_ENV,
        ownership_diagnostic_package::ENV,
    );
    if ownership_yield_enabled {
        assert!(
            prod_enabled,
            "ownership-yield measurement requires CRAT_BOC1_PROD=1"
        );
        assert_eq!(
            std::env::var("CRAT_BO_REPAIR").as_deref(),
            Ok("mode_a"),
            "ownership-yield measurement requires Mode-A"
        );
        assert_eq!(
            crate::analyses::borrow_ownership::borrow_verify::RepairMode::current(),
            crate::analyses::borrow_ownership::borrow_verify::RepairMode::ModeA,
            "ownership-yield measurement repair mode drifted"
        );
        assert_eq!(
            std::env::var("CRAT_BO_L2_GUARDED_COMMITS").as_deref(),
            Ok("0"),
            "ownership-yield measurement requires L2 explicitly off"
        );
        assert!(
            !crate::analyses::borrow_ownership::l2::enabled_from_env(),
            "ownership-yield measurement resolved L2 on"
        );
        assert_eq!(
            timeout,
            Duration::from_secs(900),
            "ownership-yield BO timeout must be 900 seconds"
        );
        assert_eq!(
            prod_timeout,
            Duration::from_secs(1800),
            "ownership-yield production timeout must be 1800 seconds"
        );
        assert_eq!(
            std::env::var("CRAT_BOC1_MEM_MB").as_deref(),
            Ok("8192"),
            "ownership-yield measurement requires the 8192-MiB worker cap"
        );
        assert!(
            only.is_none(),
            "ownership-yield measurement must cover all 20 frozen programs"
        );
        assert_eq!(
            CORPUS.len(),
            20,
            "ownership-yield frozen corpus size drifted"
        );
    }
    if l2_gate {
        l2_red_gate::assert_fixtures(CORPUS);
        for name in [
            "CRAT_BO_SAFE_MONO",
            "CRAT_BO_MUT_FACTS",
            "CRAT_BO_FORK_ENGINE",
            "CRAT_NB4R_ROUTING",
        ] {
            assert!(
                std::env::var_os(name).is_none(),
                "L2 RED requires the frozen base contract with {name} unset"
            );
        }
        assert_eq!(
            crate::analyses::borrow_ownership::SafeMonoMode::current(),
            crate::analyses::borrow_ownership::SafeMonoMode::PerSite,
            "L2 RED requires the frozen per-site safety profile"
        );
        assert_eq!(
            crate::analyses::borrow_ownership::mutability_facts::MutFactsMode::current(),
            crate::analyses::borrow_ownership::mutability_facts::MutFactsMode::On,
            "L2 RED requires the frozen mutability-facts profile"
        );
        assert_eq!(
            crate::analyses::borrow_ownership::borrow_engine::ForkEngineMode::current(),
            crate::analyses::borrow_ownership::borrow_engine::ForkEngineMode::Fork,
            "L2 RED requires the frozen fork-engine profile"
        );
        assert_eq!(
            std::env::var("CRAT_BO_L2_GUARDED_COMMITS").as_deref(),
            Ok("1"),
            "L2 RED requires CRAT_BO_L2_GUARDED_COMMITS=1"
        );
        assert!(
            crate::analyses::borrow_ownership::l2::enabled_from_env(),
            "L2 RED feature flag did not resolve on"
        );
        assert_eq!(
            std::env::var("CRAT_BO_REPAIR").as_deref(),
            Ok("mode_a"),
            "L2 RED requires CRAT_BO_REPAIR=mode_a"
        );
        assert_eq!(
            crate::analyses::borrow_ownership::borrow_verify::RepairMode::current(),
            crate::analyses::borrow_ownership::borrow_verify::RepairMode::ModeA,
        );
        assert_eq!(
            std::env::var("CRAT_POINTER_DECISION_DIAGNOSTICS").as_deref(),
            Ok("raw"),
            "L2 RED requires CRAT_POINTER_DECISION_DIAGNOSTICS=raw"
        );
        assert_eq!(
            std::env::var("CRAT_BOC1_TIMEOUT_SECS").as_deref(),
            Ok("900"),
            "L2 RED requires the official 900-second worker timeout"
        );
        assert_eq!(
            timeout,
            Duration::from_secs(900),
            "L2 RED effective timeout drifted"
        );
        assert_eq!(
            std::env::var("CRAT_BOC1_MEM_MB").as_deref(),
            Ok("8192"),
            "L2 RED requires the official 8192-MiB memory cap"
        );
        assert_eq!(
            std::env::var("CRAT_BOC1_PROD").as_deref(),
            Ok("0"),
            "L2 RED must run only the Mode-A BO worker"
        );
        assert!(
            !prod_enabled,
            "L2 RED production-baseline child must be disabled"
        );
        assert!(
            only.is_none(),
            "L2 RED must not set CRAT_BOC1_PROGRAMS; run all 20 frozen programs"
        );
        assert_eq!(CORPUS.len(), 20, "L2 RED frozen corpus size drifted");
        assert_eq!(
            CORPUS.last().map(|program| program.name),
            Some("brotli"),
            "L2 RED must include brotli as the final development-boundary row"
        );
        assert!(
            CORPUS
                .iter()
                .all(|program| !is_resource_deferred(program.sloc)),
            "L2 RED cannot resource-defer any frozen rs-crown program"
        );
    }

    fs::create_dir_all(out_dir().join("logs")).expect("create out dir");
    if prod_box_snapshot_only {
        let retry_timeout = Duration::from_secs(3600);
        let mut rows = Vec::<Row>::new();
        let mut retry_queue = Vec::<CorpusProgram>::new();
        let clean_note = |note: &str| {
            note.chars()
                .map(|character| {
                    if character.is_control() {
                        '_'
                    } else {
                        character
                    }
                })
                .collect::<String>()
        };

        let record_counts = |program: &CorpusProgram,
                             outcome: &orchestrate::ChildOutcome,
                             row: &mut Row| {
            let counts = ownership_diagnostic_package::parse_pointer_diagnostics(&outcome.stderr)
                .unwrap_or_else(|error| panic!("{}: {error}", program.name));
            ownership_diagnostic_package::write_json(
                &production_box_path(program.name),
                &ownership_diagnostic_package::BoxDecisionEvidence {
                    program: program.name.to_string(),
                    counts,
                },
            )
            .unwrap_or_else(|error| panic!("{error}"));
            row.set("locals", counts.locals);
            row.set("params", counts.params);
            row.set("returns", counts.returns);
            row.set("fields", counts.fields);
            row.set(
                "total",
                counts.locals + counts.params + counts.returns + counts.fields,
            );
            row.set("d0_locals_only", counts.d0_locals);
        };

        for &program in CORPUS {
            let input = program.input_path(&root);
            assert!(input.is_file(), "missing crate root {input:?}");
            eprintln!(
                "[boc1] {}: pre-transform decision snapshot...",
                program.name
            );
            let outcome = run_child(program.name, &input, "prod-box", prod_timeout);
            let mut row = Row::default();
            row.set("program", program.name);
            row.set("first_wall_s", format!("{:.1}", outcome.wall_s));
            row.set("total_wall_s", format!("{:.1}", outcome.wall_s));
            match diagnostic_worker_disposition(&outcome.status) {
                DiagnosticWorkerDisposition::Complete => {
                    row.set("status", "ok");
                    record_counts(&program, &outcome, &mut row);
                }
                DiagnosticWorkerDisposition::ResourceDeferred => {
                    row.set("status", "resource-deferred-pending-retry");
                    row.set(
                        "note",
                        format!("{} at {}s", outcome.status, prod_timeout.as_secs()),
                    );
                    retry_queue.push(program);
                }
                DiagnosticWorkerDisposition::CorrectnessFailure => {
                    row.set("status", format!("failed-{}", outcome.status));
                    row.set("note", clean_note(&outcome.note));
                }
            }
            rows.push(row);
        }

        for program in retry_queue {
            let input = program.input_path(&root);
            eprintln!(
                "[boc1] {}: pre-transform decision snapshot retry ({}s cap)...",
                program.name,
                retry_timeout.as_secs()
            );
            let outcome = run_child_labeled(
                program.name,
                &input,
                "prod-box",
                "prod-box-retry",
                retry_timeout,
                &[],
            );
            let row = rows
                .iter_mut()
                .find(|row| row.get("program") == Some(program.name))
                .expect("pre-transform retry row");
            let first_wall_s = row
                .get("first_wall_s")
                .expect("pre-transform first wall")
                .parse::<f64>()
                .expect("numeric pre-transform first wall");
            row.set("retry_wall_s", format!("{:.1}", outcome.wall_s));
            row.set(
                "total_wall_s",
                format!("{:.1}", first_wall_s + outcome.wall_s),
            );
            match diagnostic_worker_disposition(&outcome.status) {
                DiagnosticWorkerDisposition::Complete => {
                    row.set("status", "ok-after-retry");
                    row.set("note", "completed_on_3600s_retry");
                    record_counts(&program, &outcome, row);
                }
                DiagnosticWorkerDisposition::ResourceDeferred => {
                    row.set("status", "resource-deferred-final");
                    row.set(
                        "note",
                        format!(
                            "resource wall at {}s and {} at {}s",
                            prod_timeout.as_secs(),
                            outcome.status,
                            retry_timeout.as_secs()
                        ),
                    );
                }
                DiagnosticWorkerDisposition::CorrectnessFailure => {
                    row.set("status", format!("failed-{}", outcome.status));
                    row.set("note", clean_note(&outcome.note));
                }
            }
        }

        let failures = rows
            .iter()
            .filter(|row| {
                row.get("status")
                    .map_or(true, |status| !status.starts_with("ok"))
                    && row.get("status") != Some("resource-deferred-final")
            })
            .map(|row| row.get("program").unwrap_or("unknown"))
            .collect::<Vec<_>>();
        let deferred = rows
            .iter()
            .filter(|row| row.get("status") == Some("resource-deferred-final"))
            .count();
        let covered = rows.len() - failures.len() - deferred;
        let snapshot_sha = orchestrate::git_sha();
        let snapshot_dirty = orchestrate::git_dirty();
        let total = rows
            .iter()
            .filter(|row| {
                row.get("status")
                    .is_some_and(|status| status.starts_with("ok"))
            })
            .map(|row| {
                row.get("total")
                    .expect("successful snapshot total")
                    .parse::<usize>()
                    .expect("numeric successful snapshot total")
            })
            .sum::<usize>();
        fs::write(
            out_dir().join("production-box-pre-transform-decisions.csv"),
            report::render_csv(&rows),
        )
        .expect("write pre-transform decision snapshot CSV");
        fs::write(
            out_dir().join("production-box-pre-transform-report.md"),
            format!(
                "# Production decision-layer yield\n\n\
                 - Label: decision-layer yield, PRE-transform-demotion UPPER BOUND.\n\
                 - Contract: frozen rs-crown; Mode-A; L2 off; both z3 seeds 0; serialized; \
                   1800 s / 8192 MiB first pass; one 3600 s retry.\n\
                 - Provenance: code={snapshot_sha}; dirty={snapshot_dirty}.\n\
                 - Coverage: {covered}/20; resource-deferred: {deferred}; failures: {:?}.\n\
                 - Box-family total on covered programs: {total}.\n",
                failures,
            ),
        )
        .expect("write pre-transform decision snapshot report");
        assert!(
            failures.len() <= 5,
            "pre-transform production decision snapshot failed on {} programs; \
             measurement design review required: {:?}",
            failures.len(),
            failures
        );
        println!("{}", render_report(&rows));
        return;
    }

    // Provenance guard (NB2, 2026-07-10): stamp this run's SHA into results.jsonl (line 1)
    // and move any SHA-mismatched / unstamped prior file aside so a killed sweep cannot
    // masquerade as current data. Rename, not delete — forensic trail. See the NB2 task doc.
    let sha = orchestrate::git_sha();
    let dirty = orchestrate::git_dirty();
    let unix = orchestrate::now_unix();
    if dirty {
        eprintln!("[boc1] WARNING: working tree dirty — provenance sha {sha} is approximate");
    }
    {
        let results = out_dir().join("results.jsonl");
        let first_line = results
            .is_file()
            .then(|| fs::read_to_string(&results).ok())
            .flatten()
            .and_then(|s| s.lines().next().map(|l| l.to_string()));
        if let Some(suffix) = provenance::stale_verdict(first_line.as_deref(), &sha) {
            let stale = out_dir().join(format!("results.jsonl.stale-{suffix}"));
            fs::rename(&results, &stale).expect("rename stale results.jsonl aside");
            eprintln!("[boc1] moved stale results.jsonl aside to {stale:?} (sweep sha {sha})");
        }
    }

    let mut raw_rows: Vec<Row> = Vec::new();
    let mut merged: Vec<Row> = Vec::new();
    let mut ownership_yield_rows: Vec<ownership_yield::ProgramSummary> = Vec::new();
    let mut production_failures = 0usize;
    let mut selector_retry_queue = Vec::new();
    let mut selector_resource_deferred = Vec::new();
    let mut diagnostic_retry_queue: Vec<(CorpusProgram, &'static str)> = Vec::new();

    for &program in CORPUS {
        if let Some(only) = &only
            && !only.iter().any(|p| p == program.name)
        {
            continue;
        }
        let input = program.input_path(&root);
        assert!(input.is_file(), "missing crate root {input:?}");

        let mut m = Row::default();
        m.set("program", program.name);
        m.set("dir", program.name);
        m.set("sloc", program.sloc);

        if is_resource_deferred(program.sloc) {
            m.set("status", "resource-deferred");
            m.set("note", format!("sloc_gt_brotli_{BROTLI_SLOC}"));
            eprintln!(
                "[boc1] {} ({}, {} SLOC): resource-deferred (> brotli {})",
                program.name, program.lib_root, program.sloc, BROTLI_SLOC
            );
        } else {
            eprintln!(
                "[boc1] {} ({}, {} SLOC): bo mode...",
                program.name, program.lib_root, program.sloc
            );
            let bo = run_child(program.name, &input, "bo", timeout);
            m.set("status", &bo.status);
            m.set("wall_s", format!("{:.1}", bo.wall_s));
            m.set("bo_wall_s", format!("{:.1}", bo.wall_s));
            if let Some(row) = &bo.row {
                for (k, v) in &row.0 {
                    if !matches!(k.as_str(), "program" | "mode" | "status") {
                        m.set(k, v);
                    }
                }
                raw_rows.push(row.clone());
            }
            if !bo.note.is_empty() {
                m.set("note", &bo.note);
            }

            if selector_leak_diag {
                assert_eq!(
                    bo.status, "ok",
                    "selector-leak official worker failed for {}: status={} note={}",
                    program.name, bo.status, bo.note
                );
                assert!(
                    selector_trace_path(program.name).is_file(),
                    "selector-leak official trace missing for {}",
                    program.name
                );
                eprintln!("[boc1] {}: selector-core mode...", program.name);
                let tracked = run_child(program.name, &input, "selector-core", diagnostic_timeout);
                m.set(
                    "selector_core_first_wall_s",
                    format!("{:.1}", tracked.wall_s),
                );
                m.set("selector_core_wall_s", format!("{:.1}", tracked.wall_s));
                match diagnostic_worker_disposition(&tracked.status) {
                    DiagnosticWorkerDisposition::Complete => {
                        m.set("selector_core_status", &tracked.status);
                        if let Some(row) = &tracked.row {
                            for key in [
                                "selector_core_events",
                                "selector_core_sources_final",
                                "selector_core_sinks_final",
                                "check_sat_count",
                            ] {
                                if let Some(value) = row.get(key) {
                                    m.set(&format!("tracked_{key}"), value);
                                }
                            }
                            raw_rows.push(row.clone());
                        }
                        assert!(
                            selector_evidence_path(program.name).is_file(),
                            "selector-leak core evidence missing for {}",
                            program.name
                        );
                    }
                    DiagnosticWorkerDisposition::ResourceDeferred => {
                        selector_retry_queue.push(program);
                        m.set("selector_core_status", "resource-deferred-pending-retry");
                        m.set(
                            "selector_core_note",
                            format!(
                                "family-tracked worker hit {} at {}s",
                                tracked.status,
                                diagnostic_timeout.as_secs()
                            ),
                        );
                    }
                    DiagnosticWorkerDisposition::CorrectnessFailure => {
                        panic!(
                            "selector-leak tracked worker failed for {}: status={} note={}",
                            program.name, tracked.status, tracked.note
                        );
                    }
                }
            }

            if diagnostic_package || pairwise_probe {
                assert_eq!(
                    bo.status, "ok",
                    "necessity diagnostic official worker failed for {}: status={} note={}",
                    program.name, bo.status, bo.note
                );
                assert!(
                    selector_trace_path(program.name).is_file(),
                    "necessity diagnostic official trace missing for {}",
                    program.name
                );

                eprintln!("[boc1] {}: selector-necessity mode...", program.name);
                let necessity = run_child(
                    program.name,
                    &input,
                    "selector-necessity",
                    diagnostic_timeout,
                );
                m.set("necessity_first_wall_s", format!("{:.1}", necessity.wall_s));
                m.set("necessity_wall_s", format!("{:.1}", necessity.wall_s));
                match diagnostic_worker_disposition(&necessity.status) {
                    DiagnosticWorkerDisposition::Complete => {
                        m.set("necessity_status", "ok");
                        let row = necessity
                            .row
                            .as_ref()
                            .expect("necessity worker completed without row");
                        for (source, target) in [
                            ("necessity_sources", "necessity_sources"),
                            ("necessity_joint", "necessity_joint"),
                            ("necessity_pair_recovered", "necessity_pair_recovered"),
                            ("necessity_no_pair", "necessity_no_pair"),
                            ("check_sat_count", "necessity_check_sat_count"),
                        ] {
                            if let Some(value) = row.get(source) {
                                m.set(target, value);
                            }
                        }
                        raw_rows.push(row.clone());
                        assert!(
                            necessity_evidence_path(program.name).is_file(),
                            "necessity evidence missing for {}",
                            program.name
                        );
                    }
                    DiagnosticWorkerDisposition::ResourceDeferred => {
                        diagnostic_retry_queue.push((program, "selector-necessity"));
                        m.set("necessity_status", "resource-deferred-pending-retry");
                        m.set(
                            "necessity_note",
                            format!("{} at {}s", necessity.status, diagnostic_timeout.as_secs()),
                        );
                    }
                    DiagnosticWorkerDisposition::CorrectnessFailure => {
                        panic!(
                            "necessity worker correctness failure for {}: status={} note={}",
                            program.name, necessity.status, necessity.note
                        );
                    }
                }
            }

            if diagnostic_package {
                eprintln!("[boc1] {}: prod-precision mode...", program.name);
                let precision = run_child(program.name, &input, "prod-precision", prod_timeout);
                m.set(
                    "prod_precision_first_wall_s",
                    format!("{:.1}", precision.wall_s),
                );
                m.set("prod_precision_wall_s", format!("{:.1}", precision.wall_s));
                match diagnostic_worker_disposition(&precision.status) {
                    DiagnosticWorkerDisposition::Complete => {
                        m.set("prod_precision_status", "ok");
                        let row = precision
                            .row
                            .as_ref()
                            .expect("production precision worker completed without row");
                        for key in [
                            "t_andersen_s",
                            "t_output_params_s",
                            "t_ownership_s",
                            "t_solidify_s",
                            "n_own_prod",
                            "n_own_prod_fields",
                        ] {
                            if let Some(value) = row.get(key) {
                                m.set(&format!("prod_precision_{key}"), value);
                            }
                        }
                        raw_rows.push(row.clone());
                        assert!(
                            production_precision_path(program.name).is_file(),
                            "production precision evidence missing for {}",
                            program.name
                        );
                    }
                    DiagnosticWorkerDisposition::ResourceDeferred => {
                        diagnostic_retry_queue.push((program, "prod-precision"));
                        m.set("prod_precision_status", "resource-deferred-pending-retry");
                        m.set(
                            "prod_precision_note",
                            format!("{} at {}s", precision.status, prod_timeout.as_secs()),
                        );
                    }
                    DiagnosticWorkerDisposition::CorrectnessFailure => {
                        m.set(
                            "prod_precision_status",
                            format!("failed-{}", precision.status),
                        );
                        m.set("prod_precision_note", &precision.note);
                    }
                }

                eprintln!("[boc1] {}: prod-box mode...", program.name);
                let boxes = run_child(program.name, &input, "prod-box", prod_timeout);
                m.set("prod_box_first_wall_s", format!("{:.1}", boxes.wall_s));
                m.set("prod_box_wall_s", format!("{:.1}", boxes.wall_s));
                match diagnostic_worker_disposition(&boxes.status) {
                    DiagnosticWorkerDisposition::Complete => {
                        m.set("prod_box_status", "ok");
                        let counts =
                            ownership_diagnostic_package::parse_pointer_diagnostics(&boxes.stderr)
                                .unwrap_or_else(|error| panic!("{}: {error}", program.name));
                        ownership_diagnostic_package::write_json(
                            &production_box_path(program.name),
                            &ownership_diagnostic_package::BoxDecisionEvidence {
                                program: program.name.to_string(),
                                counts,
                            },
                        )
                        .unwrap_or_else(|error| panic!("{error}"));
                        m.set("prod_box_locals", counts.locals);
                        m.set("prod_box_params", counts.params);
                        m.set("prod_box_returns", counts.returns);
                        m.set("prod_box_fields", counts.fields);
                        m.set("prod_box_d0_locals", counts.d0_locals);
                        if let Some(row) = &boxes.row {
                            raw_rows.push(row.clone());
                        }
                    }
                    DiagnosticWorkerDisposition::ResourceDeferred => {
                        diagnostic_retry_queue.push((program, "prod-box"));
                        m.set("prod_box_status", "resource-deferred-pending-retry");
                        m.set(
                            "prod_box_note",
                            format!("{} at {}s", boxes.status, prod_timeout.as_secs()),
                        );
                    }
                    DiagnosticWorkerDisposition::CorrectnessFailure => {
                        m.set("prod_box_status", format!("failed-{}", boxes.status));
                        m.set("prod_box_note", &boxes.note);
                    }
                }
            }

            let bo_records = ownership_yield_enabled.then(|| {
                assert_eq!(
                    bo.status, "ok",
                    "ownership-yield BO worker failed for {}: status={} note={}",
                    program.name, bo.status, bo.note
                );
                let row = bo.row.as_ref().unwrap_or_else(|| {
                    panic!("ownership-yield BO row missing for {}", program.name)
                });
                let records =
                    ownership_yield::read_worker_snapshot(&yield_snapshot_path(program.name, "bo"))
                        .unwrap_or_else(|error| panic!("{}: {error}", program.name));
                let counts = ownership_yield::side_counts(&records);
                let row_n_own = row
                    .get("n_own")
                    .unwrap_or_else(|| panic!("{} BO row missing n_own", program.name))
                    .parse::<usize>()
                    .unwrap_or_else(|error| {
                        panic!("{} BO n_own is not numeric: {error}", program.name)
                    });
                assert_eq!(
                    counts.total_owning, row_n_own,
                    "{} BO snapshot n_own disagrees with the official row",
                    program.name
                );
                records
            });

            if prod_enabled {
                let prod_mode = if ownership_yield_enabled {
                    "prod-own"
                } else {
                    "prod"
                };
                eprintln!("[boc1] {}: {prod_mode} mode...", program.name);
                let prod = run_child(program.name, &input, prod_mode, prod_timeout);
                m.set("prod_status", &prod.status);
                m.set("prod_wall_s", format!("{:.1}", prod.wall_s));
                if let Some(row) = &prod.row {
                    let keys: &[&str] = if ownership_yield_enabled {
                        &[
                            "t_andersen_s",
                            "t_output_params_s",
                            "t_ownership_s",
                            "t_solidify_s",
                            "n_own_prod",
                            "n_own_prod_fields",
                            "n_own_prod_forced_output",
                            "n_own_prod_without_forced",
                        ]
                    } else {
                        &["n_slots_d0", "n_demoted_prod", "n_ref_prod", "t_prod_s"]
                    };
                    for key in keys {
                        if let Some(v) = row.get(key) {
                            m.set(key, v);
                        }
                    }
                    raw_rows.push(row.clone());
                }

                if ownership_yield_enabled {
                    let bo_records = bo_records.as_ref().expect("yield BO records");
                    let bo_counts = ownership_yield::side_counts(bo_records);
                    let parse_time = |key: &str| {
                        prod.row
                            .as_ref()
                            .and_then(|row| row.get(key))
                            .and_then(|value| value.parse::<f64>().ok())
                    };
                    let (production_failure, comparison) = if prod.status == "ok" {
                        let production_records = ownership_yield::read_worker_snapshot(
                            &yield_snapshot_path(program.name, "prod-own"),
                        )
                        .unwrap_or_else(|error| panic!("{}: {error}", program.name));
                        let comparison = ownership_yield::compare(bo_records, &production_records)
                            .unwrap_or_else(|error| panic!("{}: {error}", program.name));
                        m.set("bo_only_owning", comparison.bo_only_owning.len());
                        m.set(
                            "production_only_owning",
                            comparison.production_only_owning.len(),
                        );
                        m.set("bo_universe_only", comparison.bo_universe_only.len());
                        m.set(
                            "production_universe_only",
                            comparison.production_universe_only.len(),
                        );
                        (None, Some(comparison))
                    } else {
                        production_failures += 1;
                        let detail = prod
                            .row
                            .as_ref()
                            .and_then(|row| row.get("err"))
                            .map(|error| format!("{}:{error}", prod.status))
                            .unwrap_or_else(|| prod.status.clone());
                        m.set(
                            "prod_failure",
                            format!("{detail}_cap_{}s", prod_timeout.as_secs()),
                        );
                        (Some(detail), None)
                    };
                    ownership_yield_rows.push(ownership_yield::ProgramSummary {
                        program: program.name.to_string(),
                        bo_status: bo.status.clone(),
                        production_status: prod.status.clone(),
                        bo_wall_s: bo.wall_s,
                        production_wall_s: Some(prod.wall_s),
                        production_andersen_s: parse_time("t_andersen_s"),
                        production_output_params_s: parse_time("t_output_params_s"),
                        production_ownership_s: parse_time("t_ownership_s"),
                        production_solidify_s: parse_time("t_solidify_s"),
                        production_cap_s: prod_timeout.as_secs(),
                        production_failure,
                        bo: bo_counts,
                        comparison,
                    });
                } else if let (Some(bo_ref), Some(prod_ref)) = (
                    m.get("n_ref_d0").and_then(|v| v.parse::<i64>().ok()),
                    m.get("n_ref_prod").and_then(|v| v.parse::<i64>().ok()),
                ) {
                    m.set("d_ref_d0", bo_ref - prod_ref);
                }
            }
        }

        eprintln!("[boc1] {}: {}", program.name, report::to_kv_line(&m));
        merged.push(m);

        // Persist incrementally so partial sweeps still leave artifacts. Line 1 is the
        // provenance stamp (guard above); data rows follow.
        let mut jsonl = provenance::line(&sha, dirty, unix) + "\n";
        for r in &raw_rows {
            jsonl.push_str(&report::to_json_line(r));
            jsonl.push('\n');
        }
        fs::write(out_dir().join("results.jsonl"), jsonl).expect("write jsonl");
        fs::write(out_dir().join("results.csv"), report::render_csv(&merged)).expect("write csv");
        fs::write(out_dir().join("report.md"), render_report(&merged)).expect("write report");
        if ownership_yield_enabled {
            fs::write(
                out_dir().join("ownership-yield-summary.csv"),
                ownership_yield::render_summary_csv(&ownership_yield_rows),
            )
            .expect("write ownership-yield summary");
            fs::write(
                out_dir().join("ownership-yield-deltas.tsv"),
                ownership_yield::render_deltas_tsv(&ownership_yield_rows),
            )
            .expect("write ownership-yield deltas");
            fs::write(
                out_dir().join("ownership-yield-report.md"),
                ownership_yield::render_markdown(&ownership_yield_rows),
            )
            .expect("write ownership-yield report");
            assert!(
                production_failures <= 5,
                "ownership-yield production failed on {production_failures}/20 programs; \
                 measurement design review required"
            );
        }
    }

    if selector_leak_diag {
        let retry_timeout = Duration::from_secs(3600);
        for program in selector_retry_queue {
            let input = program.input_path(&root);
            eprintln!(
                "[boc1] {}: selector-core retry ({}s cap)...",
                program.name,
                retry_timeout.as_secs()
            );
            let tracked = run_child_labeled(
                program.name,
                &input,
                "selector-core",
                "selector-core-retry",
                retry_timeout,
                &[],
            );
            let m = merged
                .iter_mut()
                .find(|row| row.get("program") == Some(program.name))
                .unwrap_or_else(|| panic!("selector retry row missing for {}", program.name));
            let first_wall = m
                .get("selector_core_first_wall_s")
                .and_then(|wall| wall.parse::<f64>().ok())
                .expect("selector first-attempt wall time");
            m.set(
                "selector_core_retry_wall_s",
                format!("{:.1}", tracked.wall_s),
            );
            m.set(
                "selector_core_wall_s",
                format!("{:.1}", first_wall + tracked.wall_s),
            );
            match diagnostic_worker_disposition(&tracked.status) {
                DiagnosticWorkerDisposition::Complete => {
                    m.set("selector_core_status", "ok-after-retry");
                    m.set("selector_core_note", "completed_on_3600s_retry");
                    if let Some(row) = &tracked.row {
                        for key in [
                            "selector_core_events",
                            "selector_core_sources_final",
                            "selector_core_sinks_final",
                            "check_sat_count",
                        ] {
                            if let Some(value) = row.get(key) {
                                m.set(&format!("tracked_{key}"), value);
                            }
                        }
                        raw_rows.push(row.clone());
                    }
                    assert!(
                        selector_evidence_path(program.name).is_file(),
                        "selector-leak retry evidence missing for {}",
                        program.name
                    );
                }
                DiagnosticWorkerDisposition::ResourceDeferred => {
                    selector_resource_deferred.push(program.name);
                    m.set("selector_core_status", "resource-deferred-tracked");
                    m.set(
                        "selector_core_note",
                        format!(
                            "family-tracked worker hit {} at 1800s and {} at 3600s",
                            m.get("selector_core_note").unwrap_or("resource-wall"),
                            tracked.status
                        ),
                    );
                }
                DiagnosticWorkerDisposition::CorrectnessFailure => {
                    panic!(
                        "selector-leak tracked retry failed for {}: status={} note={}",
                        program.name, tracked.status, tracked.note
                    );
                }
            }

            let mut jsonl = provenance::line(&sha, dirty, unix) + "\n";
            for row in &raw_rows {
                jsonl.push_str(&report::to_json_line(row));
                jsonl.push('\n');
            }
            fs::write(out_dir().join("results.jsonl"), jsonl).expect("write retry jsonl");
            fs::write(out_dir().join("results.csv"), report::render_csv(&merged))
                .expect("write retry csv");
            fs::write(out_dir().join("report.md"), render_report(&merged))
                .expect("write retry report");
        }
    }

    if diagnostic_package || pairwise_probe {
        let retry_timeout = Duration::from_secs(3600);
        for (program, mode) in diagnostic_retry_queue {
            let input = program.input_path(&root);
            let label = format!("{mode}-retry");
            eprintln!(
                "[boc1] {}: {mode} retry ({}s cap)...",
                program.name,
                retry_timeout.as_secs()
            );
            let retried =
                run_child_labeled(program.name, &input, mode, &label, retry_timeout, &[]);
            let m = merged
                .iter_mut()
                .find(|row| row.get("program") == Some(program.name))
                .unwrap_or_else(|| panic!("diagnostic retry row missing for {}", program.name));
            let prefix = match mode {
                "selector-necessity" => "necessity",
                "prod-precision" => "prod_precision",
                "prod-box" => "prod_box",
                _ => unreachable!("unknown diagnostic retry mode"),
            };
            let first_wall = m
                .get(&format!("{prefix}_first_wall_s"))
                .and_then(|wall| wall.parse::<f64>().ok())
                .expect("diagnostic first-attempt wall time");
            m.set(
                &format!("{prefix}_retry_wall_s"),
                format!("{:.1}", retried.wall_s),
            );
            m.set(
                &format!("{prefix}_wall_s"),
                format!("{:.1}", first_wall + retried.wall_s),
            );
            match diagnostic_worker_disposition(&retried.status) {
                DiagnosticWorkerDisposition::Complete => {
                    m.set(&format!("{prefix}_status"), "ok-after-retry");
                    m.set(&format!("{prefix}_note"), "completed_on_3600s_retry");
                    match mode {
                        "selector-necessity" => {
                            assert!(
                                necessity_evidence_path(program.name).is_file(),
                                "necessity retry evidence missing for {}",
                                program.name
                            );
                            let row = retried
                                .row
                                .as_ref()
                                .expect("necessity retry completed without row");
                            for (source, target) in [
                                ("necessity_sources", "necessity_sources"),
                                ("necessity_joint", "necessity_joint"),
                                ("necessity_pair_recovered", "necessity_pair_recovered"),
                                ("necessity_no_pair", "necessity_no_pair"),
                                ("check_sat_count", "necessity_check_sat_count"),
                            ] {
                                if let Some(value) = row.get(source) {
                                    m.set(target, value);
                                }
                            }
                        }
                        "prod-precision" => {
                            assert!(
                                production_precision_path(program.name).is_file(),
                                "production precision retry evidence missing for {}",
                                program.name
                            );
                            let row = retried
                                .row
                                .as_ref()
                                .expect("production precision retry completed without row");
                            for key in [
                                "t_andersen_s",
                                "t_output_params_s",
                                "t_ownership_s",
                                "t_solidify_s",
                                "n_own_prod",
                                "n_own_prod_fields",
                            ] {
                                if let Some(value) = row.get(key) {
                                    m.set(&format!("prod_precision_{key}"), value);
                                }
                            }
                        }
                        "prod-box" => {
                            let counts = ownership_diagnostic_package::parse_pointer_diagnostics(
                                &retried.stderr,
                            )
                            .unwrap_or_else(|error| panic!("{}: {error}", program.name));
                            ownership_diagnostic_package::write_json(
                                &production_box_path(program.name),
                                &ownership_diagnostic_package::BoxDecisionEvidence {
                                    program: program.name.to_string(),
                                    counts,
                                },
                            )
                            .unwrap_or_else(|error| panic!("{error}"));
                            m.set("prod_box_locals", counts.locals);
                            m.set("prod_box_params", counts.params);
                            m.set("prod_box_returns", counts.returns);
                            m.set("prod_box_fields", counts.fields);
                            m.set("prod_box_d0_locals", counts.d0_locals);
                        }
                        _ => unreachable!(),
                    }
                    if let Some(row) = &retried.row {
                        raw_rows.push(row.clone());
                    }
                }
                DiagnosticWorkerDisposition::ResourceDeferred => {
                    m.set(&format!("{prefix}_status"), "resource-deferred-final");
                    m.set(
                        &format!("{prefix}_note"),
                        format!(
                            "resource wall at {}s and {} at 3600s",
                            diagnostic_timeout.as_secs(),
                            retried.status
                        ),
                    );
                }
                DiagnosticWorkerDisposition::CorrectnessFailure => {
                    if mode == "selector-necessity" {
                        panic!(
                            "necessity retry correctness failure for {}: status={} note={}",
                            program.name, retried.status, retried.note
                        );
                    }
                    m.set(
                        &format!("{prefix}_status"),
                        format!("failed-{}", retried.status),
                    );
                    m.set(&format!("{prefix}_note"), &retried.note);
                }
            }
        }
    }

    if pairwise_probe {
        let parse_total = |key: &str| {
            merged
                .iter()
                .map(|row| {
                    row.get(key)
                        .unwrap_or_else(|| panic!("pairwise row missing {key}"))
                        .parse::<usize>()
                        .unwrap_or_else(|error| panic!("pairwise {key} is not numeric: {error}"))
                })
                .sum::<usize>()
        };
        assert_eq!(merged.len(), 20, "pairwise sweep must cover 20 programs");
        assert!(
            merged.iter().all(|row| row.get("status") == Some("ok")),
            "pairwise official worker declined"
        );
        assert_eq!(parse_total("n_ref"), 52_810);
        assert_eq!(parse_total("n_own"), 230);
        assert_eq!(parse_total("sources_leaked_sel"), 114);
        assert_eq!(parse_total("sinks_leaked"), 170);

        let expected_joint = BTreeMap::from(PAIRWISE_EXPECTED_JOINT_BY_PROGRAM);
        assert_eq!(
            expected_joint.values().sum::<usize>(),
            63,
            "registered joint-row distribution must sum to 63"
        );

        let mut records = Vec::<NecessityEvidence>::new();
        let mut deferred_programs = Vec::new();
        let mut covered_joint_by_program = BTreeMap::<&str, usize>::new();
        for program in CORPUS {
            let row = merged
                .iter()
                .find(|row| row.get("program") == Some(program.name))
                .expect("pairwise program row");
            if row
                .get("necessity_status")
                .is_some_and(|status| status.starts_with("ok"))
            {
                let mut program_records: Vec<NecessityEvidence> =
                    ownership_diagnostic_package::read_json(&necessity_evidence_path(program.name))
                        .unwrap_or_else(|error| panic!("{error}"));
                let covered_joint = program_records
                    .iter()
                    .filter(|record| {
                        record.causal_bucket
                            == ownership_diagnostic_package::CausalBucket::JointNoSingleFamilyNecessity
                    })
                    .count();
                assert_eq!(
                    covered_joint, expected_joint[program.name],
                    "{} joint-row anchor diverged",
                    program.name
                );
                covered_joint_by_program.insert(program.name, covered_joint);
                records.append(&mut program_records);
            } else {
                assert_eq!(
                    row.get("necessity_status"),
                    Some("resource-deferred-final"),
                    "{} necessity ended in a non-resource failure",
                    program.name
                );
                covered_joint_by_program.insert(program.name, 0);
                deferred_programs.push(program.name);
            }
        }
        records.sort_by(|left, right| {
            left.program
                .cmp(&right.program)
                .then_with(|| left.selector_key.cmp(&right.selector_key))
        });
        let programs = CORPUS
            .iter()
            .map(|program| program.name)
            .collect::<Vec<_>>();
        let summary = ownership_diagnostic_package::summarize_pair_removals(&records, &programs);
        let deferred_joint = deferred_programs
            .iter()
            .map(|program| expected_joint[program])
            .sum::<usize>();
        assert_eq!(
            summary.joint_rows + deferred_joint,
            63,
            "covered and resource-deferred joint rows must reconcile to 63"
        );
        let completed_outcomes = records
            .iter()
            .filter_map(|record| record.pair_removal.as_ref())
            .map(|evidence| evidence.outcomes.len())
            .sum::<usize>();
        assert_eq!(
            completed_outcomes,
            summary.joint_rows * 10,
            "every covered joint row must contain all ten actual pair solves"
        );
        if deferred_programs.is_empty() {
            assert_eq!(summary.joint_rows, 63);
            assert_eq!(completed_outcomes, 630);
        }

        fs::write(
            out_dir().join("selector-pair-necessity.csv"),
            &summary.selector_csv,
        )
        .expect("write per-selector pair necessity");
        fs::write(out_dir().join("pair-frequency.csv"), &summary.frequency_csv)
            .expect("write pair frequency");
        fs::write(
            out_dir().join("pair-program-crosstab.csv"),
            &summary.program_csv,
        )
        .expect("write pair/program cross-tab");
        fs::write(out_dir().join("no-pair-suffices.csv"), &summary.no_pair_csv)
            .expect("write no-pair bucket");

        let mut program_status_csv = String::from(
            "program,expected_joint_rows,covered_joint_rows,status,official_wall_s,\
             necessity_first_wall_s,necessity_retry_wall_s,necessity_total_wall_s\n",
        );
        for row in &merged {
            let program = row.get("program").expect("pairwise status program");
            program_status_csv.push_str(&format!(
                "{program},{},{},{},{},{},{},{}\n",
                expected_joint[program],
                covered_joint_by_program[program],
                row.get("necessity_status").unwrap_or("missing"),
                row.get("bo_wall_s").unwrap_or("-"),
                row.get("necessity_first_wall_s").unwrap_or("-"),
                row.get("necessity_retry_wall_s").unwrap_or("-"),
                row.get("necessity_wall_s").unwrap_or("-"),
            ));
        }
        fs::write(
            out_dir().join("pairwise-program-status.csv"),
            &program_status_csv,
        )
        .expect("write pairwise program status");

        let dominance = ownership_diagnostic_package::dominant_pair_summary(
            &summary.pair_frequency,
            deferred_joint == 0,
        );
        let dominant_pairs = dominance
            .as_ref()
            .map(|(pairs, _)| pairs.clone())
            .unwrap_or_default();
        let representatives_enabled = !dominant_pairs.is_empty();
        let dominant_coverage = |record: &NecessityEvidence| {
            record
                .pair_removal
                .as_ref()
                .expect("representative joint row")
                .minimal_sat_pairs
                .intersection(&dominant_pairs)
                .count()
        };
        let mut joint_indices = records
            .iter()
            .enumerate()
            .filter(|(_, record)| record.pair_removal.is_some())
            .map(|(index, _)| index)
            .collect::<Vec<_>>();
        joint_indices.sort_by(|left, right| {
            dominant_coverage(&records[*right])
                .cmp(&dominant_coverage(&records[*left]))
                .then_with(|| records[*left].program.cmp(&records[*right].program))
                .then_with(|| {
                    records[*left]
                        .selector_key
                        .cmp(&records[*right].selector_key)
                })
        });

        let mut selected_indices = Vec::new();
        if representatives_enabled {
            let lil_index = joint_indices
                .iter()
                .copied()
                .filter(|index| records[*index].program == "lil")
                .max_by_key(|index| dominant_coverage(&records[*index]))
                .expect("representative set must include one lil joint row");
            selected_indices.push(lil_index);
        }
        while representatives_enabled
            && selected_indices.len() < 3
            && selected_indices.len() < joint_indices.len()
        {
            let selected_programs = selected_indices
                .iter()
                .map(|index| records[*index].program.as_str())
                .collect::<BTreeSet<_>>();
            let candidate = joint_indices
                .iter()
                .copied()
                .filter(|index| !selected_indices.contains(index))
                .max_by(|left, right| {
                    let left_distinct =
                        !selected_programs.contains(records[*left].program.as_str());
                    let right_distinct =
                        !selected_programs.contains(records[*right].program.as_str());
                    left_distinct
                        .cmp(&right_distinct)
                        .then_with(|| {
                            dominant_coverage(&records[*left])
                                .cmp(&dominant_coverage(&records[*right]))
                        })
                        .then_with(|| records[*right].program.cmp(&records[*left].program))
                        .then_with(|| {
                            records[*right]
                                .selector_key
                                .cmp(&records[*left].selector_key)
                        })
                });
            let Some(candidate) = candidate else {
                break;
            };
            selected_indices.push(candidate);
        }
        if representatives_enabled {
            assert_eq!(
                selected_indices.len(),
                3,
                "complete 63-row coverage must yield three representatives"
            );
            assert!(
                selected_indices
                    .iter()
                    .any(|index| records[*index].program == "lil"),
                "representative set lost the mandatory lil row"
            );
        } else {
            assert!(
                selected_indices.is_empty(),
                "partial or all-no-pair coverage must not produce dominance representatives"
            );
        }

        let mut representative_tsv = String::from(
            "program\tselector_key\tepoch\tselector_index\tminimal_pairs\tdominant_pairs\t\
             raw_families\tminimized_families\traw_labels\tminimized_labels\tcommit_origins\t\
             first_wall_s\tretry_wall_s\ttotal_wall_s\tstatus\tevidence_path\n",
        );
        for index in selected_indices {
            let record = &records[index];
            let corpus_program = CORPUS
                .iter()
                .find(|program| program.name == record.program)
                .expect("representative program belongs to corpus");
            let input = corpus_program.input_path(&root);
            let mode = format!("selector-detail-{}-{}", record.epoch, record.selector_index);
            eprintln!(
                "[boc1] {}: {mode} pairwise representative...",
                record.program
            );
            let first = run_child(&record.program, &input, &mode, diagnostic_timeout);
            let first_wall_s = first.wall_s;
            let retry_wall_s = match diagnostic_worker_disposition(&first.status) {
                DiagnosticWorkerDisposition::Complete => None,
                DiagnosticWorkerDisposition::ResourceDeferred => {
                    eprintln!(
                        "[boc1] {}: {mode} representative retry (3600s cap)...",
                        record.program
                    );
                    let retry = run_child_labeled(
                        &record.program,
                        &input,
                        &mode,
                        &format!("{mode}-retry"),
                        Duration::from_secs(3600),
                        &[],
                    );
                    match diagnostic_worker_disposition(&retry.status) {
                        DiagnosticWorkerDisposition::Complete => Some(retry.wall_s),
                        DiagnosticWorkerDisposition::ResourceDeferred => {
                            representative_tsv.push_str(&format!(
                                "{}\t{}\t{}\t{}\t{}\t{}\t-\t-\t-\t-\t-\t{:.1}\t{:.1}\t{:.1}\t\
                                 resource-deferred\t-\n",
                                record.program,
                                record.selector_key,
                                record.epoch,
                                record.selector_index,
                                record
                                    .pair_removal
                                    .as_ref()
                                    .expect("representative pair evidence")
                                    .minimal_sat_pairs
                                    .iter()
                                    .map(ownership_diagnostic_package::FamilyPair::label)
                                    .collect::<Vec<_>>()
                                    .join(";"),
                                record
                                    .pair_removal
                                    .as_ref()
                                    .expect("representative pair evidence")
                                    .minimal_sat_pairs
                                    .intersection(&dominant_pairs)
                                    .map(ownership_diagnostic_package::FamilyPair::label)
                                    .collect::<Vec<_>>()
                                    .join(";"),
                                first_wall_s,
                                retry.wall_s,
                                first_wall_s + retry.wall_s,
                            ));
                            continue;
                        }
                        DiagnosticWorkerDisposition::CorrectnessFailure => {
                            panic!(
                                "{} representative retry failed: status={} note={}",
                                record.program, retry.status, retry.note
                            );
                        }
                    }
                }
                DiagnosticWorkerDisposition::CorrectnessFailure => {
                    panic!(
                        "{} representative failed: status={} note={}",
                        record.program, first.status, first.note
                    );
                }
            };
            let path = selector_detail_path(
                &record.program,
                &format!("{}-{}", record.epoch, record.selector_index),
            );
            assert!(
                path.is_file(),
                "pairwise representative evidence missing: {}",
                path.display()
            );
            let detail = selector_leak_diagnosis::read_detail_evidence(&path)
                .unwrap_or_else(|error| panic!("{error}"));
            assert_eq!(detail.program, record.program);
            assert_eq!(detail.selector_key, record.selector_key);
            representative_tsv.push_str(&format!(
                "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{first_wall_s:.1}\t{}\t{:.1}\t\
                 ok\t{}\n",
                record.program,
                record.selector_key,
                record.epoch,
                record.selector_index,
                record
                    .pair_removal
                    .as_ref()
                    .expect("representative pair evidence")
                    .minimal_sat_pairs
                    .iter()
                    .map(ownership_diagnostic_package::FamilyPair::label)
                    .collect::<Vec<_>>()
                    .join(";"),
                record
                    .pair_removal
                    .as_ref()
                    .expect("representative pair evidence")
                    .minimal_sat_pairs
                    .intersection(&dominant_pairs)
                    .map(ownership_diagnostic_package::FamilyPair::label)
                    .collect::<Vec<_>>()
                    .join(";"),
                detail
                    .raw_families
                    .iter()
                    .cloned()
                    .collect::<Vec<_>>()
                    .join("+"),
                detail
                    .minimized_families
                    .iter()
                    .cloned()
                    .collect::<Vec<_>>()
                    .join("+"),
                serde_json::to_string(&detail.raw_labels).expect("encode raw labels"),
                serde_json::to_string(&detail.minimized_labels).expect("encode minimized labels"),
                serde_json::to_string(&detail.commit_origins).expect("encode commit origins"),
                retry_wall_s
                    .map(|wall| format!("{wall:.1}"))
                    .unwrap_or_else(|| "-".to_string()),
                first_wall_s + retry_wall_s.unwrap_or(0.0),
                path.display(),
            ));
        }
        fs::write(
            out_dir().join("pairwise-representatives.tsv"),
            &representative_tsv,
        )
        .expect("write pairwise representative index");

        let dominance_report = match &dominance {
            None => "not computed because pair coverage is partial".to_string(),
            Some((pairs, 0)) if pairs.is_empty() => {
                "none; every pair frequency is zero".to_string()
            }
            Some((pairs, count)) => format!(
                "{} ({count} rows each)",
                pairs
                    .iter()
                    .map(ownership_diagnostic_package::FamilyPair::label)
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        };
        let interpretation = if dominance.is_some() {
            "Pair necessity localizes coupling structure and prices candidate repairs. It does \
             not authorize tuning; kind-coupling through equality/version paths remains a \
             hypothesis to test against the recorded chains."
        } else {
            "Dominance interpretation is withheld because final pair coverage is partial. Raw \
             covered-row tables and resource deferrals remain recorded."
        };
        fs::write(
            out_dir().join("pairwise-family-removal-report.md"),
            format!(
                "# Pairwise family-removal probing\n\n\
                 - Contract: Mode-A, L2 off, smt.random_seed=0, sat.random_seed=0, \
                   official and first-pass diagnostic cap 900 s, one serialized 3600 s retry, \
                   8192 MiB, serialized.\n\
                 - Baseline: 20/20 accept; n_ref=52,810; n_own=230; \
                   sources leaked=114/144; sinks leaked=170/206.\n\
                 - Joint rows: {}/63 covered; {} resource-deferred. Completed actual pair solves: \
                   {completed_outcomes}/630.\n\
                 - Pair recovery: {} rows have at least one SAT pair; {} rows have no SAT pair.\n\
                 - Inclusion-minimality: all singleton removals for these rows were already UNSAT, \
                   so every SAT pair is inclusion-minimal.\n\
                 - Dominant pair(s): {dominance_report}.\n\
                 - Interpretation: {interpretation}\n\n\
                 ## Pair frequency\n\n```csv\n{}```\n\n\
                 ## Pair × program\n\n```csv\n{}```\n\n\
                 ## Program status\n\n```csv\n{program_status_csv}```\n\n\
                 ## No-pair bucket\n\n```csv\n{}```\n\n\
                 Representative tracked chains are supplementary explanations only; untracked \
                 pair solves are authoritative. See `pairwise-representatives.tsv` and \
                 `selector-details/`.\n",
                summary.joint_rows,
                deferred_joint,
                summary.recovered_rows,
                summary.no_pair_rows,
                summary.frequency_csv,
                summary.program_csv,
                summary.no_pair_csv,
            ),
        )
        .expect("write pairwise report");

        let mut jsonl = provenance::line(&sha, dirty, unix) + "\n";
        for row in &raw_rows {
            jsonl.push_str(&report::to_json_line(row));
            jsonl.push('\n');
        }
        fs::write(out_dir().join("results.jsonl"), jsonl).expect("write pairwise jsonl");
        fs::write(out_dir().join("results.csv"), report::render_csv(&merged))
            .expect("write pairwise csv");
        fs::write(out_dir().join("report.md"), render_report(&merged))
            .expect("write pairwise corpus report");
    }

    if selector_leak_diag {
        let parse_total = |key: &str| {
            merged
                .iter()
                .map(|row| {
                    row.get(key)
                        .unwrap_or_else(|| panic!("selector-leak row missing {key}"))
                        .parse::<usize>()
                        .unwrap_or_else(|error| {
                            panic!("selector-leak {key} is not numeric: {error}")
                        })
                })
                .sum::<usize>()
        };
        assert_eq!(
            merged.len(),
            20,
            "selector-leak sweep must cover 20 programs"
        );
        assert!(
            merged.iter().all(|row| row.get("status") == Some("ok")),
            "selector-leak official worker declined"
        );
        assert_eq!(parse_total("n_ref"), 52_810);
        assert_eq!(parse_total("n_own"), 230);
        assert_eq!(parse_total("sources_leaked_sel"), 114);
        assert_eq!(parse_total("sinks_leaked"), 170);

        let mut evidence = Vec::new();
        for program in CORPUS {
            if selector_resource_deferred.contains(&program.name) {
                continue;
            }
            evidence.extend(
                selector_leak_diagnosis::read_core_evidence(&selector_evidence_path(program.name))
                    .unwrap_or_else(|error| panic!("{error}")),
            );
        }
        let source_records = selector_leak_diagnosis::final_records(
            &evidence,
            selector_leak_diagnosis::SelectorClass::Source,
        )
        .unwrap_or_else(|error| panic!("{error}"));
        let sink_records = selector_leak_diagnosis::final_records(
            &evidence,
            selector_leak_diagnosis::SelectorClass::Sink,
        )
        .unwrap_or_else(|error| panic!("{error}"));
        let deferred_sources = selector_resource_deferred
            .iter()
            .map(|program| {
                merged
                    .iter()
                    .find(|row| row.get("program") == Some(*program))
                    .and_then(|row| row.get("sources_leaked_sel"))
                    .unwrap_or_else(|| panic!("deferred {program} row lacks sources_leaked_sel"))
                    .parse::<usize>()
                    .unwrap_or_else(|error| panic!("deferred source count is not numeric: {error}"))
            })
            .sum::<usize>();
        let deferred_sinks = selector_resource_deferred
            .iter()
            .map(|program| {
                merged
                    .iter()
                    .find(|row| row.get("program") == Some(*program))
                    .and_then(|row| row.get("sinks_leaked"))
                    .unwrap_or_else(|| panic!("deferred {program} row lacks sinks_leaked"))
                    .parse::<usize>()
                    .unwrap_or_else(|error| panic!("deferred sink count is not numeric: {error}"))
            })
            .sum::<usize>();
        assert_eq!(
            source_records.len(),
            114 - deferred_sources,
            "every non-deferred final leaked source selector must have one classification row"
        );
        assert_eq!(
            sink_records.len(),
            170 - deferred_sinks,
            "every non-deferred final leaked sink selector must have one secondary classification row"
        );
        let mut program_status_csv = String::from(
            "program,status,official_sources_leaked,covered_sources,official_sinks_leaked,\
             covered_sinks,official_wall_s,tracked_first_wall_s,tracked_retry_wall_s,\
             tracked_total_wall_s\n",
        );
        for row in &merged {
            let program = row.get("program").expect("selector program");
            let deferred = selector_resource_deferred.contains(&program);
            let sources = row
                .get("sources_leaked_sel")
                .expect("selector source count");
            let sinks = row.get("sinks_leaked").expect("selector sink count");
            program_status_csv.push_str(&format!(
                "{program},{},{sources},{},{sinks},{},{},{},{},{}\n",
                row.get("selector_core_status").unwrap_or("missing"),
                if deferred { "0" } else { sources },
                if deferred { "0" } else { sinks },
                row.get("bo_wall_s").unwrap_or("-"),
                row.get("selector_core_first_wall_s").unwrap_or("-"),
                row.get("selector_core_retry_wall_s").unwrap_or("-"),
                row.get("selector_core_wall_s").unwrap_or("-"),
            ));
        }

        let source_final = selector_leak_diagnosis::final_evidence(
            &evidence,
            selector_leak_diagnosis::SelectorClass::Source,
        );
        let sink_final = selector_leak_diagnosis::final_evidence(
            &evidence,
            selector_leak_diagnosis::SelectorClass::Sink,
        );
        let tracked_wall = |program: &str| {
            merged
                .iter()
                .find(|row| row.get("program") == Some(program))
                .and_then(|row| row.get("selector_core_wall_s"))
                .and_then(|wall| wall.parse::<f64>().ok())
                .unwrap_or(f64::INFINITY)
        };
        let families = source_final
            .iter()
            .flat_map(|record| record.raw_families.iter().cloned())
            .collect::<BTreeSet<_>>();
        let mut selected_by_family = Vec::new();
        let mut selected_cases: BTreeMap<(String, usize, usize), BTreeSet<String>> =
            BTreeMap::new();
        for family in families {
            let mut candidates = source_final
                .iter()
                .map(|record| (false, *record))
                .chain(sink_final.iter().map(|record| (true, *record)))
                .filter(|(_, record)| record.raw_families.contains(&family))
                .collect::<Vec<_>>();
            candidates.sort_by(|(left_sink, left), (right_sink, right)| {
                left_sink
                    .cmp(right_sink)
                    .then_with(|| {
                        tracked_wall(&left.program).total_cmp(&tracked_wall(&right.program))
                    })
                    .then_with(|| left.program.cmp(&right.program))
                    .then_with(|| left.selector_key.cmp(&right.selector_key))
            });
            let case_limit = representative_case_limit(candidates.len());
            for (_, record) in candidates.into_iter().take(case_limit) {
                selected_cases
                    .entry((record.program.clone(), record.epoch, record.selector_index))
                    .or_default()
                    .insert(family.clone());
                selected_by_family.push((
                    family.clone(),
                    record.program.clone(),
                    record.selector_key.clone(),
                    record.epoch,
                    record.selector_index,
                    record.class,
                ));
            }
        }

        enum DetailOutcome {
            Complete {
                wall_s: f64,
                path: std::path::PathBuf,
                detail: selector_leak_diagnosis::DetailEvidence,
            },
            ResourceDeferred {
                wall_s: f64,
                status: String,
                note: String,
            },
        }

        let mut detail_outcomes = BTreeMap::new();
        for ((program, epoch, selector_index), selected_families) in &selected_cases {
            let corpus_program = CORPUS
                .iter()
                .find(|candidate| candidate.name == program)
                .unwrap_or_else(|| panic!("representative program {program} is not in rs-crown"));
            let input = corpus_program.input_path(&root);
            let mode = format!("selector-detail-{epoch}-{selector_index}");
            eprintln!(
                "[boc1] {program}: {mode} families={}...",
                selected_families
                    .iter()
                    .cloned()
                    .collect::<Vec<_>>()
                    .join("+")
            );
            let outcome = run_child(program, &input, &mode, diagnostic_timeout);
            let detail_outcome = match diagnostic_worker_disposition(&outcome.status) {
                DiagnosticWorkerDisposition::Complete => {
                    let path = selector_detail_path(program, &format!("{epoch}-{selector_index}"));
                    assert!(
                        path.is_file(),
                        "selector representative evidence missing: {}",
                        path.display()
                    );
                    let detail = selector_leak_diagnosis::read_detail_evidence(&path)
                        .unwrap_or_else(|error| panic!("{error}"));
                    DetailOutcome::Complete {
                        wall_s: outcome.wall_s,
                        path,
                        detail,
                    }
                }
                DiagnosticWorkerDisposition::ResourceDeferred => DetailOutcome::ResourceDeferred {
                    wall_s: outcome.wall_s,
                    status: outcome.status,
                    note: outcome.note,
                },
                DiagnosticWorkerDisposition::CorrectnessFailure => {
                    panic!(
                        "selector representative failed for {program} epoch {epoch} selector \
                         {selector_index}: status={} note={}",
                        outcome.status, outcome.note
                    );
                }
            };
            detail_outcomes.insert((program.clone(), *epoch, *selector_index), detail_outcome);
        }

        let mut representative_tsv = String::from(
            "family\tprogram\tselector_key\tepoch\tselector_index\tclass\t\
             matrix_raw_families\tdetail_raw_families\tdetail_minimized_families\t\
             minimized\tcommit_origins\twall_s\tstatus\tnote\tevidence_path\n",
        );
        for (family, program, selector_key, epoch, selector_index, class) in selected_by_family {
            let outcome = detail_outcomes
                .get(&(program.clone(), epoch, selector_index))
                .expect("representative outcome");
            let matrix = source_final
                .iter()
                .chain(sink_final.iter())
                .find(|record| {
                    record.program == program
                        && record.epoch == epoch
                        && record.selector_index == selector_index
                })
                .expect("representative matrix record");
            let matrix_families = matrix
                .raw_families
                .iter()
                .cloned()
                .collect::<Vec<_>>()
                .join("+");
            match outcome {
                DetailOutcome::Complete {
                    wall_s,
                    path,
                    detail,
                } => representative_tsv.push_str(&format!(
                    "{family}\t{program}\t{selector_key}\t{epoch}\t{selector_index}\t{class:?}\t\
                     {matrix_families}\t{}\t{}\t{}\t{}\t{wall_s:.1}\tok\t-\t{}\n",
                    detail
                        .raw_families
                        .iter()
                        .cloned()
                        .collect::<Vec<_>>()
                        .join("+"),
                    detail
                        .minimized_families
                        .iter()
                        .cloned()
                        .collect::<Vec<_>>()
                        .join("+"),
                    detail.minimized,
                    detail.commit_origins.join(" || "),
                    path.display(),
                )),
                DetailOutcome::ResourceDeferred {
                    wall_s,
                    status,
                    note,
                } => representative_tsv.push_str(&format!(
                    "{family}\t{program}\t{selector_key}\t{epoch}\t{selector_index}\t{class:?}\t\
                     {matrix_families}\t-\t-\tfalse\t-\t{wall_s:.1}\t\
                     resource-deferred-{status}\t{}\t-\n",
                    report::sanitize(note),
                )),
            }
        }
        fs::write(
            out_dir().join("representative-cases.tsv"),
            representative_tsv,
        )
        .expect("write representative case index");

        let json_lines = |records: Vec<&selector_leak_diagnosis::CoreEvidence>| {
            let mut output = String::new();
            for record in records {
                output.push_str(&serde_json::to_string(record).expect("encode combined evidence"));
                output.push('\n');
            }
            output
        };
        fs::write(
            out_dir().join("selector-drop-events.jsonl"),
            json_lines(
                evidence
                    .iter()
                    .filter(|record| record.phase == selector_leak_diagnosis::TracePhase::Drop)
                    .collect(),
            ),
        )
        .expect("write selector drop events");
        fs::write(
            out_dir().join("selector-reenable-events.jsonl"),
            json_lines(
                evidence
                    .iter()
                    .filter(|record| record.phase == selector_leak_diagnosis::TracePhase::Reenable)
                    .collect(),
            ),
        )
        .expect("write selector re-enable events");
        let (source_csv, source_cross_tab) =
            selector_leak_diagnosis::render_records(&source_records);
        let (sink_csv, sink_cross_tab) = selector_leak_diagnosis::render_records(&sink_records);
        fs::write(
            out_dir().join("source-selector-classification.csv"),
            &source_csv,
        )
        .expect("write source selector classifications");
        fs::write(
            out_dir().join("sink-selector-classification.csv"),
            &sink_csv,
        )
        .expect("write sink selector classifications");
        fs::write(
            out_dir().join("family-program-crosstab.csv"),
            &source_cross_tab,
        )
        .expect("write source family/program cross-tab");
        fs::write(
            out_dir().join("sink-family-program-crosstab.csv"),
            &sink_cross_tab,
        )
        .expect("write sink family/program cross-tab");
        fs::write(
            out_dir().join("selector-program-status.csv"),
            &program_status_csv,
        )
        .expect("write selector program status");
        fs::write(
            out_dir().join("classification-report.md"),
            format!(
                "# Source-selector leak core classification\n\n\
                 - Contract: Mode-A, L2 off, smt.random_seed=0, sat.random_seed=0, \
                   official 900 s / tracked 1800 s, one serial tracked retry at 3600 s, \
                   8192 MiB, serialized.\n\
                 - Baseline: 20/20 accept; n_ref=52,810; n_own=230; \
                   sources leaked=114/144; sinks leaked=170/206.\n\
                 - Covered source rows: {}/114. Covered sink secondary rows: {}/170.\n\
                 - Resource-deferred tracked programs: {} (source rows deferred: {}; \
                   sink rows deferred: {}).\n\
                 - Corpus hard-core minimization: disabled; `minimized=false` and \
                   the raw family-marker core is authoritative.\n\
                 - Out-param tag: untagged unless direct selector-to-slot provenance exists; \
                   this run does not infer from core chains.\n\
                 - Core visibility: mutability and fatness are not independent Z3 families; \
                   their influence can appear only indirectly through replay-generated commits.\n\n\
                 ## Per-program status\n\n```csv\n{program_status_csv}```\n\n\
                 ## Source family × program\n\n```csv\n{source_cross_tab}```\n\n\
                 ## Sink family × program\n\n```csv\n{sink_cross_tab}```\n\n\
                 ## Limitations\n\n\
                 The matrix is core-incidence under one marker per hard-constraint family. \
                 A reserved follow-up, not run here, is removal-based necessity attribution \
                 at each drop point: re-solve the untracked system with one family's constraints \
                 removed and report that family necessary when the result becomes SAT. This could \
                 cover resource-deferred programs at untracked speed while preserving the \
                 family-incidence meaning of the matrix.\n",
                source_records.len(),
                sink_records.len(),
                if selector_resource_deferred.is_empty() {
                    "none".to_string()
                } else {
                    selector_resource_deferred.join(",")
                },
                deferred_sources,
                deferred_sinks,
            ),
        )
        .expect("write selector classification report");
    }

    if diagnostic_package {
        let parse_total = |key: &str| {
            merged
                .iter()
                .map(|row| {
                    row.get(key)
                        .unwrap_or_else(|| panic!("ownership diagnostic row missing {key}"))
                        .parse::<usize>()
                        .unwrap_or_else(|error| {
                            panic!("ownership diagnostic {key} is not numeric: {error}")
                        })
                })
                .sum::<usize>()
        };
        assert_eq!(
            merged.len(),
            20,
            "diagnostic package must cover 20 programs"
        );
        assert!(
            merged.iter().all(|row| row.get("status") == Some("ok")),
            "ownership diagnostic official worker declined"
        );
        assert_eq!(parse_total("n_ref"), 52_810);
        assert_eq!(parse_total("n_own"), 230);
        assert_eq!(parse_total("sources_leaked_sel"), 114);
        let source_selector_total = merged
            .iter()
            .map(|row| {
                let emissions = row
                    .get("source_sink_emissions")
                    .expect("diagnostic row missing source_sink_emissions")
                    .parse::<usize>()
                    .expect("source_sink_emissions is numeric");
                let sinks = row
                    .get("sinks_total")
                    .expect("diagnostic row missing sinks_total")
                    .parse::<usize>()
                    .expect("sinks_total is numeric");
                emissions
                    .checked_sub(sinks)
                    .expect("sink selectors cannot exceed total selector emissions")
            })
            .sum::<usize>();
        assert_eq!(source_selector_total, 144);
        assert_eq!(parse_total("sinks_leaked"), 170);
        assert_eq!(parse_total("sinks_total"), 206);

        let production_failures = merged
            .iter()
            .flat_map(|row| {
                ["prod_precision_status", "prod_box_status"]
                    .into_iter()
                    .filter_map(move |key| {
                        row.get(key)
                            .filter(|status| !status.starts_with("ok"))
                            .map(|status| {
                                (
                                    row.get("program").unwrap_or("unknown"),
                                    key,
                                    status.to_string(),
                                )
                            })
                    })
            })
            .collect::<Vec<_>>();
        let failed_production_programs = production_failures
            .iter()
            .map(|(program, _, _)| *program)
            .collect::<BTreeSet<_>>();
        assert!(
            failed_production_programs.len() <= 5,
            "production failed on {} programs; measurement design review required: {:?}",
            failed_production_programs.len(),
            production_failures
        );

        let mut necessity = Vec::<NecessityEvidence>::new();
        let mut uncovered_sources = 0usize;
        for program in CORPUS {
            let row = merged
                .iter()
                .find(|row| row.get("program") == Some(program.name))
                .expect("diagnostic program row");
            if row
                .get("necessity_status")
                .is_some_and(|status| status.starts_with("ok"))
            {
                let mut records: Vec<NecessityEvidence> =
                    ownership_diagnostic_package::read_json(&necessity_evidence_path(program.name))
                        .unwrap_or_else(|error| panic!("{error}"));
                necessity.append(&mut records);
            } else {
                uncovered_sources += row
                    .get("sources_leaked_sel")
                    .expect("deferred necessity source count")
                    .parse::<usize>()
                    .expect("numeric deferred necessity source count");
            }
        }
        necessity.sort_by(|left, right| {
            left.program
                .cmp(&right.program)
                .then_with(|| left.selector_key.cmp(&right.selector_key))
        });
        assert_eq!(
            necessity.len() + uncovered_sources,
            114,
            "necessity coverage must reconcile to official leaked sources"
        );

        let mut selector_csv = String::from(
            "program,selector_key,epoch,raw_families,necessary_families,\
             causal_bucket,own_assume_necessary_sites,solely_own_assume,\
             wrapper_share,own_linear_candidate,grouping_hinge\n",
        );
        let mut causal_csv = String::from(
            "program,selector_key,causal_bucket,solely_own_assume,wrapper_share,\
             own_linear_candidate,grouping_hinge,joint_no_single_family_necessity\n",
        );
        let mut assume_csv =
            String::from("program,selector_key,own_assume_necessary,necessary_sites,distributed\n");
        let programs = CORPUS
            .iter()
            .map(|program| program.name)
            .collect::<Vec<_>>();
        let mut family_program: BTreeMap<String, BTreeMap<&str, usize>> = BTreeMap::new();
        let mut sole_own_assume = 0usize;
        let mut wrapper_share = 0usize;
        let mut own_linear_candidates = 0usize;
        let mut grouping_hinges = 0usize;
        let mut joint = 0usize;
        let mut distributed_assume = 0usize;
        for record in &necessity {
            for family in &record.necessary_families {
                *family_program
                    .entry(family.clone())
                    .or_default()
                    .entry(record.program.as_str())
                    .or_default() += 1;
            }
            let sole = record.necessary_families.len() == 1
                && record.necessary_families.contains("own-assume");
            let wrapper = sole
                && record
                    .own_assume_necessary_sites
                    .contains(AssumeSite::LocalWrapper.as_str());
            let own_linear = record.necessary_families.contains("own-linear");
            let grouping = record.necessary_families.contains("kind-equate")
                || record.necessary_families.contains("link-own");
            let is_joint = record.necessary_families.is_empty();
            let own_assume = record.necessary_families.contains("own-assume");
            let distributed = own_assume && record.own_assume_necessary_sites.is_empty();
            sole_own_assume += usize::from(sole);
            wrapper_share += usize::from(wrapper);
            own_linear_candidates += usize::from(own_linear);
            grouping_hinges += usize::from(grouping);
            joint += usize::from(is_joint);
            distributed_assume += usize::from(distributed);
            let raw = record
                .raw_families
                .iter()
                .cloned()
                .collect::<Vec<_>>()
                .join("+");
            let necessary_families = record
                .necessary_families
                .iter()
                .cloned()
                .collect::<Vec<_>>()
                .join("+");
            let sites = record
                .own_assume_necessary_sites
                .iter()
                .cloned()
                .collect::<Vec<_>>()
                .join("+");
            selector_csv.push_str(&format!(
                "{},{},{},{raw},{necessary_families},{:?},{sites},{sole},{wrapper},\
                 {own_linear},{grouping}\n",
                record.program, record.selector_key, record.epoch, record.causal_bucket
            ));
            causal_csv.push_str(&format!(
                "{},{},{:?},{sole},{wrapper},{own_linear},{grouping},{is_joint}\n",
                record.program, record.selector_key, record.causal_bucket
            ));
            assume_csv.push_str(&format!(
                "{},{},{own_assume},{sites},{distributed}\n",
                record.program, record.selector_key
            ));
        }
        let mut family_program_csv = format!("family,{},total\n", programs.join(","));
        for family in CORE_LABEL_FAMILIES {
            let mut total = 0usize;
            family_program_csv.push_str(family);
            for program in &programs {
                let count = family_program
                    .get(*family)
                    .and_then(|by_program| by_program.get(*program))
                    .copied()
                    .unwrap_or(0);
                total += count;
                family_program_csv.push_str(&format!(",{count}"));
            }
            family_program_csv.push_str(&format!(",{total}\n"));
        }

        let mut precision_records = Vec::<FunctionPrecisionRecord>::new();
        let mut precision_programs = Vec::<ProductionPrecisionEvidence>::new();
        for program in CORPUS {
            let row = merged
                .iter()
                .find(|row| row.get("program") == Some(program.name))
                .expect("precision program row");
            if row
                .get("prod_precision_status")
                .is_some_and(|status| status.starts_with("ok"))
            {
                let evidence: ProductionPrecisionEvidence =
                    ownership_diagnostic_package::read_json(&production_precision_path(
                        program.name,
                    ))
                    .unwrap_or_else(|error| panic!("{error}"));
                precision_records.extend(evidence.functions.iter().cloned());
                precision_programs.push(evidence);
            }
        }
        precision_records.sort_by(|left, right| {
            left.program
                .cmp(&right.program)
                .then_with(|| left.function.cmp(&right.function))
        });
        let production_total = precision_programs
            .iter()
            .map(|evidence| evidence.total_owning)
            .sum::<usize>();
        if production_failures
            .iter()
            .all(|(_, key, _)| *key != "prod_precision_status")
        {
            assert_eq!(production_total, 6_515, "production Owning anchor diverged");
        }
        let mut precision_csv = String::from(
            "program,function,required_precision,final_precision,class,owning_locals\n",
        );
        for record in &precision_records {
            precision_csv.push_str(&format!(
                "{},{},{},{},{:?},{}\n",
                record.program,
                record.function,
                record.required_precision,
                record.final_precision,
                record.class,
                record.owning_locals
            ));
        }
        let mut owning_by_precision_csv = String::from(
            "program,full_owning,degraded_owning,dummy_owning,field_owning_not_applicable,\
             total_owning\n",
        );
        let mut full_owning = 0usize;
        let mut degraded_owning = 0usize;
        let mut dummy_owning = 0usize;
        let mut field_na = 0usize;
        for evidence in &precision_programs {
            let by_class = |class| {
                evidence
                    .functions
                    .iter()
                    .filter(|record| record.class == class)
                    .map(|record| record.owning_locals)
                    .sum::<usize>()
            };
            let full = by_class(ownership_diagnostic_package::PrecisionClass::Full);
            let degraded = by_class(ownership_diagnostic_package::PrecisionClass::Degraded);
            let dummy = by_class(ownership_diagnostic_package::PrecisionClass::Dummy);
            full_owning += full;
            degraded_owning += degraded;
            dummy_owning += dummy;
            field_na += evidence.field_owning_not_applicable;
            owning_by_precision_csv.push_str(&format!(
                "{},{full},{degraded},{dummy},{},{}\n",
                evidence.program, evidence.field_owning_not_applicable, evidence.total_owning
            ));
        }
        let functions_total = precision_records.len();
        let functions_degraded = precision_records
            .iter()
            .filter(|record| record.class == ownership_diagnostic_package::PrecisionClass::Degraded)
            .count();
        let functions_dummy = precision_records
            .iter()
            .filter(|record| record.class == ownership_diagnostic_package::PrecisionClass::Dummy)
            .count();

        let mut boxes = Vec::<BoxDecisionEvidence>::new();
        for program in CORPUS {
            let row = merged
                .iter()
                .find(|row| row.get("program") == Some(program.name))
                .expect("Box program row");
            if row
                .get("prod_box_status")
                .is_some_and(|status| status.starts_with("ok"))
            {
                boxes.push(
                    ownership_diagnostic_package::read_json(&production_box_path(program.name))
                        .unwrap_or_else(|error| panic!("{error}")),
                );
            }
        }
        let mut box_csv =
            String::from("program,locals,params,returns,fields,total,d0_locals_only\n");
        let mut box_total = ownership_diagnostic_package::BoxDecisionCounts::default();
        for evidence in &boxes {
            let counts = evidence.counts;
            box_total.locals += counts.locals;
            box_total.params += counts.params;
            box_total.returns += counts.returns;
            box_total.fields += counts.fields;
            box_total.d0_locals += counts.d0_locals;
            box_csv.push_str(&format!(
                "{},{},{},{},{},{},{}\n",
                evidence.program,
                counts.locals,
                counts.params,
                counts.returns,
                counts.fields,
                counts.locals + counts.params + counts.returns + counts.fields,
                counts.d0_locals,
            ));
        }

        let mut status_csv = String::from(
            "program,official_status,official_wall_s,necessity_status,necessity_first_wall_s,\
             necessity_retry_wall_s,necessity_total_wall_s,prod_precision_status,\
             prod_precision_first_wall_s,prod_precision_retry_wall_s,prod_precision_total_wall_s,\
             prod_box_status,prod_box_first_wall_s,prod_box_retry_wall_s,prod_box_total_wall_s\n",
        );
        for row in &merged {
            status_csv.push_str(&format!(
                "{},{},{},{},{},{},{},{},{},{},{},{},{},{},{}\n",
                row.get("program").unwrap_or("-"),
                row.get("status").unwrap_or("-"),
                row.get("bo_wall_s").unwrap_or("-"),
                row.get("necessity_status").unwrap_or("-"),
                row.get("necessity_first_wall_s").unwrap_or("-"),
                row.get("necessity_retry_wall_s").unwrap_or("-"),
                row.get("necessity_wall_s").unwrap_or("-"),
                row.get("prod_precision_status").unwrap_or("-"),
                row.get("prod_precision_first_wall_s").unwrap_or("-"),
                row.get("prod_precision_retry_wall_s").unwrap_or("-"),
                row.get("prod_precision_wall_s").unwrap_or("-"),
                row.get("prod_box_status").unwrap_or("-"),
                row.get("prod_box_first_wall_s").unwrap_or("-"),
                row.get("prod_box_retry_wall_s").unwrap_or("-"),
                row.get("prod_box_wall_s").unwrap_or("-"),
            ));
        }

        fs::write(
            out_dir().join("selector-family-necessity.csv"),
            &selector_csv,
        )
        .expect("write selector-family necessity");
        fs::write(
            out_dir().join("family-program-necessity.csv"),
            &family_program_csv,
        )
        .expect("write family-program necessity");
        fs::write(out_dir().join("assume-site-necessity.csv"), &assume_csv)
            .expect("write assume-site necessity");
        fs::write(out_dir().join("causal-partition.csv"), &causal_csv)
            .expect("write causal partition");
        fs::write(
            out_dir().join("production-function-precision.csv"),
            &precision_csv,
        )
        .expect("write production function precision");
        fs::write(
            out_dir().join("production-owning-by-precision.csv"),
            &owning_by_precision_csv,
        )
        .expect("write production owning by precision");
        fs::write(out_dir().join("production-box-decisions.csv"), &box_csv)
            .expect("write production Box decisions");
        fs::write(out_dir().join("status-timing.csv"), &status_csv)
            .expect("write diagnostic status and timing");
        let joint_followup = if joint == 0 {
            String::new()
        } else {
            "\n## Joint-cause follow-up\n\n\
             Because the joint/no-single-family bucket is nonempty, pairwise \
             family-removal probing is a recorded follow-up option. It was not \
             executed in this task.\n"
                .to_string()
        };
        fs::write(
            out_dir().join("ownership-diagnostic-package-report.md"),
            format!(
                "# Ownership diagnostic package\n\n\
                 - Contract: frozen rs-crown; Mode-A; L2 off; smt.random_seed=0; \
                   sat.random_seed=0; serialized; official workers 900 s; diagnostic and \
                   production workers 1800 s; one 3600 s retry; 8192 MiB.\n\
                 - Baseline: 20/20 accept; n_ref=52,810; n_own=230; source leaks=114/144; \
                   sink leaks=170/206.\n\
                 - Necessity coverage: {}/114 (uncovered resource-deferred: {}).\n\
                 - Solely own-assume: {sole_own_assume}; local-wrapper share: {wrapper_share}; \
                   own-linear candidates: {own_linear_candidates}; grouping hinges: \
                   {grouping_hinges}; joint/no-single-family necessity: {joint}; \
                   distributed own-assume sites: {distributed_assume}.\n\
                 - Production precision coverage: {}/20 programs; functions: {functions_total}; \
                   degraded: {functions_degraded}; dummy: {functions_dummy}; Owning claims by \
                   function precision full/degraded/dummy={full_owning}/{degraded_owning}/\
                   {dummy_owning}; fields not applicable={field_na}; covered production Owning \
                   total={production_total}.\n\
                 - Production end-to-end Box-family coverage: {}/20 programs; \
                   locals/params/returns/fields={}/{}/{}/{}; total={}; \
                   d0-locals-only={}.\n\
                 - Production failures: {:?}.\n\
                 {joint_followup}",
                necessity.len(),
                uncovered_sources,
                precision_programs.len(),
                boxes.len(),
                box_total.locals,
                box_total.params,
                box_total.returns,
                box_total.fields,
                box_total.locals + box_total.params + box_total.returns + box_total.fields,
                box_total.d0_locals,
                production_failures,
            ),
        )
        .expect("write ownership diagnostic package report");
    }

    println!("\n{}", render_report(&merged));
    if ownership_yield_enabled {
        assert_eq!(
            ownership_yield_rows.len(),
            20,
            "ownership-yield measurement did not produce 20 BO rows"
        );
        let bo_total = ownership_yield_rows
            .iter()
            .map(|row| row.bo.total_owning)
            .sum::<usize>();
        assert_eq!(
            bo_total, 230,
            "ownership-yield BO total diverged from the official rs-crown baseline"
        );
        println!(
            "\n{}",
            ownership_yield::render_markdown(&ownership_yield_rows)
        );
    }
    if l2_gate {
        l2_red_gate::assert_results(&merged, CORPUS);
    }
}

#[cfg(test)]
fn render_report(merged: &[report::Row]) -> String {
    let cols = [
        "program",
        "sloc",
        "status",
        "wall_s",
        "t_fixpoint_s",
        "t_origins_s",
        "rounds",
        "commits_conflict",
        "check_sat_count",
        "slots_total",
        "n_ref",
        "n_raw",
        "n_own",
        "n_ref_d0",
        "n_own_d0",
        "n_ref_shared_d0",
        "n_ref_mut_d0",
        "mut_facts",
        "mut_default_fires",
        "n_ref_prod",
        "d_ref_d0",
        "l2_base_n_ref",
        "l2_n_ref_delta",
        "l2_targets_expected",
        "l2_targets_found",
        "l2_targets_ref",
        "sources_total",
        "sources_leaked",
        "sources_leaked_sel",
        "sinks_total",
        "sinks_leaked",
        "s23_stores_owned",
        "s23_owning_model",
        "s23_blocked",
        "decline_reason",
        "l2_decline",
        "core_families",
        "core_minimized",
        "prod_status",
    ];
    let repair = merged
        .iter()
        .find_map(|row| row.get("repair"))
        .unwrap_or("pending");
    let z3_version = merged
        .iter()
        .find_map(|row| row.get("z3_full_version"))
        .unwrap_or("pending");
    let deferred = CORPUS
        .iter()
        .filter(|program| is_resource_deferred(program.sloc))
        .count();
    let mut out = String::from("# rs-crown BO baseline report\n\n");
    out.push_str(&format!(
        "Run contract: repair={repair}; smt.random_seed=0; sat.random_seed=0; \
         z3_full_version={z3_version}.\n\n\
         Corpus: the 20 programs in `benchmarks/rs-crown/`, smallest-first by Rust SLOC. \
         Brotli is the inclusive development boundary at {BROTLI_SLOC} SLOC; \
         resource-deferred means strictly greater than brotli ({deferred} programs in this catalog).\n\n"
    ));
    out.push_str(
        "`d_ref_d0` = BO depth-0 local Ref count minus the optional production baseline's \
         (`demote_pointers_iterative_with_fields` from all-Ref, same accounting). \
         `decline_reason` separates non-source UNSAT from z3 Unknown (harness-side \
         phase-1 replay). `sources_total`/`sources_leaked` count malloc-source SLOTS \
         (propagation-closed over copies/moves/casts, so one allocation can contribute \
         several slots, e.g. its `free` call-arg temp); a slot is leaked when its final \
         kind is not Owning. `sources_leaked_sel` and `sinks_leaked` count dropped source/sink \
         SELECTORS. `s23_stores_owned` counts field owning-store candidates; \
         `s23_owning_model` counts those emerging Owning in an accepted model. \
         `commits_conflict` counts exclusion assertions exactly as the real \
         loop's `committed` does — the same slot can be committed by several conflicts \
         in one round, so this is commit OPERATIONS, not unique slots. `d_ref_d0` is a \
         Ref-count delta, not a pure borrow-precision delta: BO's non-Ref includes \
         Owning (a win) and leaked-source Raw — read it together with `n_own`. \
         `wall_s` is supervision-level (includes up to ~200ms poll latency); \
         `t_total_s` in the CSV/JSONL is the child-measured time.\n\n",
    );
    out.push_str(&report::render_markdown(merged, &cols));
    if merged.iter().any(|row| row.get("l2_feature") == Some("on")) {
        out.push_str("\n\n");
        out.push_str(&l2_red_gate::summary(merged));
        out.push('\n');
    }
    out
}

/// §NB5-L — the empty-context disjunctive lemma vs Mode-A, per-slot (first-touch dump 2026-07-18; the
/// original "≡ Mode-A" claim was an AGGREGATE-COUNT claim, REFUTED by this per-slot check — Codex-
/// demanded). **This is an EMPIRICAL observation on these fixtures + the pinned seed, NOT a universal
/// law** (Codex re-review): the loop is NON-CONFLUENT, so the two models are **incomparable in
/// general** — there is no proof `Ref(lemmas) ⊆ Ref(mode_a)` always holds. What IS established: on the
/// fixtures below the inclusion holds, and on a 33-requirer fan-out it is STRICT — Lemmas loses ≥1 Ref
/// by demoting a NON-MINIMAL menu member (`nb5l_high_arity_lemmas_converges_no_panic`), the hazard
/// `verify_to_fixpoint`'s doc names ("Mode A = monotone single-slot commitment, deliberately NOT
/// disjunctive"). So the disjunction has no established upside and a demonstrated downside — the
/// disjunction axis is DEAD; the positive win, if any, is NB5-L2's orthogonal context axis
/// (context-conditioned SINGLE-LITERAL commits, hazard-free), gated behind the commit-necessity audit.
/// Non-vacuity: at least one shape emits a genuine ≥2-literal A′ menu (distinct requirers ≠ issuer), so
/// the disjunction path is actually exercised (not a trivial singleton ≡ Mode-A).
#[cfg(test)]
#[test]
fn nb5l_lemma_ref_subset_mode_a_on_fixtures() {
    use rustc_hash::{FxHashMap, FxHashSet};

    use crate::analyses::borrow_ownership::{
        CrateCtxt, SlotKind,
        borrow_verify::{RepairMode, revalidate, verify_to_fixpoint_counting},
        coherence::add_coherence,
        crate_slots::CrateSlots,
        emit_crate_ownership_constraints,
        origins::compute_origins,
        solver::{KindSolver, SlotRef},
    };
    struct Outcome {
        model: FxHashMap<SlotRef, SlotKind>,
    }
    // Returns (mode_a, lemmas, max_a_prime_menu_len) for `code`. The menu-len witness mirrors
    // `a_prime_menu` at the round-0 all-Ref model: the count of DISTINCT requirers r with r ≠ issuer
    // (the Lemmas disjunction's ACTUAL literal set). NOT raw `requirers.len()` — that counts the
    // issuer as a self-requirer and any duplicate owners, over-reporting arity so the non-vacuity
    // guard could pass on singleton menus (Codex MEDIUM 2026-07-18).
    fn run(code: &str) -> (Outcome, Outcome, usize) {
        ::utils::compilation::run_compiler_on_str(code, |tcx| {
            let program = collect_program(tcx);
            let slots = CrateSlots::build(&program);
            let max_menu = revalidate(&program, &slots, |_s: SlotRef| true, true)
                .values()
                .flatten()
                .map(|e| {
                    let mut seen = FxHashSet::default();
                    e.requirers
                        .iter()
                        .filter(|r| Some(**r) != e.issuer)
                        .filter(|r| seen.insert(**r))
                        .count()
                })
                .max()
                .unwrap_or(0);
            let solve = |mode: RepairMode| {
                let crate_ctxt = CrateCtxt::new(&program);
                let solver = KindSolver::new(&slots);
                let (_s, sel) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &solver,
                )
                .expect("emit");
                for &g in &program.functions {
                    let body = tcx.mir_drops_elaborated_and_const_checked(g).borrow();
                    add_coherence(&solver, &slots, g, &body);
                }
                let (model, stats) = RepairMode::with_override(mode, || {
                    verify_to_fixpoint_counting(&program, &slots, &solver, &sel, true)
                });
                assert_eq!(
                    stats.repair, mode,
                    "mode-stamp (guard 3) must record the active repair"
                );
                Outcome {
                    model: model.expect("fixture must accept under both modes"),
                }
            };
            (
                solve(RepairMode::ModeA),
                solve(RepairMode::Lemmas),
                max_menu,
            )
        })
        .unwrap_or_else(|e| e.raise())
    }
    // Shapes: a single-requirer cascade plus three that produce genuine ≥2-requirer edges (a shared
    // reborrow aliased by several interproc copies, all live at one invalidating write).
    let shapes: [(&str, &str); 4] = [
        (
            "single_req_cascade",
            "unsafe fn id(p: *mut i32) -> *mut i32 { p } \
             unsafe fn f(p: *mut i32) -> i32 { let x = id(p); *x = 1; let b = p; *b = 2; *x }",
        ),
        (
            "two_requirer",
            "unsafe fn id(p: *mut i32) -> *mut i32 { p } \
             unsafe fn f(p: *mut i32) -> i32 { let base = id(p); let a = id(base); let b = id(base); \
             let w = p; *w = 9; *a + *b }",
        ),
        (
            "three_requirer",
            "unsafe fn id(p: *mut i32) -> *mut i32 { p } \
             unsafe fn f(p: *mut i32) -> i32 { let bb = p; let x = id(p); let z = id(x); let q = id(x); \
             *bb = 5; *x + *z + *q }",
        ),
        (
            "asymmetric",
            "unsafe fn id(p: *mut i32) -> *mut i32 { p } \
             unsafe fn f(p: *mut i32) -> i32 { let a = id(p); let b = id(p); let d = id(b); \
             *a = 1; *b = 2; *d = 3; let w = p; *w = 4; *a + *b + *d }",
        ),
    ];
    let ref_of = |m: &FxHashMap<SlotRef, SlotKind>| -> FxHashSet<SlotRef> {
        m.iter()
            .filter(|(_, k)| **k == SlotKind::Ref)
            .map(|(s, _)| *s)
            .collect()
    };
    let mut max_menu_seen = 0usize;
    for (tag, code) in shapes {
        let (a, l, max_menu) = run(code);
        // EMPIRICAL per-slot relation on these fixtures (per-slot — the granularity Codex demanded;
        // aggregate counts hid the high-arity divergence). Lemmas' Ref-set ⊆ Mode-A's here: the
        // disjunction keeps no MORE Ref than Mode-A's minimal unit commit and CAN keep fewer (the
        // high-arity witness). This inclusion is an OBSERVATION on these fixtures + the pinned seed,
        // NOT a universal law — the loop is non-confluent, so the models are incomparable in general.
        assert!(
            ref_of(&l.model).is_subset(&ref_of(&a.model)),
            "{tag}: on this fixture Lemmas Ref-set should be ⊆ Mode-A's; a Lemmas-only Ref would mean \
             the modes are incomparable here (still not a regression-in-our-favor — see the row doc)"
        );
        // NOTE: no path-cost assertion. `commits`/`rounds` are NOT ordered between the modes in general
        // (non-confluence — Lemmas could converge in fewer or more rounds on a given program); asserting
        // `≥` would be an unsupported dominance claim (Codex). The counts are reported by the sweep.
        max_menu_seen = max_menu_seen.max(max_menu);
    }
    // Non-vacuity: at least one shape must emit a genuine ≥2-literal A′ menu (≥2 DISTINCT requirers
    // ≠ issuer). Without this the equality could hold trivially because every emitted lemma is a
    // singleton ≡ Mode-A, leaving the disjunction path — the whole point of the row — untested.
    assert!(
        max_menu_seen >= 2,
        "non-vacuity: no shape emitted a ≥2-literal A′ menu (max distinct requirers≠issuer = {max_menu_seen}); \
         the disjunction path is untested"
    );
}

/// §NB5-L high-arity regression (Codex HIGH, 2026-07-18). One loan required by a large fan-out of
/// live requirers is the shape whose disjunction could, in the abstract, drive subset oscillation up
/// to ~2^k rounds against the linear cap. This test pins the EMPIRICAL reality under the NB5-Z seed:
/// even a 33-distinct-requirer edge **converges in a handful of rounds under Lemmas and never panics**
/// — the 2^k worst case does not manifest. It is also the **≤-regression witness**: here `Ref(lemmas)`
/// is a STRICT subset of `Ref(mode_a)` (Lemmas loses ≥1 Ref to non-minimal demotion), so the modes do
/// NOT match per-slot. The cap-exhaustion path is a CONTROLLED decline (not a panic) for Lemmas
/// regardless (see `verify_to_fixpoint_counting` + `nb5l_cap_exhaustion_declines_not_panics`), so even
/// if a future solver/seed did oscillate, the outcome is a sound decline, never a crash.
#[test]
fn nb5l_high_arity_lemmas_converges_no_panic() {
    use rustc_hash::{FxHashMap, FxHashSet};

    use crate::analyses::borrow_ownership::{
        CrateCtxt, SlotKind,
        borrow_verify::{RepairMode, revalidate, verify_to_fixpoint_counting},
        coherence::add_coherence,
        crate_slots::CrateSlots,
        emit_crate_ownership_constraints,
        origins::compute_origins,
        solver::{KindSolver, SlotRef},
    };
    let n = 32usize; // 32 aliases + x ⇒ a 33-distinct-requirer single-loan edge.
    let aliases: String = (0..n)
        .map(|i| format!("let a{i} = id(x);"))
        .collect::<Vec<_>>()
        .join(" ");
    let uses: String = (0..n)
        .map(|i| format!("*a{i}"))
        .collect::<Vec<_>>()
        .join(" + ");
    let code = format!(
        "unsafe fn id(p: *mut i32) -> *mut i32 {{ p }} \
         unsafe fn f(p: *mut i32) -> i32 {{ let bb = p; let x = id(p); {aliases} *bb = 5; {uses} + *x }}"
    );
    ::utils::compilation::run_compiler_on_str(&code, |tcx| {
        let program = collect_program(tcx);
        let slots = CrateSlots::build(&program);
        // Confirm the shape actually has the high-arity edge (else the regression is vacuous).
        let max_menu = revalidate(&program, &slots, |_s: SlotRef| true, true)
            .values()
            .flatten()
            .map(|e| e.requirers.iter().filter(|r| Some(**r) != e.issuer).count())
            .max()
            .unwrap_or(0);
        assert!(max_menu >= 16, "regression must build a high-arity edge; got menu {max_menu}");
        let run = |mode: RepairMode| {
            let crate_ctxt = CrateCtxt::new(&program);
            let solver = KindSolver::new(&slots);
            let (_s, sel) = emit_crate_ownership_constraints(
                &crate_ctxt,
                &slots,
                &compute_origins(&program),
                &solver,
            )
            .expect("emit");
            for &g in &program.functions {
                let body = tcx.mir_drops_elaborated_and_const_checked(g).borrow();
                add_coherence(&solver, &slots, g, &body);
            }
            RepairMode::with_override(mode, || {
                verify_to_fixpoint_counting(&program, &slots, &solver, &sel, true)
            })
        };
        let (am, ast) = run(RepairMode::ModeA);
        let (lm, lst) = run(RepairMode::Lemmas);
        // No panic (we reached here). Lemmas converges (accepts) — the 2^k oscillation worst case does
        // NOT fire under the pinned seed.
        let am = am.expect("Mode-A must accept the high-arity fan-out");
        let lm = lm.expect("Lemmas must converge (accept), not oscillate to the cap, on high arity");
        assert!(
            lst.rounds <= ast.rounds + 4,
            "high-arity: Lemmas rounds ({}) must stay near Mode-A ({}) — no subset-oscillation blowup",
            lst.rounds, ast.rounds
        );
        // THE HAZARD WITNESS (Codex HIGH follow-through). ≤ law: Lemmas' Ref-set ⊆ Mode-A's. And here
        // the inclusion is STRICT — Lemmas demotes ≥1 slot Mode-A keeps Ref (non-minimal demotion), so
        // `n_ref(lemmas) < n_ref(mode_a)`. This fixture is the shipped regression witness that the
        // empty-context disjunction is ≤ Mode-A, NOT ≡, and that the loss is real (not just theoretical).
        let ref_of = |m: &FxHashMap<SlotRef, SlotKind>| -> FxHashSet<SlotRef> {
            m.iter().filter(|(_, k)| **k == SlotKind::Ref).map(|(s, _)| *s).collect()
        };
        let (ra, rl) = (ref_of(&am), ref_of(&lm));
        assert!(rl.is_subset(&ra), "high-arity: Lemmas Ref-set must be ⊆ Mode-A's (the ≤ law)");
        assert!(
            rl.len() < ra.len(),
            "high-arity: expected Lemmas to lose ≥1 Ref via non-minimal demotion (the regression \
             witness); Mode-A Ref={}, Lemmas Ref={}",
            ra.len(), rl.len()
        );
    })
    .unwrap_or_else(|e| e.raise())
}

/// §NB5-L (Codex MEDIUM) — the cap backstop is repair-mode-dependent: `Lemmas` returns a CONTROLLED
/// decline tagged `cap_exhausted` (the oscillation blowup does not manifest, but Lemmas has no proven
/// linear bound), while `ModeA` PANICS (its linear bound is proven, so a cap hit is a genuine bug).
/// The natural oscillation never reaches the cap, so this forces it with a test-only cap override.
#[test]
fn nb5l_cap_exhaustion_declines_not_panics() {
    use crate::analyses::borrow_ownership::{
        CrateCtxt,
        borrow_verify::{RepairMode, verify_to_fixpoint_counting, with_cap_override},
        coherence::add_coherence,
        crate_slots::CrateSlots,
        emit_crate_ownership_constraints,
        origins::compute_origins,
        solver::KindSolver,
    };
    // An alias cascade that genuinely needs >1 CEGAR round (so cap=1 exhausts).
    let code = "unsafe fn id(p: *mut i32) -> *mut i32 { p } \
                unsafe fn f(p: *mut i32) -> i32 { let x = id(p); *x = 1; let b = p; *b = 2; *x }";
    ::utils::compilation::run_compiler_on_str(code, |tcx| {
        let program = collect_program(tcx);
        let slots = CrateSlots::build(&program);
        let solve = |mode: RepairMode, cap: usize| {
            let crate_ctxt = CrateCtxt::new(&program);
            let solver = KindSolver::new(&slots);
            let (_s, sel) = emit_crate_ownership_constraints(
                &crate_ctxt,
                &slots,
                &compute_origins(&program),
                &solver,
            )
            .expect("emit");
            for &g in &program.functions {
                let body = tcx.mir_drops_elaborated_and_const_checked(g).borrow();
                add_coherence(&solver, &slots, g, &body);
            }
            with_cap_override(cap, || {
                RepairMode::with_override(mode, || {
                    verify_to_fixpoint_counting(&program, &slots, &solver, &sel, true)
                })
            })
        };
        // Sanity: the fixture needs >1 round, else cap=1 would not exhaust.
        let (_m, natural) = solve(RepairMode::ModeA, 999);
        assert!(
            natural.rounds > 1,
            "fixture must need >1 round (got {})",
            natural.rounds
        );
        // Lemmas at cap=1 ⇒ controlled decline, tagged cap_exhausted (NOT a panic, NOT mislabeled).
        let (model, stats) = solve(RepairMode::Lemmas, 1);
        assert!(
            model.is_none() && stats.cap_exhausted,
            "Lemmas cap-exhaustion must be a tagged decline (model={:?}, cap_exhausted={})",
            model.is_some(),
            stats.cap_exhausted
        );
        // Mode-A at cap=1 ⇒ PANIC (proven linear bound; a hit is a real bug). Drop-guards restore the
        // cap/mode on unwind, so this does not leak state into later tests.
        let panicked =
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| solve(RepairMode::ModeA, 1)))
                .is_err();
        assert!(
            panicked,
            "Mode-A cap-exhaustion must PANIC (its linear bound is proven)"
        );
    })
    .unwrap_or_else(|e| e.raise())
}

/// §NB5-L2 commit-necessity audit — helper: run Mode-A to fixpoint capturing the distinct commit set
/// `C` (dedup by slot, first-seen order) and the accepted model. Panics if the fixture declines.
#[cfg(test)]
fn nb5l2_anchor<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
) -> (
    crate::utils::rustc::RustProgram<'tcx>,
    crate::analyses::borrow_ownership::crate_slots::CrateSlots,
    crate::analyses::borrow_ownership::origin_summary::OriginSummaries,
    rustc_hash::FxHashMap<
        crate::analyses::borrow_ownership::solver::SlotRef,
        crate::analyses::borrow_ownership::SlotKind,
    >,
    Vec<(crate::analyses::borrow_ownership::solver::SlotRef, usize)>,
) {
    use crate::analyses::borrow_ownership::{
        CrateCtxt,
        borrow_verify::{
            self, RepairMode, model_accepts_with_flows, verify_to_fixpoint_counting_with_flows,
        },
        coherence::add_coherence,
        crate_slots::CrateSlots,
        emit_crate_ownership_constraints,
        origins::compute_origins,
        solver::KindSolver,
    };
    let program = collect_program(tcx);
    let slots = CrateSlots::build(&program);
    let origins = compute_origins(&program);
    let crate_ctxt = CrateCtxt::new(&program);
    let solver = KindSolver::new(&slots);
    let (_s, sel) =
        emit_crate_ownership_constraints(&crate_ctxt, &slots, &origins, &solver).expect("emit");
    for &g in &program.functions {
        let body = tcx.mir_drops_elaborated_and_const_checked(g).borrow();
        add_coherence(&solver, &slots, g, &body);
    }
    let ((model, _stats), events) = RepairMode::with_override(RepairMode::ModeA, || {
        borrow_verify::with_capture(|| {
            verify_to_fixpoint_counting_with_flows(
                &program,
                &slots,
                origins.native_flows(),
                &solver,
                &sel,
                true,
            )
        })
    });
    let model = model.expect("fixture must accept under Mode-A");
    // FULL-anchor anti-drift: the accepted model must satisfy model_accepts.
    assert!(
        model_accepts_with_flows(&program, &slots, origins.native_flows(), &model, true,),
        "anchor's accepted model must satisfy model_accepts (drift check)"
    );
    (program, slots, origins, model, events)
}

/// §NB5-L2 — distinct commit set (dedup by slot, first-seen order) from the raw `(slot, round)` events.
#[cfg(test)]
fn nb5l2_distinct(
    events: &[(crate::analyses::borrow_ownership::solver::SlotRef, usize)],
) -> Vec<crate::analyses::borrow_ownership::solver::SlotRef> {
    let mut seen = rustc_hash::FxHashSet::default();
    events
        .iter()
        .map(|(s, _)| *s)
        .filter(|s| seen.insert(*s))
        .collect()
}

/// §NB5-L2 — calibrate the probe's two verdicts deterministically on `single_req_cascade`.
/// NECESSARY arm (singleton probe): probing `[ci]` at index 0 leaves the EMPTY commit set, so the
/// re-solve reproduces the anchor's round-1 (pre-commit) state — which HAD a conflict (Mode-A
/// committed ≥1), so it does NOT accept → NECESSARY. Guaranteed for any `ci`, no `|C|` dependence.
/// OVER-PIN arm (injected): append a surviving-`Ref` slot (∉ `C`) to the FULL commit set and probe it
/// — leaving it out keeps the real `C`, so the re-solve reproduces the anchor's ACCEPTING state with
/// that slot `Ref` → OVER-PIN. Both arms fire; the OverPin assertion cannot pass vacuously.
#[cfg(test)]
#[test]
fn nb5l2_probe_necessary_and_injected_overpin() {
    use crate::analyses::borrow_ownership::SlotKind;
    let code = "unsafe fn id(p: *mut i32) -> *mut i32 { p } \
                unsafe fn f(p: *mut i32) -> i32 { let x = id(p); *x = 1; let b = p; *b = 2; *x }";
    ::utils::compilation::run_compiler_on_str(code, |tcx| {
        let (program, slots, origins, model, events) = nb5l2_anchor(tcx);
        let before =
            crate::analyses::borrow_ownership::origin_flow::ORIGIN_DERIVATION_COUNT
                .with(|count| count.get());
        let commit_set = nb5l2_distinct(&events);
        assert!(!commit_set.is_empty(), "cascade must yield >=1 Mode-A commit");
        // NECESSARY arm: singleton probe of any real commit → empty leave-one-out → conflict returns.
        let singleton = [commit_set[0]];
        assert!(
            matches!(
                run::necessity_probe(&program, &slots, &origins, true, &singleton, 0),
                run::ProbeOutcome::Necessary
            ),
            "singleton probe of a genuine commit must be NECESSARY (∅ leave-one-out re-exposes the \
             round-1 conflict)"
        );
        // OVER-PIN arm: inject a surviving-Ref slot (∉ C) as a spurious commit on the FULL set.
        let injected = model
            .iter()
            .filter(|(_, k)| **k == SlotKind::Ref)
            .map(|(s, _)| *s)
            .find(|s| !commit_set.contains(s))
            .expect("fixture must leave >=1 surviving Ref slot outside C");
        let mut with_spurious = commit_set.clone();
        with_spurious.push(injected);
        let spurious_idx = with_spurious.len() - 1;
        assert!(
            matches!(
                run::necessity_probe(&program, &slots, &origins, true, &with_spurious, spurious_idx),
                run::ProbeOutcome::OverPin
            ),
            "a spurious ¬ref on a surviving Ref slot must probe OVER-PIN (dropping it still accepts, \
             slot Ref)"
        );
        let after =
            crate::analyses::borrow_ownership::origin_flow::ORIGIN_DERIVATION_COUNT
                .with(|count| count.get());
        assert_eq!(
            after, before,
            "necessity probes must reuse the anchor's retained origin flows"
        );
    })
    .unwrap_or_else(|e| e.raise())
}

/// §NB5-L2 — the probe finds a GENUINE accumulation over-pin (not just an injected one).
/// `single_req_cascade` drives Mode-A to `|C|=2`: the round-1 commit induces a second, but demoting
/// only the second (keeping the first `Ref`) still accepts — so the first is a real over-pin. This is
/// exactly the L2 headroom the audit measures, and it pins that a natural Mode-A commit set contains
/// over-pins the probe detects. At least one real commit must probe OVER-PIN and at least one NECESSARY
/// (an all-necessary or all-over-pin verdict here would signal the probe collapsed a distinction).
#[cfg(test)]
#[test]
fn nb5l2_probe_finds_natural_accumulation_overpin() {
    let code = "unsafe fn id(p: *mut i32) -> *mut i32 { p } \
                unsafe fn f(p: *mut i32) -> i32 { let x = id(p); *x = 1; let b = p; *b = 2; *x }";
    ::utils::compilation::run_compiler_on_str(code, |tcx| {
        let (program, slots, origins, _model, events) = nb5l2_anchor(tcx);
        let commit_set = nb5l2_distinct(&events);
        assert!(
            commit_set.len() >= 2,
            "cascade must yield >=2 commits (got {})",
            commit_set.len()
        );
        let (mut overpins, mut necessary) = (0usize, 0usize);
        for i in 0..commit_set.len() {
            match run::necessity_probe(&program, &slots, &origins, true, &commit_set, i) {
                run::ProbeOutcome::OverPin => overpins += 1,
                run::ProbeOutcome::Necessary => necessary += 1,
            }
        }
        assert!(
            overpins >= 1,
            "the cascade must contain >=1 natural accumulation over-pin (found {overpins})"
        );
        assert!(
            necessary >= 1,
            "the cascade must retain >=1 necessary commit (found {necessary}) — else the probe \
             collapsed the distinction"
        );
    })
    .unwrap_or_else(|e| e.raise())
}

/// §NB5-L2 — the witnessed-joint greedy set is a CERTIFIED lower bound: `na_joint_witnessed=true`
/// (one solve with only the retained set demoted leaves EVERY removed slot `Ref` and accepts), and the
/// count is bounded by `|C|`. The certificate — NOT any relation to the independent count — is the
/// soundness property: whatever set the greedy commits to, the witness proves it is jointly recoverable.
///
/// Greedy and independent are INCOMPARABLE (do not assert `joint ≤ indep`): independent demotes ALL
/// other commits at once, so it MISSES a slot recoverable only while other removed slots stay `Ref`
/// (e.g. coherence-equated slots — demoting the partner forces the slot `¬ref`, but keeping it `Ref`
/// does not). The greedy, un-demoting removals as it goes, captures those JOINT recoveries — so
/// `joint > indep` occurs at corpus scale (libtree: indep 3, witnessed-joint 7, all certified). It can
/// also be `<` if the greedy order spends a removal that blocks two others. The witness is what makes
/// the count sound regardless of direction; the independent count is a labeled diagnostic only.
#[cfg(test)]
#[test]
fn nb5l2_greedy_witnessed_joint_certified() {
    let fixtures: [(&str, &str); 3] = [
        (
            "single_req_cascade",
            "unsafe fn id(p: *mut i32) -> *mut i32 { p } \
             unsafe fn f(p: *mut i32) -> i32 { let x = id(p); *x = 1; let b = p; *b = 2; *x }",
        ),
        (
            "two_requirer",
            "unsafe fn id(p: *mut i32) -> *mut i32 { p } \
             unsafe fn f(p: *mut i32) -> i32 { let base = id(p); let a = id(base); let b = id(base); \
             let w = p; *w = 9; *a + *b }",
        ),
        (
            "asymmetric",
            "unsafe fn id(p: *mut i32) -> *mut i32 { p } \
             unsafe fn f(p: *mut i32) -> i32 { let a = id(p); let b = id(p); let d = id(b); \
             *a = 1; *b = 2; *d = 3; let w = p; *w = 4; *a + *b + *d }",
        ),
    ];
    for (tag, code) in fixtures {
        ::utils::compilation::run_compiler_on_str(code, |tcx| {
            let (program, slots, origins, model, events) = nb5l2_anchor(tcx);
            let mut row = report::Row::default();
            run::run_necessity_audit(
                &program,
                &slots,
                &origins,
                true,
                &Some(model),
                &events,
                &mut row,
            );
            let get = |k: &str| {
                row.get(k)
                    .unwrap_or_else(|| panic!("{tag}: audit did not emit {k}"))
                    .to_string()
            };
            assert_eq!(get("na_status"), "ok", "{tag}: audit status");
            // The CERTIFICATE: the greedy removed set is jointly realizable (all removed Ref + accept).
            assert_eq!(
                get("na_joint_witnessed"),
                "true",
                "{tag}: the greedy removed set must be jointly witnessed (all removed Ref + accept)"
            );
            let joint: usize = get("na_overpins").parse().unwrap();
            let total: usize = get("na_commits_total").parse().unwrap();
            assert!(
                joint <= total,
                "{tag}: witnessed-joint ({joint}) must be <= |C| ({total})"
            );
            // Both counts are emitted (rider 5) — the independent as a labeled diagnostic.
            assert!(
                row.get("na_indep_overpins").is_some(),
                "{tag}: independent count must be emitted"
            );
        })
        .unwrap_or_else(|e| e.raise())
    }
}

/// §NB5-L2 (Codex F3) — the audit capture is Mode-A-ONLY: under `CRAT_BO_REPAIR=lemmas` the CEGAR loop
/// takes the `Lemmas` branch, which does NOT record commit events, so `with_capture` returns empty. The
/// `run_bo` guard rests on this — it refuses `repair != ModeA` with `na_status=wrong-repair-mode` rather
/// than publishing a plausible-but-meaningless zero audit. Mode-A on the same fixture DOES capture.
#[cfg(test)]
#[test]
fn nb5l2_capture_is_mode_a_only() {
    use crate::analyses::borrow_ownership::{
        CrateCtxt,
        borrow_verify::{self, RepairMode, verify_to_fixpoint_counting},
        coherence::add_coherence,
        crate_slots::CrateSlots,
        emit_crate_ownership_constraints,
        origins::compute_origins,
        solver::KindSolver,
    };
    let code = "unsafe fn id(p: *mut i32) -> *mut i32 { p } \
                unsafe fn f(p: *mut i32) -> i32 { let x = id(p); *x = 1; let b = p; *b = 2; *x }";
    ::utils::compilation::run_compiler_on_str(code, |tcx| {
        let program = collect_program(tcx);
        let slots = CrateSlots::build(&program);
        let origins = compute_origins(&program);
        let run_mode = |mode: RepairMode| {
            let crate_ctxt = CrateCtxt::new(&program);
            let solver = KindSolver::new(&slots);
            let (_s, sel) =
                emit_crate_ownership_constraints(&crate_ctxt, &slots, &origins, &solver)
                    .expect("emit");
            for &g in &program.functions {
                let body = tcx.mir_drops_elaborated_and_const_checked(g).borrow();
                add_coherence(&solver, &slots, g, &body);
            }
            let ((_model, stats), events) = RepairMode::with_override(mode, || {
                borrow_verify::with_capture(|| {
                    verify_to_fixpoint_counting(&program, &slots, &solver, &sel, true)
                })
            });
            (stats.repair, events)
        };
        let (mode_a_repair, mode_a_events) = run_mode(RepairMode::ModeA);
        assert_eq!(
            mode_a_repair,
            RepairMode::ModeA,
            "Mode-A run must stamp ModeA"
        );
        assert!(
            !mode_a_events.is_empty(),
            "Mode-A must capture commits on a conflict fixture"
        );
        let (lemmas_repair, lemmas_events) = run_mode(RepairMode::Lemmas);
        assert_eq!(
            lemmas_repair,
            RepairMode::Lemmas,
            "Lemmas run must stamp Lemmas"
        );
        assert!(
            lemmas_events.is_empty(),
            "Lemmas must capture NO commit events — the audit is Mode-A-only (got {} events)",
            lemmas_events.len()
        );
    })
    .unwrap_or_else(|e| e.raise())
}

// ---------------------------------------------------------------------------
// §L2 RED — feature-off base golden captured at ae6f334.
// ---------------------------------------------------------------------------

const L2_FEATURE_OFF_BASE_SHA: &str = "ae6f334eca78cbaa254bfb3afc65e3c31130153d";
const L2_FEATURE_OFF_OUTPUT_LEN: usize = 212;
const L2_FEATURE_OFF_OUTPUT_SHA256: &str =
    "7e625bb8120839583f7cf64d19c6b87a342d2525bca5bf36dfc115e4a003a17a";
const L2_FEATURE_OFF_SOURCE_DROP: &str =
    include_str!("analyses/borrow_ownership/testdata/l2_feature_off_source_drop.rs");
const L2_FEATURE_OFF_SINK_DROP: &str =
    include_str!("analyses/borrow_ownership/testdata/l2_feature_off_sink_drop.rs");

fn l2_feature_off_capture_program(fixture: &str, source: &str) -> String {
    use std::fmt::Write;

    use crate::analyses::borrow_ownership::{
        CrateCtxt,
        borrow_verify::{RepairMode, model_accepts, verify_to_fixpoint_counting},
        coherence::add_coherence,
        crate_slots::CrateSlots,
        emit_crate_ownership_constraints,
        mutability_facts::MutFacts,
        origins::compute_origins,
        solver::KindSolver,
    };

    ::utils::compilation::run_compiler_on_str(source, |tcx| {
        let program = collect_program(tcx);
        let slots = CrateSlots::build(&program);
        let origins = compute_origins(&program);
        let mut rendered = String::new();

        for (mutability, mut_facts) in [
            ("from_program", MutFacts::from_program(&program)),
            ("all_mut", MutFacts::all_mut()),
        ] {
            let crate_ctxt = CrateCtxt::new(&program);
            let solver = KindSolver::new(&slots);
            let (_emission, selectors) =
                emit_crate_ownership_constraints(&crate_ctxt, &slots, &origins, &solver)
                    .expect("L2 feature-off golden emission");
            for &fn_did in &program.functions {
                let body = tcx.mir_drops_elaborated_and_const_checked(fn_did).borrow();
                add_coherence(&solver, &slots, fn_did, &body);
            }

            let (model, stats) = RepairMode::with_override(RepairMode::ModeA, || {
                verify_to_fixpoint_counting(&program, &slots, &solver, &selectors, &mut_facts)
            });
            let model =
                model.unwrap_or_else(|| panic!("{fixture}/{mutability}: base Mode-A must accept"));
            let accepted = model_accepts(&program, &slots, &model, &mut_facts);
            assert!(
                accepted,
                "{fixture}/{mutability}: accepted model must satisfy model_accepts"
            );

            let (reported_model, dropped) = solver
                .model_kinds_relaxing_reporting(&selectors)
                .unwrap_or_else(|| {
                    panic!("{fixture}/{mutability}: reporting solve must remain SAT")
                });
            assert_eq!(
                reported_model, model,
                "{fixture}/{mutability}: reporting solve must reproduce the accepted model"
            );

            let dropped_selectors = l2_feature_off_dropped_selectors(&selectors, &dropped);
            assert_eq!(
                stats.dropped_sources,
                dropped_selectors
                    .iter()
                    .filter(|selector| selector.starts_with("source:"))
                    .count(),
                "{fixture}/{mutability}: source-drop counter/reporting mismatch"
            );
            assert_eq!(
                stats.dropped_sinks,
                dropped_selectors
                    .iter()
                    .filter(|selector| selector.starts_with("sink:"))
                    .count(),
                "{fixture}/{mutability}: sink-drop counter/reporting mismatch"
            );

            let mut kinds: Vec<(String, _)> = model
                .iter()
                .map(|(&slot, &kind)| (run::fmt_slot(&program, &slots, slot), kind))
                .collect();
            kinds.sort_by(|(left, _), (right, _)| left.cmp(right));

            writeln!(rendered, "case={fixture}/{mutability}").unwrap();
            writeln!(rendered, "accepted={accepted}").unwrap();
            writeln!(rendered, "stats.repair={}", stats.repair.label()).unwrap();
            writeln!(rendered, "stats.rounds={}", stats.rounds).unwrap();
            writeln!(
                rendered,
                "stats.commits_conflict={}",
                stats.commits_conflict
            )
            .unwrap();
            writeln!(
                rendered,
                "stats.commits_per_round={:?}",
                stats.commits_per_round
            )
            .unwrap();
            writeln!(rendered, "stats.dropped_sources={}", stats.dropped_sources).unwrap();
            writeln!(rendered, "stats.dropped_sinks={}", stats.dropped_sinks).unwrap();
            let field_decline = stats
                .field_conflict_decline
                .map(|slot| run::fmt_slot(&program, &slots, slot))
                .unwrap_or_else(|| "-".to_string());
            writeln!(rendered, "stats.field_conflict_decline={field_decline}").unwrap();
            writeln!(rendered, "stats.cap_exhausted={}", stats.cap_exhausted).unwrap();
            writeln!(
                rendered,
                "dropped_selectors={}",
                if dropped_selectors.is_empty() {
                    "-".to_string()
                } else {
                    dropped_selectors.join(",")
                }
            )
            .unwrap();
            for (slot, kind) in kinds {
                writeln!(rendered, "model.{slot}={kind:?}").unwrap();
            }
            writeln!(rendered, "end_case").unwrap();
        }

        rendered
    })
    .unwrap_or_else(|error| error.raise())
}

fn l2_feature_off_dropped_selectors(
    selectors: &crate::analyses::borrow_ownership::solver::Selectors,
    dropped: &[z3::ast::Bool],
) -> Vec<String> {
    let mut names = Vec::new();
    for literal in dropped {
        if let Some(index) = selectors
            .sources()
            .iter()
            .position(|selector| selector == literal)
        {
            names.push(format!("source:{index}"));
        } else if let Some(index) = selectors
            .sinks()
            .iter()
            .position(|selector| selector == literal)
        {
            names.push(format!("sink:{index}"));
        } else {
            panic!("L2 feature-off reporting solve returned an unknown selector");
        }
    }
    names.sort();
    names
}

fn l2_feature_off_capture() -> (String, String, crate::BytemuckDependency) {
    use std::{fmt::Write, process::Command};

    let rustc = Command::new("rustc")
        .arg("--version")
        .output()
        .expect("query rustc version for L2 base golden");
    assert!(rustc.status.success(), "rustc --version must succeed");
    let rustc = String::from_utf8(rustc.stdout)
        .expect("rustc version must be UTF-8")
        .trim()
        .to_string();

    let mut snapshot = String::new();
    writeln!(snapshot, "base.sha={L2_FEATURE_OFF_BASE_SHA}").unwrap();
    writeln!(snapshot, "toolchain.rustc={rustc}").unwrap();
    writeln!(snapshot, "z3.full_version={}", z3::full_version()).unwrap();
    writeln!(snapshot, "z3.smt.random_seed=0").unwrap();
    writeln!(snapshot, "z3.sat.random_seed=0").unwrap();
    snapshot.push_str(&l2_feature_off_capture_program(
        "source_drop",
        L2_FEATURE_OFF_SOURCE_DROP,
    ));
    snapshot.push_str(&l2_feature_off_capture_program(
        "sink_drop",
        L2_FEATURE_OFF_SINK_DROP,
    ));
    let (output, bytemuck) =
        ::utils::compilation::run_compiler_on_str(L2_FEATURE_OFF_SOURCE_DROP, |tcx| {
            crate::replace_local_borrows(&crate::Config::default(), tcx)
        })
        .unwrap_or_else(|error| error.raise());
    writeln!(snapshot, "rewrite.source_drop.bytemuck={bytemuck:?}").unwrap();
    (snapshot, output, bytemuck)
}

fn l2_decode_hex(encoded: &str) -> Vec<u8> {
    fn nibble(byte: u8) -> u8 {
        match byte {
            b'0'..=b'9' => byte - b'0',
            b'a'..=b'f' => byte - b'a' + 10,
            b'A'..=b'F' => byte - b'A' + 10,
            _ => panic!("L2 feature-off golden contains non-hex byte {byte:?}"),
        }
    }

    let digits: Vec<u8> = encoded
        .bytes()
        .filter(|byte| !byte.is_ascii_whitespace())
        .collect();
    assert_eq!(
        digits.len() % 2,
        0,
        "L2 feature-off golden contains an odd number of hex digits"
    );
    digits
        .chunks_exact(2)
        .map(|pair| (nibble(pair[0]) << 4) | nibble(pair[1]))
        .collect()
}

fn l2_sha256_hex(input: &[u8]) -> String {
    const ROUND: [u32; 64] = [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4,
        0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe,
        0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f,
        0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
        0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc,
        0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
        0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116,
        0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
        0xc67178f2,
    ];
    let mut state = [
        0x6a09e667u32,
        0xbb67ae85,
        0x3c6ef372,
        0xa54ff53a,
        0x510e527f,
        0x9b05688c,
        0x1f83d9ab,
        0x5be0cd19,
    ];
    let bit_len = u64::try_from(input.len())
        .expect("L2 feature-off golden length fits u64")
        .checked_mul(8)
        .expect("L2 feature-off golden bit length fits u64");
    let mut padded = input.to_vec();
    padded.push(0x80);
    while padded.len() % 64 != 56 {
        padded.push(0);
    }
    padded.extend_from_slice(&bit_len.to_be_bytes());

    for block in padded.chunks_exact(64) {
        let mut words = [0u32; 64];
        for (word, bytes) in words[..16].iter_mut().zip(block.chunks_exact(4)) {
            *word = u32::from_be_bytes(bytes.try_into().expect("four-byte SHA-256 word"));
        }
        for index in 16..64 {
            let s0 = words[index - 15].rotate_right(7)
                ^ words[index - 15].rotate_right(18)
                ^ (words[index - 15] >> 3);
            let s1 = words[index - 2].rotate_right(17)
                ^ words[index - 2].rotate_right(19)
                ^ (words[index - 2] >> 10);
            words[index] = words[index - 16]
                .wrapping_add(s0)
                .wrapping_add(words[index - 7])
                .wrapping_add(s1);
        }

        let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] = state;
        for index in 0..64 {
            let sum1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let choose = (e & f) ^ (!e & g);
            let temp1 = h
                .wrapping_add(sum1)
                .wrapping_add(choose)
                .wrapping_add(ROUND[index])
                .wrapping_add(words[index]);
            let sum0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
            let majority = (a & b) ^ (a & c) ^ (b & c);
            let temp2 = sum0.wrapping_add(majority);
            h = g;
            g = f;
            f = e;
            e = d.wrapping_add(temp1);
            d = c;
            c = b;
            b = a;
            a = temp1.wrapping_add(temp2);
        }
        for (slot, value) in state.iter_mut().zip([a, b, c, d, e, f, g, h]) {
            *slot = slot.wrapping_add(value);
        }
    }

    state.iter().map(|word| format!("{word:08x}")).collect()
}

#[test]
fn l2_red_feature_off_matches_base_ae6f334() {
    let explicit_off = match std::env::var("CRAT_BO_L2_GUARDED_COMMITS") {
        Ok(value) => {
            assert_eq!(
                value, "0",
                "the feature-off base-golden test requires CRAT_BO_L2_GUARDED_COMMITS=0"
            );
            true
        }
        Err(std::env::VarError::NotPresent) => false,
        Err(error) => panic!("CRAT_BO_L2_GUARDED_COMMITS is not valid Unicode: {error}"),
    };
    assert!(
        !crate::analyses::borrow_ownership::l2::enabled_from_env(),
        "CRAT_BO_L2_GUARDED_COMMITS=0 must resolve feature-off"
    );
    // The exact RED evidence command sets the feature flag explicitly and filters
    // this test into a fresh, single-threaded process. Pin both seeds before its
    // first z3 operation, matching the official Mode-A worker contract. An
    // ordinary full-suite run leaves the flag absent and retains z3's defaults,
    // avoiding a process-global write in the parallel runner.
    if explicit_off {
        z3::set_global_param("smt.random_seed", "0");
        z3::set_global_param("sat.random_seed", "0");
    }

    let (actual_snapshot, actual_output, actual_bytemuck) = l2_feature_off_capture();
    assert_eq!(
        actual_snapshot,
        include_str!("analyses/borrow_ownership/testdata/l2_feature_off_base_ae6f334.snap"),
        "feature-off Mode-A semantics drifted from the approved ae6f334 base"
    );
    assert_eq!(
        actual_bytemuck,
        crate::BytemuckDependency::None,
        "source-drop BytemuckDependency drifted from the approved ae6f334 base"
    );
    // Storage-encoding contract: the authoritative 212-byte capture is hex so
    // editors, Git, and CI cannot normalize its terminal byte. Never normalize
    // either side or replace this with raw-text include_bytes!: both alternatives
    // weaken the exact base anchor.
    let golden_output = l2_decode_hex(include_str!(
        "analyses/borrow_ownership/testdata/l2_feature_off_base_ae6f334.output.hex"
    ));
    assert_eq!(
        l2_sha256_hex(b""),
        "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
        "L2 feature-off SHA-256 helper failed its standard empty-input vector"
    );
    assert_eq!(
        golden_output.len(),
        L2_FEATURE_OFF_OUTPUT_LEN,
        "encoded feature-off golden no longer decodes to the authoritative capture length"
    );
    assert_eq!(
        l2_sha256_hex(&golden_output),
        L2_FEATURE_OFF_OUTPUT_SHA256,
        "encoded feature-off golden no longer matches the captured artifact's SHA-256"
    );
    assert_eq!(
        actual_output.as_bytes(),
        golden_output,
        "feature-off generated output is not byte-identical to the approved ae6f334 base"
    );
}

#[cfg(test)]
mod crown_projection_red_tests {
    use std::collections::BTreeSet;

    use rustc_hash::FxHashMap;

    use super::crown_projection::{
        BoFullScopeCounts, LegacyBackingKind, LegacyDecisionKind, MappingCompleteness, ModelKind,
        ProjectionOutcome, bo_full_scope_csv_rows, classify_legacy_safe_backing,
        classify_legacy_subjects, classify_model_slots, csv_cell, legacy_full_scope_csv_row,
        parse_bo_full_scope_counts, parse_legacy_decisions, parse_legacy_full_scope_histogram,
        project_model_for_universe,
    };

    #[test]
    fn crown_projection_csv_preserves_nul_as_visible_text() {
        assert_eq!(csv_cell("a\0b"), "a\\0b");
        assert_eq!(csv_cell("a,b"), "\"a,b\"");
    }

    #[test]
    fn crown_projection_uses_all_mapped_slots_and_partitions_safe_groups() {
        assert_eq!(
            classify_model_slots(
                MappingCompleteness::Complete,
                &[ModelKind::Ref, ModelKind::Ref]
            ),
            ProjectionOutcome::RefBacked
        );
        assert_eq!(
            classify_model_slots(
                MappingCompleteness::Complete,
                &[ModelKind::Ref, ModelKind::Owning]
            ),
            ProjectionOutcome::OwningBacked
        );
        assert_eq!(
            classify_model_slots(
                MappingCompleteness::Complete,
                &[ModelKind::Ref, ModelKind::Raw]
            ),
            ProjectionOutcome::Remaining
        );
        assert_eq!(
            classify_model_slots(MappingCompleteness::Partial, &[ModelKind::Ref]),
            ProjectionOutcome::Unmapped
        );
        assert_eq!(
            classify_model_slots(MappingCompleteness::Complete, &[]),
            ProjectionOutcome::Unmapped
        );
    }

    #[test]
    fn crown_projection_legacy_safe_kind_list_is_closed_and_all_subjects_apply() {
        let safe = [
            LegacyDecisionKind::Ref,
            LegacyDecisionKind::OptRef,
            LegacyDecisionKind::Slice,
            LegacyDecisionKind::SliceCursor,
            LegacyDecisionKind::Box,
            LegacyDecisionKind::OptBox,
            LegacyDecisionKind::BoxedSlice,
            LegacyDecisionKind::OptBoxedSlice,
        ];
        assert_eq!(
            classify_legacy_subjects(MappingCompleteness::Complete, &safe),
            ProjectionOutcome::Eliminated
        );
        assert_eq!(
            classify_legacy_subjects(
                MappingCompleteness::Complete,
                &[LegacyDecisionKind::Ref, LegacyDecisionKind::Raw]
            ),
            ProjectionOutcome::Remaining
        );
        assert_eq!(
            classify_legacy_subjects(MappingCompleteness::Empty, &[]),
            ProjectionOutcome::Unmapped
        );
    }

    #[test]
    fn crown_projection_parses_final_legacy_subjects_without_collapsing_duplicates() {
        let input = "\
[pointer-decision] subject=local fn=src::sample::f name=x original=*mut i32 span=a final=Ref(true)
[pointer-decision] subject=local fn=src::sample::f name=x original=*mut i32 span=b final=Box
[pointer-decision] subject=param fn=src::sample::f index=0 name=p original=*mut i32 span=c final=Raw(true)
[pointer-decision] subject=return fn=src::sample::f original=*mut i32 final=OptRef(true)
";
        let records = parse_legacy_decisions(input).expect("legacy decisions");
        assert_eq!(records.len(), 4);
        assert_eq!(
            records[0].declaration_key.as_deref(),
            Some("src::sample::f::x")
        );
        assert_eq!(
            records[1].declaration_key.as_deref(),
            Some("src::sample::f::x")
        );
        assert_eq!(
            records[2].declaration_key.as_deref(),
            Some("src::sample::f::p")
        );
        assert_eq!(records[3].declaration_key, None);
    }

    #[test]
    fn crown_projection_classifies_legacy_safe_backing_with_box_precedence() {
        assert_eq!(
            classify_legacy_safe_backing(&[LegacyDecisionKind::Ref, LegacyDecisionKind::Box])
                .expect("safe mixed group"),
            LegacyBackingKind::BoxFamily
        );
        assert_eq!(
            classify_legacy_safe_backing(&[
                LegacyDecisionKind::OptRef,
                LegacyDecisionKind::SliceCursor,
            ])
            .expect("safe reference/slice group"),
            LegacyBackingKind::RefSlice
        );
        assert!(classify_legacy_safe_backing(&[]).is_err());
        assert!(
            classify_legacy_safe_backing(&[LegacyDecisionKind::Ref, LegacyDecisionKind::Raw])
                .is_err()
        );
    }

    #[test]
    fn crown_projection_strictly_parses_bo_full_scope_counts() {
        let input = "\
running 1 test
BOC1 program=sample mode=bo slots_total=20 status=ok n_ref=11 n_raw=7 n_own=2 n_ref_d0=9 n_raw_d0=6 n_own_d0=1
test result: ok
";
        let counts = parse_bo_full_scope_counts(input).expect("BO full-scope counts");
        assert_eq!(counts.program, "sample");
        assert_eq!(counts.slots_total, 20);
        assert_eq!(counts.n_ref, 11);
        assert_eq!(counts.n_own, 2);
        assert_eq!(counts.n_raw, 7);
        assert_eq!(counts.d0_local_slots(), 16);

        assert!(parse_bo_full_scope_counts(input.replace(" n_raw=7", "").as_str()).is_err());
        assert!(
            parse_bo_full_scope_counts(input.replace(" n_own=2", " n_raw=7 n_own=2").as_str())
                .is_err()
        );
        assert!(parse_bo_full_scope_counts(&input.replace("mode=bo", "mode=legacy")).is_err());
        assert!(parse_bo_full_scope_counts(&input.replace("status=ok", "status=failed")).is_err());
        assert!(parse_bo_full_scope_counts(&format!("{input}{input}")).is_err());
        assert!(
            parse_bo_full_scope_counts(&input.replace("slots_total=20", "slots_total=19")).is_err()
        );
        assert!(parse_bo_full_scope_counts(&input.replace("n_raw_d0=6", "n_raw_d0=18")).is_err());
        assert!(
            parse_bo_full_scope_counts(
                &input
                    .replace("n_ref_d0=9", "n_ref_d0=12")
                    .replace("n_raw_d0=6", "n_raw_d0=3"),
            )
            .is_err()
        );
    }

    #[test]
    fn crown_projection_emits_exact_bo_full_scope_csv_rows() {
        let counts = BoFullScopeCounts {
            program: "sample".to_owned(),
            slots_total: 20,
            n_ref: 11,
            n_own: 2,
            n_raw: 7,
            n_ref_d0: 9,
            n_own_d0: 1,
            n_raw_d0: 6,
        };
        assert_eq!(
            bo_full_scope_csv_rows("Mode-A L2-off", &counts).expect("BO rows"),
            "\
sample,Mode-A L2-off,all slots,BO local + field slots at all pointer depths,20,11,2,7,35.00,PASS: n_ref + n_own + n_raw = slots_total
sample,Mode-A L2-off,d0 local slots,BO depth-0 local slots only; fields excluded,16,9,1,6,37.50,PASS: n_ref + n_own + n_raw = slots_total
"
        );
    }

    #[test]
    fn crown_projection_strictly_parses_legacy_full_scope_histogram() {
        let input = "\
[pointer-decision] subject=local fn=f name=a original=*mut i32 final=Ref(true)
[pointer-decision] subject=param fn=f name=b original=*mut i32 final=Ref(false)
[pointer-decision] subject=return fn=f original=*mut i32 final=OptRef(true)
[pointer-decision] subject=field owner=S name=x original=*mut i32 final=Slice(false)
[pointer-decision] subject=local fn=f name=c original=*mut i32 final=SliceCursor(true)
[pointer-decision] subject=local fn=f name=d original=*mut i32 final=Box
[pointer-decision] subject=local fn=f name=e original=*mut i32 final=OptBox
[pointer-decision] subject=local fn=f name=f original=*mut i32 final=BoxedSlice
[pointer-decision] subject=local fn=f name=g original=*mut i32 final=OptBoxedSlice
[pointer-decision] subject=local fn=f name=h original=*mut i32 final=Raw(false)
[pointer-decision] subject=local fn=f name=i original=*mut i32 final=Raw(true)
[pointer-decision] subject=local fn=f name=j original=*mut i32 final=None
";
        let counts = parse_legacy_full_scope_histogram(input).expect("legacy full-scope histogram");
        assert_eq!(counts.subjects_total(), 12);
        assert_eq!(counts.ref_count(), 2);
        assert_eq!(counts.opt_ref_count(), 1);
        assert_eq!(counts.slice_count(), 1);
        assert_eq!(counts.slice_cursor_count(), 1);
        assert_eq!(counts.box_family_count(), 4);
        assert_eq!(counts.raw_false, 1);
        assert_eq!(counts.raw_true, 1);
        assert_eq!(counts.none, 1);

        assert!(
            parse_legacy_full_scope_histogram(
                "[pointer-decision] subject=local fn=f name=x final=UnknownKind\n"
            )
            .is_err()
        );
    }

    #[test]
    fn crown_projection_emits_exact_legacy_full_scope_csv_rows() {
        let counts = parse_legacy_full_scope_histogram(
            "\
[pointer-decision] subject=local fn=f name=a final=Ref(true)
[pointer-decision] subject=local fn=f name=b final=Box
[pointer-decision] subject=local fn=f name=c final=Raw(false)
[pointer-decision] subject=local fn=f name=d final=None
",
        )
        .expect("legacy counts");
        assert_eq!(
            legacy_full_scope_csv_row("sample", "measured", Some(&counts)).expect("legacy row"),
            "\
sample,measured,all legacy pre-transform decision subjects; final decision kind,4,1,0,0,0,1,0,0,0,1,0,1,2,1,1,PASS: Σ final kinds + None = subjects_total
"
        );
        assert_eq!(
            legacy_full_scope_csv_row(
                "urlparser",
                "unmeasurable: urlparser pre-seam parser panic",
                None,
            )
            .expect("unmeasurable row"),
            "urlparser,unmeasurable: urlparser pre-seam parser panic,all legacy pre-transform decision subjects; final decision kind,,,,,,,,,,,,,,,,\n"
        );
    }

    #[test]
    fn crown_projection_maps_debug_declarations_through_existing_mir_groups() {
        use crate::analyses::borrow_ownership::{
            SlotKind, crate_slots::CrateSlots, slots::SlotId, solver::SlotRef,
        };

        ::utils::compilation::run_compiler_on_str(
            "pub unsafe fn f(p: *mut i32) -> i32 { let copy = p; *copy }",
            |tcx| {
                let program = super::collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let did = program.functions[0];
                let key = format!("{}::p", tcx.def_path_str(did));
                let universe = BTreeSet::from([key.clone()]);
                let mut model = FxHashMap::default();
                for (&fn_did, slot_universe) in &slots.fn_local_slots {
                    for index in 0..slot_universe.len() {
                        model.insert(
                            SlotRef::Local(fn_did, SlotId::from_usize(index)),
                            SlotKind::Ref,
                        );
                    }
                }

                let projected =
                    project_model_for_universe(tcx, &program, &slots, &model, &universe);
                let record = &projected[&key];
                assert_eq!(record.completeness, MappingCompleteness::Complete);
                assert_eq!(record.outcome, ProjectionOutcome::RefBacked);
                assert!(record.mapped_mir_locals >= 1);
                assert!(record.mapped_slots >= 1);

                for kind in model.values_mut() {
                    *kind = SlotKind::Raw;
                }
                let projected =
                    project_model_for_universe(tcx, &program, &slots, &model, &universe);
                assert_eq!(projected[&key].outcome, ProjectionOutcome::Remaining);
            },
        )
        .unwrap_or_else(|error| error.raise());
    }
}
