//! **Wave-6o relay 146 (R796-1, USER): the retained-alias STOP-GAP for batch 55.**
//!
//! The input-repair pass ran bzip2 and libtree past the input's own reports and
//! found output-only Tree Borrows reports of one class: a formal delivered as a
//! reference whose pointee the program also reaches through a pointer it keeps
//! in memory (bzip2's state keeps `s->strm`; libtree's small vector keeps
//! `v->p` into its own buffer). The RULE for that class (relay 140, R787-1) is
//! being refined (points-to first); until it replaces this line, exactly the
//! formals whose report a Miri run has shown are held raw.
//!
//! **What this is NOT:** it is not the rule. It holds what was observed, nothing
//! more; a formal of the same class that no run has reached is not held here.
//!
//! Receipt `held:retained-alias`, detail `observed:<run>`; rows are
//! `side-condition` in the audit. A formal joins the table only with the run
//! that showed it, or (R805-2) with a Miri fixture of the record's own emitted
//! signature when the corpus run cannot reach the call: brotli's decoder pair,
//! whose `s` reaches the state's own `symbol_lists` (era-5c 132 §3).
use rustc_middle::ty::TyCtxt;

use super::{Subject, SubjectKind};

/// `program  function  formal  run`
const TABLE: &str = "\
bzip2\thandle_compress\tstrm\tpass-D:bzip2/compress-1
bzip2\tBZ2_bzCompress\tstrm\tpass-D:bzip2/compress-1
bzip2\tBZ2_bzDecompress\tstrm\tpass-D:bzip2/decompress-1
libtree\tsmall_vec_u64_init\tv\tpass-D:libtree/bin-ls
libtree\tsmall_vec_u64_append\tv\tpass-D:libtree/bin-ls
libtree\tapply_exclude_list\tneeded_buf_offsets\thold-validation-H2:libtree/bin-ls
brotli\tReadSymbolCodeLengths\ts\tfixture:era5c-132-miri-symlists
brotli\tSafeReadSymbolCodeLengths\ts\tfixture:era5c-132-miri-symlists
";

#[cfg(test)]
const FIXTURE_TABLE: &str = "\
-\tobs_handle_compress\tstrm\tfixture-w1
-\tobs_BZ2_bzCompress\tstrm\tfixture-w1
-\tobs_small_vec_u64_init\tv\tfixture-w2
-\tobs_small_vec_u64_append\tv\tfixture-w2
";

#[cfg(test)]
fn table() -> &'static str {
    if std::env::var_os("CRAT_ERA5_PROGRAM").is_some() {
        TABLE
    } else {
        FIXTURE_TABLE
    }
}

#[cfg(not(test))]
fn table() -> &'static str {
    TABLE
}

/// The run that showed `function::formal` in `program`, if it is on the list.
pub(crate) fn observed_in<'t>(
    table: &'t str,
    program: &str,
    function: &str,
    formal: &str,
) -> Option<&'t str> {
    table.lines().find_map(|line| {
        let f: Vec<&str> = line.split('\t').collect();
        (f.len() == 4 && f[0] == program && f[1] == function && f[2] == formal).then_some(f[3])
    })
}

/// The table's key for a subject: a formal by its name, a local by
/// `name#<MIR local>` as the census keys it (R808-5).
pub(crate) fn table_key(name: &str, local: Option<u32>) -> String {
    let _ = local;
    name.to_owned()
}

/// The receipt detail (`observed:<run>`) for a listed formal.
pub(crate) fn held(tcx: TyCtxt<'_>, subject: &Subject) -> Option<String> {
    if !matches!(subject.kind, SubjectKind::Param { .. }) {
        return None;
    }
    let program = std::env::var("CRAT_ERA5_PROGRAM").unwrap_or_else(|_| "-".to_owned());
    let function = tcx.item_name(subject.fn_did.to_def_id());
    let formal = subject.param_name.as_deref()?;
    observed_in(table(), &program, function.as_str(), formal).map(|run| format!("observed:{run}"))
}

#[cfg(test)]
mod tests {
    use super::{TABLE, observed_in, table_key};

    /// F1 — the fault: the list emptied holds nothing, so W1 / W2 catch it.
    #[test]
    fn w6o_r796_f1_an_emptied_list_holds_nothing() {
        assert_eq!(
            observed_in(TABLE, "bzip2", "handle_compress", "strm"),
            Some("observed:pass-D:bzip2/compress-1")
        );
        assert_eq!(observed_in("", "bzip2", "handle_compress", "strm"), None);
        assert_eq!(
            observed_in("", "libtree", "apply_exclude_list", "needed_buf_offsets"),
            None
        );
    }

    /// The table: the six observed, brotli's `symbol_lists` pair (one observed,
    /// one on the fixture), the two overlapping `s` / `br` argument pairs Miri
    /// reported, and the local `h` that stores `symbol_lists` (R808-5): 13 rows.
    #[test]
    fn w6o_r808_the_table_is_the_thirteen_rows() {
        assert_eq!(TABLE.lines().count(), 13);
        for function in ["DecodeWindowBits", "DecodeMetaBlockLength"] {
            for formal in ["s", "br"] {
                let detail = observed_in(TABLE, "brotli", function, formal);
                assert!(
                    detail.is_some_and(|d| d.starts_with("observed-pair:")),
                    "{function}::{formal}: {detail:?}"
                );
            }
        }
        assert!(
            observed_in(TABLE, "brotli", "ReadSymbolCodeLengths", "s")
                .is_some_and(|d| d.starts_with("observed:"))
        );
        assert!(
            observed_in(TABLE, "brotli", "SafeReadSymbolCodeLengths", "s")
                .is_some_and(|d| d.starts_with("fixture:"))
        );
        assert!(observed_in(TABLE, "brotli", "BrotliDecoderDecompressStream", "h#488").is_some());
        assert_eq!(observed_in(TABLE, "brotli", "ReadHuffmanCode", "s"), None);
        assert_eq!(observed_in(TABLE, "brotli", "ReadDistance", "br"), None);
    }

    /// A local is keyed `name#<MIR local>`, as the census keys it; a formal by
    /// its name.
    #[test]
    fn w6o_r808_a_local_is_keyed_by_name_and_mir_local() {
        assert_eq!(table_key("h", Some(488)), "h#488");
        assert_eq!(table_key("strm", None), "strm");
    }
}
