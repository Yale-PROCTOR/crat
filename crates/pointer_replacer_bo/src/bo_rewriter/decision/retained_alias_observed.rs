//! **Wave-6o relays 146 / 153 / 155 (R796-1, R805-2, R808-5): the STOP-GAP
//! for batch 55. It is not the rule.**
//!
//! The table holds the formals (and the one local) that Miri has shown
//! undefined on the record's tree, of two classes of ours:
//! - **retained aliases:** a reference whose pointee the program also reaches
//!   through a pointer it keeps in memory (bzip2's state keeps `s->strm`;
//!   libtree's small vector keeps `v->p` into its own buffer; brotli's decoder
//!   keeps `h->symbol_lists` into its own header);
//! - **overlapping argument pairs:** two pointer formals of one call where one
//!   lies inside the other's object and the call writes through one while the
//!   other is a protected reference — both formals references (brotli's `s` and
//!   `br = &(*s).br`), or the state a raw view and the field a reference
//!   (`ReadHuffmanCode::table`, inside the state), or the state a reference and
//!   the field a raw view (the `…Internal` callees' `s`: wave-6o's fixture (b),
//!   relay 155, is undefined too).
//!
//! Each row carries its receipt detail: `observed:<run>` (a retained alias a
//! run showed), `observed-pair:<run>` (a pair a run showed), or `fixture:<name>`
//! (a Miri fixture of the record's own emitted signature, where the corpus run
//! had not yet reached the call). A formal is keyed by its name, a local by
//! `name#<MIR local>` as the census keys it. Receipt `held:retained-alias`;
//! rows are `side-condition` in the audit.
//!
//! **What this is NOT:** the rule (relay 140's R787-1, era-5c's relation, and
//! wave-5d's pair rule replace it). A subject of the same class that no run has
//! reached is not held here.
use rustc_middle::ty::TyCtxt;

use super::{Subject, SubjectKind};

/// `program  function  formal|local#N  detail`
const TABLE: &str = "\
bzip2\thandle_compress\tstrm\tobserved:pass-D:bzip2/compress-1
bzip2\tBZ2_bzCompress\tstrm\tobserved:pass-D:bzip2/compress-1
bzip2\tBZ2_bzDecompress\tstrm\tobserved:pass-D:bzip2/decompress-1
libtree\tsmall_vec_u64_init\tv\tobserved:pass-D:libtree/bin-ls
libtree\tsmall_vec_u64_append\tv\tobserved:pass-D:libtree/bin-ls
libtree\tapply_exclude_list\tneeded_buf_offsets\tobserved:hold-validation-H2:libtree/bin-ls
brotli\tReadSymbolCodeLengths\ts\tobserved:pass-C-enum:brotli/encode.c-q6-decompress
brotli\tSafeReadSymbolCodeLengths\ts\tfixture:era5c-132-miri-symlists
brotli\tDecodeWindowBits\ts\tobserved-pair:pass-C-enum:brotli/encode.c-q6-decompress
brotli\tDecodeWindowBits\tbr\tobserved-pair:pass-C-enum:brotli/encode.c-q6-decompress
brotli\tDecodeMetaBlockLength\ts\tobserved-pair:pass-C-enum:brotli/encode.c-q6-decompress
brotli\tDecodeMetaBlockLength\tbr\tobserved-pair:pass-C-enum:brotli/encode.c-q6-decompress
brotli\tBrotliDecoderDecompressStream\th#488\tobserved:pass-C-enum:brotli/encode.c-q6-decompress
brotli\tReadHuffmanCode\ttable\tobserved-pair:pass-C-enum:brotli/encode.c-q6-decompress
brotli\tReadCommand\ts\tobserved-pair:pass-C-enum:brotli/encode.c-q6-decompress
brotli\tReadCommand\tbr\tobserved-pair:pass-C-enum:brotli/encode.c-q6-decompress
brotli\tReadCommandInternal\ts\tobserved-pair:pass-C-enum:brotli/encode.c-q6-decompress
brotli\tReadDistance\ts\tobserved-pair:pass-C-enum:brotli/encode.c-q6-decompress
brotli\tReadDistance\tbr\tobserved-pair:pass-C-enum:brotli/encode.c-q6-decompress
brotli\tReadDistanceInternal\ts\tobserved-pair:pass-C-enum:brotli/encode.c-q6-decompress
";

#[cfg(test)]
const FIXTURE_TABLE: &str = "\
-\tobs_handle_compress\tstrm\tobserved:fixture-w1
-\tobs_BZ2_bzCompress\tstrm\tobserved:fixture-w1
-\tobs_small_vec_u64_init\tv\tobserved:fixture-w2
-\tobs_small_vec_u64_append\tv\tobserved:fixture-w2
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
    match local {
        Some(local) => format!("{name}#{local}"),
        None => name.to_owned(),
    }
}

/// The receipt detail (the row's own: `observed:<run>`, `observed-pair:<run>` or
/// `fixture:<name>`) for a listed subject.
pub(crate) fn held(tcx: TyCtxt<'_>, subject: &Subject) -> Option<String> {
    let program = std::env::var("CRAT_ERA5_PROGRAM").unwrap_or_else(|_| "-".to_owned());
    let function = tcx.item_name(subject.fn_did.to_def_id());
    let name = subject.param_name.as_deref()?;
    let key = match subject.kind {
        SubjectKind::Param { .. } => table_key(name, None),
        SubjectKind::Local => table_key(name, Some(subject.local.as_u32())),
    };
    observed_in(table(), &program, function.as_str(), &key).map(str::to_owned)
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
    /// one on the fixture), the local `h` that stores `symbol_lists`, and every
    /// overlapping pair the decoder run reported until it was clean (R810):
    /// 20 rows.
    #[test]
    fn w6o_r810_the_table_is_the_twenty_rows() {
        assert_eq!(TABLE.lines().count(), 20);
        for (function, formal) in [
            ("DecodeWindowBits", "s"),
            ("DecodeWindowBits", "br"),
            ("DecodeMetaBlockLength", "s"),
            ("DecodeMetaBlockLength", "br"),
            ("ReadCommand", "s"),
            ("ReadCommand", "br"),
            ("ReadDistance", "s"),
            ("ReadDistance", "br"),
            ("ReadCommandInternal", "s"),
            ("ReadDistanceInternal", "s"),
            ("ReadHuffmanCode", "table"),
        ] {
            let detail = observed_in(TABLE, "brotli", function, formal);
            assert!(
                detail.is_some_and(|d| d.starts_with("observed-pair:")),
                "{function}::{formal}: {detail:?}"
            );
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
        assert_eq!(observed_in(TABLE, "brotli", "SafeReadDistance", "br"), None);
        assert_eq!(
            observed_in(TABLE, "brotli", "ReadCommandInternal", "br"),
            None
        );
    }

    /// A local is keyed `name#<MIR local>`, as the census keys it; a formal by
    /// its name.
    #[test]
    fn w6o_r808_a_local_is_keyed_by_name_and_mir_local() {
        assert_eq!(table_key("h", Some(488)), "h#488");
        assert_eq!(table_key("strm", None), "strm");
    }
}
