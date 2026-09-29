//! **wave-6l relay 063 (R645-5 item 2): the KX refusal list.**
//!
//! The reader chain's companion licence (`slice_input::prove`, R425-3) named,
//! for these 46 parameters, an integer that is not the parameter's extent: a
//! flag (`is_last`), a log2 size (`table_bits`), another quantity (`gap`, an
//! alphabet size, a pixel count), or a count the reads run past (`PrepareH35`'s
//! eight-byte hashes reach `input_size + 6`). Each row carries the one line of
//! evidence the extent record's classification read in the input
//! (`agents/artifacts/2026-09-28-wave-6l-r641-extent-record/the-112-classified.tsv`).
//!
//! **A list, not a rule.** The seam refuses the listed licences and takes the
//! root's array type or the fallback extent, receipted
//! `fallback(extent-refused:kx-list:<subject>)`. The extent analysis
//! (`agents/plan/2026-09-28-extent-analysis-design.md`) replaces the reader
//! chain, and with it this list.

use rustc_middle::ty::TyCtxt;

use super::Subject;

/// `(program, function path, parameter, evidence)`.
pub(crate) const KX_LIST: &[(&str, &str, &str, &str)] = &[
    (
        "brotli",
        "src::dec::decode::ReadHuffmanCode",
        "table",
        r#"L114078: ReadHuffmanCode(26, 26, &block_len_trees[..]) - companion alphabet_size_limit is the alphabet size; L114960 BrotliBuildSimpleHuffmanTable replicates the table to goal_size 1<<8=256 root entries (2nd-level tables beyond)"#,
    ),
    (
        "brotli",
        "src::enc::backward_references_hq::EvaluateNode",
        "starting_dist_cache",
        r#"companion is gap (UpdateNodes passes gap=0, L122006-7); L121946 ComputeDistanceCache reads *starting_dist_cache++ while idx<4 - true extent is the 4-entry distance cache"#,
    ),
    (
        "brotli",
        "src::enc::backward_references_hq::UpdateNodes",
        "starting_dist_cache",
        r#"companion is num_matches (the count of matches); handed to EvaluateNode L122007 -> up to 4 reads at L121946 - as EvaluateNode"#,
    ),
    (
        "brotli",
        "src::enc::backward_references_hq::ZopfliIterate",
        "dist_cache",
        r#"companion is gap (dictionary gap); dist_cache handed to UpdateNodes/EvaluateNode (L122287/L122317) -> up to 4 reads at L121946 - as EvaluateNode"#,
    ),
    (
        "brotli",
        "src::enc::brotli_bit_stream::BuildAndStoreHuffmanTree",
        "tree",
        r#"companion alphabet_size is a symbol count; L487645-487656 CreateHuffmanTree writes tree[j_end+1] with j_end = 2n-k -> tree needs 2*histogram_length+1 slots (MAX_HUFFMAN_TREE_SIZE scratch)"#,
    ),
    (
        "brotli",
        "src::enc::brotli_bit_stream::EncodeContextMap",
        "tree",
        r#"companion num_clusters; L131700 tree handed to BuildAndStoreHuffmanTree with length num_clusters+max_run_length_prefix -> needs 2n+1 (as BuildAndStoreHuffmanTree::tree)"#,
    ),
    (
        "brotli",
        "src::enc::brotli_bit_stream::BuildAndStoreBlockSplitCode",
        "tree",
        r#"companion num_types; L131790/L131799 tree handed to BuildAndStoreHuffmanTree with lengths num_types+2 and 26 -> needs 2*max+1 (as BuildAndStoreHuffmanTree::tree)"#,
    ),
    (
        "brotli",
        "src::enc::brotli_bit_stream::StoreTrivialContextMap",
        "tree",
        r#"companion context_bits is a bit count; L131846 tree handed to BuildAndStoreHuffmanTree with alphabet_size = num_types+repeat_code (L131824) - as BuildAndStoreHuffmanTree::tree"#,
    ),
    (
        "brotli",
        "src::enc::brotli_bit_stream::BuildAndStoreEntropyCodesCommand",
        "tree",
        r#"companion alphabet_size; L131983 BuildAndStoreHuffmanTree(histo, histogram_length_, alphabet_size, tree) -> needs 2*histogram_length_+1 (as BuildAndStoreHuffmanTree::tree)"#,
    ),
    (
        "brotli",
        "src::enc::brotli_bit_stream::BuildAndStoreEntropyCodesLiteral",
        "tree",
        r#"L132017: as BuildAndStoreEntropyCodesCommand"#,
    ),
    (
        "brotli",
        "src::enc::brotli_bit_stream::BuildAndStoreEntropyCodesDistance",
        "tree",
        r#"L132051: as BuildAndStoreEntropyCodesCommand"#,
    ),
    (
        "brotli",
        "src::enc::compress_fragment::BuildAndStoreLiteralPrefixCode",
        "depths",
        r#"companion input_size is the input byte count; depths is the 256-symbol depth table (L134395 BrotliBuildAndStoreHuffmanTreeFast(.., 8, depths); L134405 depths[i] over symbols)"#,
    ),
    (
        "brotli",
        "src::enc::compress_fragment::BrotliCompressFragmentFastImpl13",
        "table",
        r#"companion is is_last (a flag); table is the 1<<table_bits hash table (L135424 passes table_bits 13; hash >> shift from L135099)"#,
    ),
    (
        "brotli",
        "src::enc::compress_fragment::BrotliCompressFragmentFastImpl11",
        "table",
        r#"as BrotliCompressFragmentFastImpl13 (table_bits 11)"#,
    ),
    (
        "brotli",
        "src::enc::compress_fragment::BrotliCompressFragmentFastImpl9",
        "table",
        r#"as BrotliCompressFragmentFastImpl13 (table_bits 9)"#,
    ),
    (
        "brotli",
        "src::enc::compress_fragment::BrotliCompressFragmentFastImpl15",
        "table",
        r#"as BrotliCompressFragmentFastImpl13 (table_bits 15)"#,
    ),
    (
        "brotli",
        "src::enc::compress_fragment_two_pass::BrotliCompressFragmentTwoPassImpl",
        "command_buf",
        r#"companion is is_last (param 3, a flag); command_buf is the per-block command buffer (L136679 let commands = command_buf) - alias tracking would not help"#,
    ),
    (
        "brotli",
        "src::enc::compress_fragment_two_pass::BrotliCompressFragmentTwoPassImpl",
        "table",
        r#"companion is table_bits (log2 of the size); CreateCommands hash = h >> (64-table_bits) (L136108), table[hash] L136142 -> extent 1<<table_bits"#,
    ),
    (
        "brotli",
        "src::enc::compress_fragment_two_pass::BrotliCompressFragmentTwoPassImpl10",
        "command_buf",
        r#"as BrotliCompressFragmentTwoPassImpl::command_buf (companion is_last)"#,
    ),
    (
        "brotli",
        "src::enc::compress_fragment_two_pass::BrotliCompressFragmentTwoPassImpl16",
        "command_buf",
        r#"as BrotliCompressFragmentTwoPassImpl::command_buf (companion is_last)"#,
    ),
    (
        "brotli",
        "src::enc::compress_fragment_two_pass::BrotliCompressFragmentTwoPassImpl15",
        "command_buf",
        r#"as BrotliCompressFragmentTwoPassImpl::command_buf (companion is_last)"#,
    ),
    (
        "brotli",
        "src::enc::compress_fragment_two_pass::BrotliCompressFragmentTwoPassImpl14",
        "command_buf",
        r#"as BrotliCompressFragmentTwoPassImpl::command_buf (companion is_last)"#,
    ),
    (
        "brotli",
        "src::enc::compress_fragment_two_pass::BrotliCompressFragmentTwoPassImpl13",
        "command_buf",
        r#"as BrotliCompressFragmentTwoPassImpl::command_buf (companion is_last)"#,
    ),
    (
        "brotli",
        "src::enc::compress_fragment_two_pass::BrotliCompressFragmentTwoPassImpl12",
        "command_buf",
        r#"as BrotliCompressFragmentTwoPassImpl::command_buf (companion is_last)"#,
    ),
    (
        "brotli",
        "src::enc::compress_fragment_two_pass::BrotliCompressFragmentTwoPassImpl11",
        "command_buf",
        r#"as BrotliCompressFragmentTwoPassImpl::command_buf (companion is_last)"#,
    ),
    (
        "brotli",
        "src::enc::compress_fragment_two_pass::BrotliCompressFragmentTwoPassImpl17",
        "command_buf",
        r#"as BrotliCompressFragmentTwoPassImpl::command_buf (companion is_last)"#,
    ),
    (
        "brotli",
        "src::enc::compress_fragment_two_pass::BrotliCompressFragmentTwoPassImpl9",
        "command_buf",
        r#"as BrotliCompressFragmentTwoPassImpl::command_buf (companion is_last)"#,
    ),
    (
        "brotli",
        "src::enc::compress_fragment_two_pass::BrotliCompressFragmentTwoPassImpl8",
        "command_buf",
        r#"as BrotliCompressFragmentTwoPassImpl::command_buf (companion is_last)"#,
    ),
    (
        "brotli",
        "src::enc::encode::PrepareH35",
        "data",
        r#"L174389 (PrepareH3): HashBytesH3(&data[i]) for every i < input_size; HashBytesH3 is BrotliUnalignedRead64 (L175184) -> reads up to data[input_size+6] (ring-buffer slack)"#,
    ),
    (
        "brotli",
        "src::enc::encode::PrepareH55",
        "data",
        r#"L174485 (PrepareH54): HashBytesH54(&data[i]) 8-byte read for i < input_size - as PrepareH35"#,
    ),
    (
        "brotli",
        "src::enc::encode::PrepareH65",
        "data",
        r#"L174605 (PrepareH6): HashBytesH6(&data[i]) 8-byte read for i < input_size - as PrepareH35"#,
    ),
    (
        "brotli",
        "src::enc::metablock::BrotliBuildMetaBlockGreedyInternal",
        "static_context_map",
        r#"companion num_contexts in {2,3,13} (L176738-176874) is the cluster count; map indexed by a 6-bit context (L491085) and MapStaticContexts reads j < 64 (L490964) -> extent 64"#,
    ),
    (
        "lodepng",
        "src::lodepng::HuffmanTree_makeFromFrequencies",
        "frequencies",
        r#"companion is mincodes (2/19/257, L3246-3252), not numcodes (30/19/286); L1985 reads frequencies[numcodes-1], L1998 hands numcodes to lodepng_huffman_code_lengths"#,
    ),
    (
        "lodepng",
        "src::lodepng::lodepng_zlib_decompressv",
        "settings",
        r#"settings is one *const LodePNGDecompressSettings struct; companion insize is in_0's byte count"#,
    ),
    (
        "lodepng",
        "src::lodepng::zlib_decompress",
        "settings",
        r#"single-struct pointer ((*settings).custom_zlib deref); companion insize belongs to in_0 - as lodepng_zlib_decompressv::settings"#,
    ),
    (
        "lodepng",
        "src::lodepng::zlib_compress",
        "settings",
        r#"single-struct pointer; companion insize belongs to in_0 - as lodepng_zlib_decompressv::settings"#,
    ),
    (
        "lodepng",
        "src::lodepng::lodepng_chunk_createv",
        "type_0",
        r#"companion length is the chunk-data length; L4347 memcpy(chunk+4, type_0, 4) reads a 4-byte type; IEND passes length 0 (L9590-9591), sRGB passes 1"#,
    ),
    (
        "lodepng",
        "src::lodepng::getPixelColorRGBA8",
        "in_0",
        r#"companion i is the pixel index (the read position): reads in[i], in[i*2+1], in[i*4+3] (L5671-5677) - all at or past i"#,
    ),
    (
        "lodepng",
        "src::lodepng::getPixelColorsRGBA8",
        "in_0",
        r#"companion numpixels counts pixels but reads are byte-scaled: in[i*2+1] for 16-bit (L5762), up to in[i*8+7] - byte extent is numpixels*bpp/8"#,
    ),
    (
        "lodepng",
        "src::lodepng::getPixelColorsRGB8",
        "in_0",
        r#"as getPixelColorsRGBA8 (L6057 in[i*6+k])"#,
    ),
    (
        "lodepng",
        "src::lodepng::addChunk_IDAT",
        "zlibsettings",
        r#"single-struct pointer handed to zlib_compress; companion datasize belongs to data - as zlib_compress::settings"#,
    ),
    (
        "lodepng",
        "src::lodepng::preProcessScanlines",
        "in_0",
        r#"companion w is the image width in pixels; image bytes = h*ceil(w*bpp/8) (L10649 outsize; L10681 filter(*out, in_0, w, h, ..))"#,
    ),
    (
        "binn",
        "src::binn::binn_list_add_raw",
        "pvalue",
        r#"L983-990 (AddValue): fixed-width storage overwrites size with 1/2/4/8 (int setters pass 0), L994 size==0 means strlen2(pvalue) for strings, L979 compress_int may swap pvalue - companion is a type-dependent hint"#,
    ),
    (
        "binn",
        "src::binn::binn_object_set_raw",
        "key",
        r#"companion is type_0 (a binn type tag); key is a NUL-terminated string: L744 strlen(key) then memcpy(p, key, int32)"#,
    ),
    (
        "binn",
        "src::binn::binn_object_set_raw",
        "pvalue",
        r#"as binn_list_add_raw::pvalue (AddValue L983-994)"#,
    ),
    (
        "binn",
        "src::binn::binn_map_set_raw",
        "pvalue",
        r#"as binn_list_add_raw::pvalue (AddValue L983-994)"#,
    ),
];

/// The row's key, `<function path>::<parameter>`, when `subject` is listed.
pub(crate) fn listed(tcx: TyCtxt<'_>, subject: &Subject) -> Option<String> {
    let param = subject.param_name.as_deref()?;
    let function = tcx.def_path_str(subject.fn_did.to_def_id());
    KX_LIST
        .iter()
        .any(|(_, path, name, _)| *path == function && *name == param)
        .then(|| format!("{function}::{param}"))
}
