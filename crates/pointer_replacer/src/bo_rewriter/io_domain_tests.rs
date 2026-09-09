//! R261-3 — the type-derived io-domain set, and the ratchet that it is a
//! superset of the sealed identity set.
//!
//! The superset property is not free: reading the sealed 109 identities against
//! the corpus source shows their named subjects carry `*mut FILE` (21) but also
//! `*mut Context` (5, brotli), `*mut BitStream` (3) and `*mut bzFile` (3).
//! Those three are program-defined wrappers, io-domain only because each holds
//! a `*mut FILE` field, so a rule keyed on the stream type names alone would
//! miss eleven of the thirty-two resolvable named identities. The ratchet below
//! pins the transitive step that covers them.

/// The wrapper shapes observed in the sealed set, reproduced as fixtures. Each
/// is a struct holding a stream handle exactly as `bzFile`, `BitStream` and
/// brotli's `Context` do.
const WRAPPER_SHAPES: &str = r#"
    #![allow(dead_code, unused_unsafe)]
    pub struct FILE {
        pub flags: i32,
    }
    /// `bzFile` / `BitStream`: the handle is the first field.
    pub struct BitStream {
        pub handle: *mut FILE,
        pub buffer: i32,
    }
    /// brotli's `Context`: the handles sit late, after many scalars, and there
    /// are two of them.
    pub struct Context {
        pub quality: i32,
        pub lgwin: i32,
        pub input_file_length: i64,
        pub fin: *mut FILE,
        pub fout: *mut FILE,
    }
    /// A wrapper of a wrapper -- depth 2, still io-domain.
    pub struct Outer {
        pub inner: *mut BitStream,
    }
    /// The negative control: same shape, no stream anywhere.
    pub struct Plain {
        pub quality: i32,
        pub buffer: *mut u8,
    }
    pub unsafe fn direct(f: *mut FILE) -> i32 {
        (*f).flags
    }
    pub unsafe fn wrapped(b: *mut BitStream) -> i32 {
        (*b).buffer
    }
    pub unsafe fn context(c: *mut Context) -> i32 {
        (*c).quality
    }
    pub unsafe fn nested(o: *mut Outer) -> i32 {
        (*(*o).inner).buffer
    }
    pub unsafe fn plain(p: *mut Plain) -> i32 {
        (*p).quality
    }
"#;

fn reasons(src: &str) -> std::collections::BTreeMap<String, String> {
    super::emit_tests::decisions_of(src)
        .into_iter()
        .map(|(name, _, reason)| (name, reason))
        .collect()
}

/// The ratchet. Every wrapper shape the sealed set actually contains is held by
/// TYPE, so the type-derived set covers them without naming a single identity.
#[test]
fn io_domain_type_rule_covers_the_sealed_wrapper_shapes() {
    let got = reasons(WRAPPER_SHAPES);
    for subject in ["f", "b", "c", "o"] {
        assert_eq!(
            got.get(subject).map(String::as_str),
            Some("held:io-domain:type"),
            "{subject} reaches a stream handle by type: {got:#?}"
        );
    }
}

/// It is a rule about streams, not about pointers: an identically shaped struct
/// with no handle in it is untouched, so the hold cannot quietly become a
/// blanket refusal of struct pointers.
#[test]
fn io_domain_type_rule_leaves_stream_free_shapes_alone() {
    let got = reasons(WRAPPER_SHAPES);
    assert_ne!(
        got.get("p").map(String::as_str),
        Some("held:io-domain:type"),
        "a stream-free struct pointer is not io-domain: {got:#?}"
    );
}

/// The type names the rule is anchored on, pinned so a rename cannot silently
/// empty the set.
#[test]
fn io_domain_type_names_are_pinned() {
    use super::decision::io_domain::IO_DOMAIN_TYPE_NAMES;
    for required in ["FILE", "_IO_FILE"] {
        assert!(
            IO_DOMAIN_TYPE_NAMES.contains(&required),
            "{required} anchors the corpus's stream handles"
        );
    }
}
