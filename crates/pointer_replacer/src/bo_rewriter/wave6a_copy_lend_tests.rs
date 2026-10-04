//! wave-6a relay 147 (R805-3): a reference lent by a LOCAL owner. With the
//! copy-lend arm on (`CRAT_ERA5C_COPY_LEND=on`), the model decides S3's
//! `let mut p = buf;` — `buf` an allocation the function frees, `p` only
//! read — as `buf` Owning and `p` Ref.

use super::wave6a_allocation_tests::{compact, emitted};

const S3: &str = include_str!("testdata/w6a-r805-s3-copy-read.rs");

/// S3, or one of its variants, by name.
fn variant(name: &str) -> String {
    let edit = |from: &str, to: &str| {
        let edited = S3.replacen(from, to, 1);
        assert_ne!(edited, S3, "{name}");
        edited
    };
    match name {
        "declaration" => S3.to_owned(),
        // `p = buf;` after a declaration.
        "assignment" => edit(
            "    let mut p = buf;\n",
            "    let mut p = 0 as *mut ::core::ffi::c_int;\n    p = buf;\n",
        ),
        // `buf` tested against null before the copy.
        "optional" => edit(
            "    *buf = 7 as ::core::ffi::c_int;\n",
            "    if buf.is_null() {\n        return -(1 as ::core::ffi::c_int);\n    }\n    *buf = 7 as ::core::ffi::c_int;\n",
        ),
        // `p` still read after `buf` is released.
        "after-release" => edit(
            "    free(buf as *mut ::core::ffi::c_void);\n    return v;",
            "    free(buf as *mut ::core::ffi::c_void);\n    return v + *p;",
        ),
        // One element: a sized owner.
        "sized" => edit(
            "        (4 as size_t)\n            .wrapping_mul(::core::mem::size_of::<::core::ffi::c_int>() as size_t),\n",
            "        ::core::mem::size_of::<::core::ffi::c_int>() as size_t,\n",
        ),
        // `p` handed on to a local reader: a use that is not a read through it.
        "argument" => edit(
            "    let mut v = *p;\n",
            "    let mut v = peek(p);\n",
        )
        .replacen(
            "unsafe fn main_0()",
            "unsafe extern \"C\" fn peek(mut q: *mut ::core::ffi::c_int) -> ::core::ffi::c_int {\n    return *q;\n}\nunsafe fn main_0()",
            1,
        ),
        // Codex: a raw pointer derived from the copy, read after the owner's write.
        "raw-cast" => edit(
            "    let mut v = *p;\n",
            "    let mut q = p as *const ::core::ffi::c_int;\n    *buf = 9 as ::core::ffi::c_int;\n    let mut v = *q;\n",
        ),
        // Codex: an address comparison through the copy.
        "compare" => edit(
            "    let mut v = *p;\n",
            "    let mut v = *p + (p == buf) as ::core::ffi::c_int;\n",
        ),
        // A write through `p`: not a shared lend.
        "write-through" => edit(
            "    let mut v = *p;\n",
            "    *p = 8 as ::core::ffi::c_int;\n    let mut v = *p;\n",
        ),
        other => panic!("no variant {other}"),
    }
}

#[test]
#[ignore = "run by w6a_r805_* in a child with the copy-lend arm on"]
fn w6a_r805_inner_emit() {
    let name = std::env::var("R805_VARIANT").expect("R805_VARIANT");
    let source = format!("// r805-s3\n{}", variant(&name));
    // `R805_PIN=<p kind>`: the model pinned (`buf` Owning, `p` as named), to
    // reach the arm with a shape the model does not decide today.
    let _frame = super::test_model_override::frame_lock();
    if let Ok(kind) = std::env::var("R805_PIN") {
        use crate::analyses::borrow_ownership::SlotKind;
        let kind = match kind.as_str() {
            "ref" => SlotKind::Ref,
            "raw" => SlotKind::Raw,
            other => panic!("R805_PIN {other}"),
        };
        super::test_model_override::set(
            "r805-s3",
            vec![],
            vec![
                ("copy_read::buf".to_owned(), SlotKind::Owning),
                ("copy_read::p".to_owned(), kind),
            ],
        );
    }
    let out = emitted("r805-s3", &source);
    super::test_model_override::clear();
    let start = out.source.find("fn copy_read").expect("copy_read");
    let end = out.source[start..]
        .find("\n}\n")
        .map_or(out.source.len(), |e| start + e + 3);
    println!(
        "R805-FUNCTION-BEGIN\n{}\nR805-FUNCTION-END",
        &out.source[start..end]
    );
    println!("R805-REVERTED {}", out.reverted);
    for row in out
        .artifacts
        .ownership_native
        .lines()
        .filter(|l| l.contains("copy_read::buf#"))
    {
        println!("R805-NATIVE {row}");
    }
}

/// `copy_read` emitted with the copy-lend arm on (a child process: the
/// switch is read from the environment), and the owner's native row.
fn emitted_with_copy_lend(name: &str) -> (String, usize, String) {
    emitted_pinned(name, None)
}

fn emitted_pinned(name: &str, pin: Option<&str>) -> (String, usize, String) {
    let exe = std::env::current_exe().expect("current_exe");
    let output = std::process::Command::new(exe)
        .args([
            "bo_rewriter::wave6a_copy_lend_tests::w6a_r805_inner_emit",
            "--exact",
            "--ignored",
            "--nocapture",
            "--test-threads=1",
        ])
        .env("CRAT_ERA5C_COPY_LEND", "on")
        .env("R805_VARIANT", name)
        .envs(pin.map(|kind| ("R805_PIN", kind)))
        .output()
        .expect("child test");
    let text = String::from_utf8_lossy(&output.stdout).into_owned();
    assert!(
        output.status.success(),
        "{name}:\n{text}\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let function = text
        .split("R805-FUNCTION-BEGIN\n")
        .nth(1)
        .and_then(|rest| rest.split("\nR805-FUNCTION-END").next())
        .unwrap_or_default()
        .to_owned();
    let reverted = text
        .lines()
        .find_map(|l| l.strip_prefix("R805-REVERTED "))
        .and_then(|n| n.parse().ok())
        .unwrap_or(usize::MAX);
    let native = text
        .lines()
        .find_map(|l| l.strip_prefix("R805-NATIVE "))
        .unwrap_or_default()
        .to_owned();
    (function, reverted, native)
}

/// **The RED (R805-3), S3 as the fork translates it.** `buf` covers the
/// four elements C allocates (`Box<[i32]>`), `p` is a shared reference
/// reborrowed from it, the C `free` is the explicit drop, and no raw pointer
/// is left in the function.
#[test]
fn w6a_r805_s3_lends_its_owner_as_a_shared_reference() {
    let (function, reverted, native) = emitted_with_copy_lend("declaration");
    let text = compact(&function);
    let context = format!("{native}\n{function}");
    assert!(
        text.contains("letmutbuf:::std::boxed::Box<[i32]>="),
        "{context}"
    );
    assert!(text.contains("letmutp:&i32=&(*(buf))[0];"), "{context}");
    assert!(text.contains("letmutv=*p;"), "{context}");
    assert!(text.contains("::std::mem::drop(buf);"), "{context}");
    assert!(!text.contains("*mut"), "{context}");
    assert_eq!(reverted, 0, "{context}");
}

/// **R805-3, a sized owner:** one element allocated, `Box<i32>`, and the
/// lend is `&*(buf)`.
#[test]
fn w6a_r805_a_sized_owner_lends_by_reborrow() {
    let (function, reverted, native) = emitted_with_copy_lend("sized");
    let text = compact(&function);
    let context = format!("{native}\n{function}");
    assert!(
        text.contains("letmutbuf:::std::boxed::Box<i32>="),
        "{context}"
    );
    assert!(text.contains("letmutp:&i32=&*(buf);"), "{context}");
    assert!(text.contains("::std::mem::drop(buf);"), "{context}");
    assert!(!text.contains("*mut"), "{context}");
    assert_eq!(reverted, 0, "{context}");
}

/// **Controls (R805-3):** the shapes the model does not decide with the arm
/// on — the assignment form, an owner tested against null, a lend still read
/// after the release (the validation refuses it), a write through the copy,
/// the copy handed on to a local reader: none delivers the pair.
#[test]
fn w6a_r805_what_the_model_does_not_decide_is_not_delivered() {
    for name in [
        "assignment",
        "optional",
        "after-release",
        "write-through",
        "argument",
    ] {
        let (function, reverted, native) = emitted_with_copy_lend(name);
        let text = compact(&function);
        assert!(
            !text.contains("::std::boxed::Box") && !text.contains(":&i32="),
            "{name}: {native}\n{function}"
        );
        assert_eq!(reverted, 0, "{name}: {function}");
    }
}

/// **R805-3 (Codex): the alias is admitted only when every use is a read
/// through it.** With the model pinned (`buf` Owning, `p` Ref), a raw pointer
/// derived from the copy and read after the owner's write would compile once
/// `p` is a reference — and be UB: the owner is not delivered.
#[test]
fn w6a_r805_a_raw_pointer_derived_from_the_lend_holds_the_owner() {
    let (function, reverted, native) = emitted_pinned("raw-cast", Some("ref"));
    assert!(native.contains("\theld\t"), "{native}\n{function}");
    assert!(
        !compact(&function).contains("::std::boxed::Box"),
        "{function}"
    );
    assert_eq!(reverted, 0, "{function}");
}

/// **R805-3 (Codex): the alias is admitted only when the model decides it
/// Ref.** With the model pinned (`buf` Owning, `p` Raw), the copy is not a
/// lend the analysis validated: the owner is not delivered as a lender.
#[test]
fn w6a_r805_a_copy_the_model_keeps_raw_is_not_a_lend() {
    let (function, _, native) = emitted_pinned("declaration", Some("raw"));
    assert!(
        !compact(&function).contains(":&i32="),
        "{native}\n{function}"
    );
}
