//! era-5c relay 213 (R988-1, USER): the mutable copy-lend at emission. wave-6a's S3 with a write
//! through the copy (`*p = 8;` then a read, before `free(buf)`) — the `write-through` variant its
//! controls pin as not delivered under the shared lend — is delivered with
//! `CRAT_ERA5C_COPY_LEND_MUT=on`: `buf` a Box, `p` a mutable reborrow of it, declared `&mut i32`.

use super::wave6a_allocation_tests::compact;

/// `copy_read` emitted in a child (wave-6a's `w6a_r805_inner_emit`) with the copy-lend arm on and
/// the mutable copy-lend as given: the function and its revert count.
fn emitted(name: &str, mutable: &str) -> (String, usize, String) {
    let exe = std::env::current_exe().expect("current_exe");
    let output = std::process::Command::new(exe)
        .args([
            "bo_rewriter::wave6a_copy_lend_tests::w6a_r805_inner_emit",
            "--exact",
            "--ignored",
            "--nocapture",
            "--test-threads=1",
        ])
        .env("CRAT_ERA5C_COPY_LEND_MUT", mutable)
        .env("R805_VARIANT", name)
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
    (function, reverted, text)
}

/// (i) at emission: the owner covers the four elements (`Box<[i32]>`), `p` is
/// `&mut (*(buf))[0]`, the write stays a write through it, the C `free` is the drop, and no raw
/// pointer is left.
#[test]
fn e5c_cm_emit_a_written_copy_is_a_mutable_reborrow() {
    let (function, reverted, text) = emitted("write-through", "on");
    let compact = compact(&function);
    let context = format!("{text}\n{function}");
    assert!(
        compact.contains("letmutbuf:::std::boxed::Box<[i32]>="),
        "{context}"
    );
    assert!(
        compact.contains("letmutp:&muti32=&mut(*(buf))[0];"),
        "{context}"
    );
    assert!(compact.contains("*p=8"), "{context}");
    assert!(compact.contains("::std::mem::drop(buf);"), "{context}");
    assert!(!compact.contains("*mut"), "{context}");
    assert_eq!(reverted, 0, "{context}");
}

/// (i) at emission, a sized owner: `Box<i32>` and `&mut *(buf)`.
#[test]
fn e5c_cm_emit_a_sized_owner_lends_mutably_by_reborrow() {
    let (function, reverted, text) = emitted("sized+write-through", "on");
    let compact = compact(&function);
    let context = format!("{text}\n{function}");
    assert!(
        compact.contains("letmutbuf:::std::boxed::Box<i32>="),
        "{context}"
    );
    assert!(compact.contains("letmutp:&muti32=&mut*(buf);"), "{context}");
    assert!(!compact.contains("*mut"), "{context}");
    assert_eq!(reverted, 0, "{context}");
}

/// (iv)/(v) at emission: the read-only S3 is the shared lend with the switch on, and the written
/// copy is not delivered with it off (wave-6a's control).
#[test]
fn e5c_cm_emit_controls() {
    let (function, _, text) = emitted("declaration", "on");
    assert!(
        compact(&function).contains("letmutp:&i32=&(*(buf))[0];"),
        "{text}\n{function}"
    );
    let (function, _, text) = emitted("write-through", "off");
    let compact = compact(&function);
    assert!(
        !compact.contains("::std::boxed::Box") && !compact.contains(":&muti32="),
        "{text}\n{function}"
    );
}
