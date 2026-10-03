//! **R766-2 / relay 253 — `next_out#6`'s depth-1 raw view, decided per site (main 150).**
//! brotli's class 2452 is held by `BrotliEncoderCompressStream::next_out#6`
//! (`flows-into-raw-param`): the delivered `next_out: &mut *mut u8` reaches three
//! callee formals the model keeps raw (`*mut *mut u8`), and every one of those raw
//! boundary sites is refused `depth2-storage-shape-held` — the depth-2 arm reads the
//! argument as the `&mut p` out-param of an INNER pointer, which a bare outer
//! subject is not. Its bridge is the ordinary depth-1 raw view (a coercion of
//! `&mut *mut u8` to `*mut *mut u8` at the call): the subject's own type is the formal's.
use super::{
    verify,
    wave6a_allocation_tests::{compact, emitted},
};

/// The degradation reason of `owner::name`, whichever key form it carries (a
/// class-held member is keyed `name#N`, a node-blocked one `name`).
fn reason_of(degradations: &[super::decision::Degradation], subject: &str) -> Option<String> {
    degradations
        .iter()
        .find(|d| {
            d.subject == subject
                || d.subject
                    .strip_prefix(subject)
                    .is_some_and(|rest| rest.starts_with('#'))
        })
        .map(|d| d.reason.key().to_owned())
}

/// The reduction: `inject` casts its OUTER formal to another pointee type, so the
/// model keeps it raw; `stream`'s `next_out` is a thin `&mut *mut u8` whose inner
/// pointer stays raw (it is stepped too).
const NEXT_OUT: &str = r#"#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]
unsafe fn inject(mut next_out: *mut *mut u8, mut n: usize) -> i32 {
    let mut q = next_out as *mut *mut i8;
    *q = (*q).offset(n as isize);
    1
}
pub unsafe fn stream(mut next_out: *mut *mut u8, mut n: usize) -> i32 {
    *next_out = (*next_out).offset(1 as isize);
    inject(next_out, n)
}
"#;

#[test]
fn r763_a_bare_outer_subject_takes_the_depth_one_view_at_a_depth_two_formal() {
    let out = emitted("r763_next_out", NEXT_OUT);
    let flat = compact(&out.source);
    assert_eq!(
        reason_of(&out.degradations, "stream::next_out"),
        None,
        "the outer subject is not held: {:#?}\n{}",
        out.degradations,
        out.source
    );
    assert!(
        flat.contains("mutnext_out:&mut*mutu8") && flat.contains("inject(next_out,n)"),
        "the subject delivers; the thin reference coerces to the raw formal at the call: {}",
        out.source
    );
    assert_eq!(out.reverted, 0, "{}", out.source);
}

/// The control: a RE-SEATED outer subject (`next_out = …` in its owner) keeps the
/// depth-2 storage hold — its re-seating is not a depth-1 view's to present.
#[test]
fn r763_a_control_a_re_seated_outer_subject_keeps_the_storage_hold() {
    let input = NEXT_OUT.replace(
        "    inject(next_out, n)\n",
        "    let r = inject(next_out, n);\n    next_out = 0 as *mut *mut u8;\n    r\n",
    );
    assert!(verify::type_checks_str(&input));
    let out = emitted("r763_next_out_reseated", &input);
    let flat = compact(&out.source);
    assert!(
        flat.contains("mutnext_out:*mut*mutu8"),
        "the re-seated subject stays raw: {}",
        out.source
    );
    assert_eq!(out.reverted, 0, "{}", out.source);
}

/// 093 §2's reduction (wave-6o's `STREAM`) with brotli's second member: `Stream`
/// also hands its bare outer `next_out` to `Inject`'s raw depth-2 formal. With the
/// depth-1 view, `next_out` no longer holds the class, so `total_out` keeps the
/// Option stage's form (the null literal renders `None`, no `arg-null-literal`).
const STREAM_NEXT_OUT: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case)]
#[repr(C)] pub struct S { pub total: usize }
unsafe fn Inject(mut s: *mut S, mut next_out: *mut *mut u8, mut total_out: *mut usize) -> i32 {
    let mut q = next_out as *mut *mut i8;
    *q = (*q).offset(1 as isize);
    if !total_out.is_null() { total_out.write((*s).total); }
    return 1 as i32;
}
unsafe fn Stream(mut s: *mut S, mut next_out: *mut *mut u8, mut total_out: *mut usize) -> i32 {
    *next_out = (*next_out).offset(1 as isize);
    return Inject(s, next_out, total_out);
}
unsafe fn CompressFile(mut s: *mut S, mut buf: *mut u8) -> i32 {
    let mut out: usize = 0;
    let mut next_out: *mut u8 = buf;
    Stream(s, &mut next_out, 0 as *mut usize) + Stream(s, &mut next_out, &mut out)
}
"#;

#[test]
fn r763_c_the_null_literal_member_keeps_its_option_once_next_out_takes_the_depth_one_view() {
    assert!(verify::type_checks_str(STREAM_NEXT_OUT));
    let out = emitted("r763_stream_next_out", STREAM_NEXT_OUT);
    assert_eq!(
        reason_of(&out.degradations, "Stream::next_out"),
        None,
        "{:#?}\n{}",
        out.degradations,
        out.source
    );
    assert_eq!(
        reason_of(&out.degradations, "Stream::total_out"),
        None,
        "{:#?}\n{}",
        out.degradations,
        out.source
    );
    assert_eq!(out.reverted, 0, "{}", out.source);
    let output = &out.source;
    let flat = compact(output);
    assert!(flat.contains("mutnext_out:&mut*mutu8"), "{output}");
    assert!(flat.contains("total_out:Option<&mutusize>"), "{output}");
    assert!(flat.contains("Stream(s,&mutnext_out,None)"), "{output}");
    assert!(verify::type_checks_str(output), "{output}");
}
