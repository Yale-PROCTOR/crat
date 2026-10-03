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

/// The A5 site-proof fallback's raw view of one argument (`replan_a5_raw_view`),
/// as the census planned it at brotli's `ProcessMetadata(.., next_out, total_out)`
/// (batch 54: `a5-site-proof-t2-fallback`, `depth2-npo-bridge`, E0308 `*mut *mut *mut u8`).
fn a5_view(shape: &'static str, argument: &str) -> super::decision::seam::A5RawViewTemp {
    use rustc_hir::def_id::CRATE_DEF_ID;

    use super::decision::{
        a5_site_proof::A5ProofSiteKey,
        raw_boundary::{Depth2Target, RawMutability, RawTargetType},
        seam::{A5RawViewTemp, Form},
    };
    use crate::analyses::borrow_ownership::l2::MirLocationKey;
    let target = RawTargetType {
        rendered: "*mut *mut u8".to_owned(),
        pointee: "*mut u8".to_owned(),
        mutability: RawMutability::Mut,
        depth2: Some(Depth2Target {
            inner_pointee: "u8".to_owned(),
            inner_mutability: RawMutability::Mut,
            thin: true,
        }),
    };
    A5RawViewTemp {
        argument_index: 4,
        argument_expression: argument.to_owned(),
        argument_shape: shape,
        raw_expression: String::new(),
        target_type: target.rendered.clone(),
        target,
        adapted_expression: String::new(),
        extent_expression: None,
        template: String::new(),
        proof_site_key: A5ProofSiteKey {
            caller: CRATE_DEF_ID,
            location: MirLocationKey::new(12, 15),
            callee: CRATE_DEF_ID.to_def_id(),
            argument_index: 4,
            slot_depth: 0,
        },
        unsafe_context: None,
        negative_write: None,
        expected_form: Form::Raw,
        found_form: Form::Ref { mutable: true },
        source_node: None,
        enclosing_unsafe_fn: true,
        input_rendering: None,
    }
}

/// R766-2's corpus failure (main 159 §2a): a BARE outer subject (`next_out`,
/// delivered `&mut *mut u8`) at a depth-2 formal is the outer pointer itself, so its
/// A5 raw view is the depth-1 one. The NPO view of its binding
/// (`from_mut(&mut next_out).cast::<*mut *mut u8>()`, a `*mut *mut *mut u8`) is the
/// view of an INNER pointer's `&mut p` storage, which a bare local is not.
#[test]
fn r766_2_an_a5_raw_view_of_a_bare_outer_subject_is_the_depth_one_view() {
    use super::decision::seam::{Form, replan_a5_raw_view};
    let view = replan_a5_raw_view(
        &a5_view("bare-local", "next_out"),
        Form::Raw,
        Form::Ref { mutable: true },
    )
    .expect("the view renders");
    assert!(
        !view.raw_expression.contains("&mut next_out") && !view.template.contains("depth2-npo"),
        "{view:#?}"
    );
    assert_eq!(
        view.raw_expression, "core::ptr::from_mut(&mut *next_out)",
        "{view:#?}"
    );
}

/// The control: an `&mut p` argument (an INNER pointer subject's storage) keeps the
/// depth-2 NPO view.
#[test]
fn r766_2_control_an_a5_raw_view_of_inner_storage_keeps_the_npo_view() {
    use super::decision::seam::{Form, replan_a5_raw_view};
    let view = replan_a5_raw_view(
        &a5_view("addr-of-mut", "slot"),
        Form::Raw,
        Form::Ref { mutable: true },
    )
    .expect("the view renders");
    assert!(view.template.contains("depth2-npo"), "{view:#?}");
}

/// R784-2 (main 160): lodepng's `lodepng_crc32` reduced. `inspect` hands `crc32` an
/// element address of a RAW root (`&*in_0.offset(12)`), which the seam row refuses
/// (one element into a formal read past it); `check_crc` hands it an element address
/// of a root decided SLICE (`&*chunk.offset(4)`), the slice's own element spine.
const CRC_CALLERS: &str = r#"#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]
unsafe fn crc32(mut data: *const u8, mut length: usize) -> u32 {
    let mut r: u32 = 0 as u32;
    let mut i: usize = 0 as usize;
    while i < length {
        r = r.wrapping_add(*data.offset(i as isize) as u32);
        i = i.wrapping_add(1 as usize);
    }
    r
}
pub unsafe fn inspect(mut in_0: *mut u8, mut insize: usize) -> u32 {
    if insize < 33 as usize {
        return 0 as u32;
    }
    let mut w = in_0 as *mut u32;
    *w = 7 as u32;
    crc32(&*in_0.offset(12 as isize), 17 as usize)
}
pub unsafe fn check_crc(mut chunk: *const u8) -> u32 {
    let mut length = *chunk.offset(0 as isize) as usize;
    crc32(&*chunk.offset(4 as isize), length.wrapping_add(4 as usize))
}
"#;

/// The row's refusal at `inspect` (`in_0` model-Raw: a write through a cast) must not
/// strand `check_crc`: at the head the refusal holds `crc32::data` raw
/// (`dropped-site:seam-one-element-into-wider-formal`), `check_crc`'s argument is
/// bridged over its unrewritten `chunk.offset(4)` (E0599), and recovery reverts every
/// class: lodepng's census failure at batch 54.
#[test]
fn r784_2_a_seam_row_refusal_does_not_strand_a_slice_rooted_caller() {
    assert!(verify::type_checks_str(CRC_CALLERS));
    let out = emitted("r784_crc_callers", CRC_CALLERS);
    assert_eq!(out.reverted, 0, "{:#?}\n{}", out.degradations, out.source);
    assert!(verify::type_checks_str(&out.source), "{}", out.source);
    assert_eq!(
        reason_of(&out.degradations, "check_crc::chunk"),
        None,
        "{:#?}\n{}",
        out.degradations,
        out.source
    );
}

/// **R761-1 as ruled — shape (ii) fabricates at the site (§77).** `inspect`'s
/// `&*in_0.offset(12)` is one element of `in_0`'s allocation, handed to a formal
/// `crc32` reads `length` elements of. The row refuses the one-element view, and
/// R674-9's arm takes the pointer under the `&*` only where the callee proves a
/// constant extent; `crc32` proves none, so at the head the site is dropped and
/// holds `crc32::data` raw (brotli's six held callees at batch 54, 227 rows behind
/// them). Ruled: the pointer carries the allocation, so the site takes the raw arm
/// with the fabricated extent, receipted, and nothing is dropped.
#[test]
fn r761_1_a_refused_element_address_of_a_raw_base_takes_the_fabricated_extent() {
    let out = emitted("r761_1_fabricate", CRC_CALLERS);
    let text = compact(&out.source);
    // The spelling of the pointer is R674-9's arm's: on the census path it keeps
    // C2Rust's `&*` over the element (`from_raw_parts(&*in_0.offset(16), 4)` at
    // lodepng's proven sites), on `rewrite_m1` it is peeled. Either way the slice is
    // built over the element's own raw pointer with the fabricated extent.
    assert!(
        text.contains("crc32(core::slice::from_raw_parts(")
            && text.contains("in_0.offset(12asisize),crate::FALLBACK_SLICE_EXTENT)"),
        "{}",
        out.source
    );
    assert!(!text.contains("from_ref(&*in_0"), "{}", out.source);
    assert!(
        !out.artifacts
            .subjects
            .contains("seam-one-element-into-wider-formal"),
        "{}",
        out.artifacts.subjects
    );
}

/// The reduction of brotli's `mb#12` (class 2772, `BrotliBuildMetaBlockGreedyInternal`,
/// 46 rows behind it at batch 54): `build`'s `mb` is a thin subject, and
/// `init_splitter` takes the ADDRESS of one of its raw-pointer fields as a depth-2
/// out-param and stores a new allocation into it, beside a depth-1 scalar out-param.
const FIELD_OUT_PARAM: &str = r#"#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]
extern "C" {
    fn malloc(n: usize) -> *mut core::ffi::c_void;
}
#[repr(C)]
#[derive(Copy, Clone)]
pub struct Split {
    pub histograms: *mut u32,
    pub histograms_size: usize,
}
unsafe fn init_splitter(mut n: usize, mut histograms: *mut *mut u32, mut histograms_size: *mut usize) {
    *histograms_size = n;
    *histograms = malloc(n.wrapping_mul(4 as usize)) as *mut u32;
}
pub unsafe fn build(mut mb: *mut Split, mut n: usize) -> usize {
    init_splitter(n, &mut (*mb).histograms, &mut (*mb).histograms_size);
    (*mb).histograms_size
}
"#;

/// **R785 (relay 263) — a raw-pointer field's address takes the depth-1 view.** At
/// the head the depth-2 arm reads `&mut (*mb).histograms` as an inner pointer's
/// out-param storage and refuses it (`depth2-storage-shape-held`: not a direct
/// variable local), and `mb` degrades `borrowed-into-raw-param`. The storage is the
/// struct's raw field, not a subject's binding: the argument's own type is the
/// formal's, as at the depth-1 position beside it.
#[test]
fn r785_a_raw_pointer_field_of_a_thin_subject_takes_the_depth_one_view_at_a_depth_two_formal() {
    assert!(verify::type_checks_str(FIELD_OUT_PARAM));
    let out = emitted("r785_field_out_param", FIELD_OUT_PARAM);
    assert_eq!(
        reason_of(&out.degradations, "build::mb"),
        None,
        "{:#?}\n{}",
        out.degradations,
        out.source
    );
    assert_eq!(out.reverted, 0, "{}", out.source);
    assert!(verify::type_checks_str(&out.source), "{}", out.source);
}
