//! **R607-1 leg B (relay 092): the Option family's unsupported use shapes.**
use super::{decision::Decision, emit_tests::ast_emitted_source_of, verify};

const MEMSET_CAST: &str = r#"
#![allow(dead_code, unused_mut, unused_variables, non_snake_case, non_camel_case_types)]
extern "C" { fn memset(s: *mut core::ffi::c_void, c: i32, n: u64) -> *mut core::ffi::c_void; }
#[repr(C)]
pub struct binn { pub header: i32, pub size: i32 }
pub unsafe fn GetValue(mut p: *mut u8, mut value: *mut binn) -> i32 {
    if value.is_null() { return 0 as i32; }
    memset(value as *mut core::ffi::c_void, 0 as i32, ::std::mem::size_of::<binn>() as u64);
    (*value).header = 0x1f22b11f as i32;
    return 1 as i32;
}
"#;

const BRANCH_SELF: &str = r#"
#![allow(dead_code, unused_mut, unused_variables, non_snake_case, unused_assignments)]
extern "C" { fn strrchr(s: *const i8, c: i32) -> *mut i8; }
pub unsafe fn parse(mut path: *const i8) -> i64 {
    let mut wd = strrchr(path, '/' as i32);
    wd = if wd.is_null() { strrchr(path, 0 as i32) } else { wd };
    return wd.offset_from(path) as i64;
}
"#;

const NULL_PARAM: &str = r#"
#![allow(dead_code, unused_mut, unused_variables, non_snake_case, unused_assignments)]
pub unsafe fn decode(mut available_out: *mut usize, mut next_out: *mut *mut u8) -> i32 {
    if *available_out != 0 && (next_out.is_null() || (*next_out).is_null()) { return 1 as i32; }
    if *available_out == 0 { next_out = 0 as *mut *mut u8; }
    if !next_out.is_null() { *(*next_out) = 0 as u8; }
    return 0 as i32;
}
"#;

fn decision_of(input: &str, function: &str, binding: &str) -> String {
    assert!(verify::type_checks_str(input));
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let table = super::decide_table(tcx).expect("native decisions");
        let (_, decision) = table
            .entries
            .iter()
            .find(|(subject, _)| {
                tcx.item_name(subject.fn_did.to_def_id()).as_str() == function
                    && subject.param_name.as_deref() == Some(binding)
            })
            .expect("subject");
        match decision {
            Decision::Degraded(degradation) => {
                format!("{} @{:?}", degradation.reason.key(), degradation.site)
            }
            other => format!("{other:?}").chars().take(60).collect::<String>(),
        }
    })
    .expect("fixture compiler context")
}

/// **The witness: libtree's `parse_ld_config_file::wd` shape.** The subject
/// is reassigned through a branch whose other arm is a raw value:
/// `wd = if wd.is_null() { path } else { wd };`. The self arm keeps the Option
/// value; only the other arm needs the raw→Option adapter, so the family takes
/// the assignment. (The initializer is a raw parameter here, a value the
/// family renders by itself — a null initializer and a local's address — so
/// the witness isolates the branch shape.)
const BRANCH_SELF_PARAM: &str = r#"
// wave6o-branch-self-frame
#![allow(dead_code, unused_mut, unused_variables, non_snake_case, unused_assignments)]
pub unsafe fn parse(mut flag: i32) -> i64 {
    let mut root: i8 = 47 as i8;
    let mut wd = 0 as *mut i8;
    if flag != 0 { wd = &mut root as *mut i8; }
    wd = if wd.is_null() { &mut root as *mut i8 } else { wd };
    return *wd as i64;
}
"#;

/// The model's verdict for `wd` is pinned `Ref` (it reads a local's address
/// as Raw), so the witness measures the Option family alone.
fn branch_self_frame() {
    super::test_model_override::set(
        "wave6o-branch-self-frame",
        Vec::new(),
        vec![(
            "parse::wd".to_owned(),
            crate::analyses::borrow_ownership::SlotKind::Ref,
        )],
    );
}

#[test]
fn wave6o_a_branch_self_reassignment_is_an_option_value() {
    let _frame = super::test_model_override::frame_lock();
    branch_self_frame();
    let decision = decision_of(BRANCH_SELF_PARAM, "parse", "wd");
    let output = ast_emitted_source_of(BRANCH_SELF_PARAM);
    super::test_model_override::clear();
    assert!(decision.starts_with("Opt {"), "{decision}");
    let output = output.expect("native emission");
    let flat: String = output.split_whitespace().collect::<Vec<_>>().join(" ");
    assert!(flat.contains("wd = if wd.is_none() {"), "{output}");
    assert!(flat.contains("} else { wd };"), "{output}");
    assert!(
        !flat.contains("let mut wd = slash;"),
        "the declaration is converted:\n{output}"
    );
}

/// libtree's exact shape (`wd` initialized from `strrchr`): the branch no
/// longer refuses it; the NEXT wall is the foreign raw return into the Option
/// local, `return-not-adapted` — wave-6l's, where libtree's `comment` (same
/// function, `strchr`) already holds at batch 48.
#[test]
fn wave6o_libtree_s_shape_moves_to_its_next_wall() {
    assert_eq!(
        decision_of(BRANCH_SELF, "parse", "wd").split(" @").next(),
        Some("return-not-adapted")
    );
}

/// Control: the subject is a branch arm assigned to ANOTHER local
/// (`let q = if .. { .. } else { wd };`) — not a self-reassignment, so the arm
/// is a copy of the subject out of Option form, which the family does not
/// render here; the use stays refused.
#[test]
fn wave6o_a_branch_arm_copied_to_another_local_is_not_taken() {
    let input = BRANCH_SELF_PARAM.replace(
        "    wd = if wd.is_null() { &mut root as *mut i8 } else { wd };\n    return *wd as i64;",
        "    let mut q = if wd.is_null() { &mut root as *mut i8 } else { wd };\n    return *q as i64;",
    );
    assert!(
        input.contains("} else { wd };\n    return *q"),
        "fixture edit applied"
    );
    let _frame = super::test_model_override::frame_lock();
    branch_self_frame();
    let decision = decision_of(&input, "parse", "wd");
    super::test_model_override::clear();
    assert!(decision.starts_with("opt-use-unsupported"), "{decision}");
}

/// binn's `memset(value as *mut c_void, ..)` and brotli's parameter null
/// assignment are shapes the family TAKES when its stage is on. At batch 48 both
/// corpus subjects were re-decided after the family was withdrawn for them
/// (`seam-positive-retention`, `depth2-storage-shape-held`), so their
/// `opt-use-unsupported` names the fallback walk, not the shape.
#[test]
fn wave6o_a_cast_argument_and_a_null_assignment_are_taken_with_the_family_on() {
    let cast = decision_of(MEMSET_CAST, "GetValue", "value");
    assert!(cast.starts_with("Opt {"), "{cast}");
    let null = decision_of(NULL_PARAM, "decode", "next_out");
    assert!(null.starts_with("Opt {"), "{null}");
}
