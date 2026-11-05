//! Relay main/388 stage 3 (B), 270's callee-unknown group: a callee's free of a field of its
//! parameter is routed into the caller as Unknown, and meets the caller's protected parameters
//! (`activity_new` freeing `activity->scope` through `activity_free` on its error path). The precise
//! form: when the callee wrote no field cell between its entry and the free, the field's content at
//! the free is its content at the call, and when the caller stored that field through a single known
//! object since its last possible write, the routed free names what the caller stored. Everything
//! else stays Unknown, as before.

use rustc_middle::mir::Local;

use super::{
    objects::{ObjectRoot, ObjectSet},
    tests_call_reach::{named_local, object_facts},
    tests_return_origin::{named_function, with_program},
};
use crate::analyses::borrow_ownership::source_events::{self, SourceRole};

/// c2rust's shape: a constructor that stores fresh copies into a fresh object and frees it through
/// the program's own destructor on its error path (`copies`); the negatives -- the caller's own
/// parameter stored (`keeps`), the callee writes the field before freeing it (`rewritten`), a local
/// call writes the object between the store and the release (`touched`), an allocation in a loop
/// (`looped`).
const RELEASE: &str = r#"
use core::ffi::{c_char, c_void};
unsafe extern "C" {
    fn malloc(size: usize) -> *mut c_void;
    fn free(p: *mut c_void);
    fn strdup(s: *const c_char) -> *mut c_char;
}
pub struct Activity {
    pub scope: *mut c_char,
    pub message: *mut c_char,
}
pub unsafe fn activity_free(activity: *mut Activity) {
    free((*activity).scope as *mut c_void);
    free((*activity).message as *mut c_void);
    free(activity as *mut c_void);
}
pub unsafe fn rewrite_free(activity: *mut Activity, other: *mut c_char) {
    (*activity).scope = other;
    free((*activity).scope as *mut c_void);
}
pub unsafe fn touch(activity: *mut Activity, other: *mut c_char) {
    (*activity).message = other;
}
pub unsafe fn copies(scope: *const c_char, message: *const c_char) -> *mut Activity {
    let activity = malloc(16) as *mut Activity;
    (*activity).scope = strdup(scope);
    (*activity).message = strdup(message);
    activity_free(activity);
    0 as *mut Activity
}
pub unsafe fn keeps(scope: *mut c_char, message: *const c_char) -> *mut Activity {
    let activity = malloc(16) as *mut Activity;
    (*activity).scope = scope;
    (*activity).message = strdup(message);
    activity_free(activity);
    0 as *mut Activity
}
pub unsafe fn rewritten(scope: *const c_char, other: *mut c_char) -> *mut Activity {
    let activity = malloc(16) as *mut Activity;
    (*activity).scope = strdup(scope);
    rewrite_free(activity, other);
    0 as *mut Activity
}
pub unsafe fn touched(scope: *const c_char, message: *mut c_char) -> *mut Activity {
    let activity = malloc(16) as *mut Activity;
    (*activity).scope = strdup(scope);
    (*activity).message = strdup(scope);
    touch(activity, message);
    activity_free(activity);
    0 as *mut Activity
}
unsafe extern "C" {
    fn strlen(s: *const c_char) -> usize;
    fn memcpy(dest: *mut c_void, src: *const c_void, n: usize) -> *mut c_void;
}
#[derive(Copy, Clone)]
pub enum Level {
    Info,
    Warning,
}
pub struct Entry {
    pub level: Level,
    pub scope: *mut c_char,
    pub message: *mut c_char,
}
pub unsafe fn dup(text: *const c_char) -> *mut c_char {
    let length = strlen(text).wrapping_add(1);
    let copy = malloc(length) as *mut c_char;
    if copy.is_null() {
        return 0 as *mut c_char;
    }
    memcpy(copy as *mut c_void, text as *const c_void, length);
    return copy;
}
pub unsafe fn entry_free(entry: *mut Entry) {
    if entry.is_null() {
        return;
    }
    free((*entry).scope as *mut c_void);
    free((*entry).message as *mut c_void);
    free(entry as *mut c_void);
}
pub unsafe fn entry_new(level: Level, scope: *const c_char, message: *const c_char) -> *mut Entry {
    let entry = malloc(24) as *mut Entry;
    if entry.is_null() {
        return 0 as *mut Entry;
    }
    (*entry).level = level;
    (*entry).scope = dup(scope);
    (*entry).message = dup(message);
    if (*entry).scope.is_null() || (*entry).message.is_null() {
        entry_free(entry);
        return 0 as *mut Entry;
    }
    return entry;
}
pub unsafe fn looped(scope: *const c_char, n: usize) -> *mut Activity {
    let mut i: usize = 0;
    let mut last = 0 as *mut Activity;
    while i < n {
        let activity = malloc(16) as *mut Activity;
        (*activity).scope = strdup(scope);
        (*activity).message = strdup(scope);
        last = activity;
        i += 1;
    }
    activity_free(last);
    0 as *mut Activity
}
"#;

/// The objects of every free routed into `caller` from a call of `callee`, in route order.
fn routed_frees(code: &str, caller: &str, callee: &str) -> Vec<ObjectSet> {
    let mut answer = Vec::new();
    with_program(code, |program| {
        let caller = named_function(program, caller);
        let callee = named_function(program, callee);
        let facts = object_facts(program);
        let events = source_events::collect(program);
        let routed = super::routes::expand(program, &events, &facts);
        answer = routed
            .frames
            .get(&caller)
            .into_iter()
            .flatten()
            .filter(|event| {
                event.source.key.role == SourceRole::Free
                    && event
                        .route
                        .first()
                        .is_some_and(|step| step.callee == callee)
            })
            .map(|event| event.objects.clone())
            .collect();
    });
    assert!(
        !answer.is_empty(),
        "{caller} has routed frees from {callee}"
    );
    answer
}

/// Whether any free routed into `caller` from `callee` may retire the object `caller`'s parameter
/// `parameter` points to (the review's heap-only overlap against the entry's objects).
fn may_free_parameter(code: &str, caller: &str, callee: &str, parameter: &str) -> bool {
    let mut answer = None;
    with_program(code, |program| {
        let frame = named_function(program, caller);
        let wanted = named_function(program, callee);
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(frame)
            .borrow();
        let local: Local = named_local(&body, parameter);
        drop(body);
        let entry = ObjectSet::root(ObjectRoot::Input {
            function: frame,
            parameter: local,
            depth: 0,
        });
        let facts = object_facts(program);
        let events = source_events::collect(program);
        let routed = super::routes::expand(program, &events, &facts);
        answer = Some(
            routed
                .frames
                .get(&frame)
                .into_iter()
                .flatten()
                .filter(|event| {
                    event.source.key.role == SourceRole::Free
                        && event
                            .route
                            .first()
                            .is_some_and(|step| step.callee == wanted)
                })
                .any(|event| super::overlap(&entry, &event.objects, frame, true).is_some()),
        );
    });
    answer.expect("the fixture compiled")
}

/// (B): `activity_free` writes no field cell before its frees -- `free` writes no cell of a live
/// object -- and `copies` stored fresh copies into its fresh object, so every free routed from it
/// names a known object of `copies`: the two `strdup`s and the `malloc`.
#[test]
fn r388_e_b_a_freed_field_holding_a_fresh_copy_names_the_callers_store() {
    for objects in routed_frees(RELEASE, "copies", "activity_free") {
        assert!(!objects.unknown, "a resolved release: {objects:?}");
        assert!(
            objects
                .roots
                .iter()
                .all(|root| matches!(root, ObjectRoot::Fresh { .. })),
            "the stored copies and the allocation: {objects:?}"
        );
    }
    assert!(!may_free_parameter(
        RELEASE,
        "copies",
        "activity_free",
        "scope"
    ));
    assert!(!may_free_parameter(
        RELEASE,
        "copies",
        "activity_free",
        "message"
    ));
}

/// (B), the real conflict stays: `keeps` stores its own parameter, so the routed free names it.
#[test]
fn r388_e_b_a_freed_field_holding_the_callers_parameter_still_conflicts() {
    assert!(may_free_parameter(
        RELEASE,
        "keeps",
        "activity_free",
        "scope"
    ));
}

/// (B), fail closed: the callee writes the field before it frees it, a local call may write the
/// object between the caller's store and the release, or the object comes from an allocation in a
/// loop (one name for many objects) -- the routed free stays Unknown.
#[test]
fn r388_e_b_an_unproven_field_content_stays_unknown() {
    for objects in routed_frees(RELEASE, "rewritten", "rewrite_free") {
        assert!(objects.unknown, "rewritten: {objects:?}");
    }
    for (caller, callee) in [("touched", "activity_free"), ("looped", "activity_free")] {
        let frees = routed_frees(RELEASE, caller, callee);
        assert!(
            frees.iter().any(|objects| objects.unknown),
            "{caller}: a field free stays Unknown: {frees:?}"
        );
    }
    assert!(may_free_parameter(
        RELEASE,
        "rewritten",
        "rewrite_free",
        "scope"
    ));
    assert!(may_free_parameter(
        RELEASE,
        "touched",
        "activity_free",
        "scope"
    ));
    assert!(may_free_parameter(
        RELEASE,
        "looped",
        "activity_free",
        "scope"
    ));
}

/// (B), the c2rust constructor as array_list writes it (`activity_new`): a C enum stored, then each
/// field from the program's own copy function (`dup`, a call between the stores), checked, and the
/// object freed through the program's destructor on the error path. The calls to `dup` cannot reach
/// the unescaped allocation, so its cells survive them, and the routed frees name the copies.
#[test]
fn r388_e_b_the_c2rust_constructor_shape_resolves() {
    for objects in routed_frees(RELEASE, "entry_new", "entry_free") {
        assert!(!objects.unknown, "a resolved release: {objects:?}");
    }
    assert!(!may_free_parameter(
        RELEASE,
        "entry_new",
        "entry_free",
        "scope"
    ));
    assert!(!may_free_parameter(
        RELEASE,
        "entry_new",
        "entry_free",
        "message"
    ));
}
