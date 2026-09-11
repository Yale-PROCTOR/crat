//! Row (a) CALL-CLOBBER-SCOPE: a callee can only write what it can reach.

/// A-W01, the `url_get_hostname` anchor. `protocol` is a closed-Fresh return; a
/// non-allocator local call sits between it and its `free`. `keep` is an
/// unrelated incoming reference. Before row (a) the middle call clobbers every
/// cell, so the freed operand reads Unknown and overlaps `keep`; after it, the
/// freed operand keeps its exact Fresh root and `keep` survives.
const ANCHOR: &str = r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut u8; fn free(p: *mut core::ffi::c_void); }
unsafe fn get_protocol(u: *mut u8) -> *mut u8 { malloc(8) }
unsafe fn get_auth(u: *mut u8) -> *mut u8 { u }
pub unsafe fn hostname(u: *mut u8, keep: *const u8) -> u8 {
    let protocol = get_protocol(u);
    let value = *keep;
    let _auth = get_auth(u);
    free(protocol as *mut core::ffi::c_void);
    value
}
"#;

/// A-W02: the same shape, except `protocol`'s own address escapes before the
/// middle call. The callee could reach that cell, so Unknown must be preserved
/// and `keep` must NOT survive.
const ANCHOR_ADDRESS_TAKEN: &str = r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut u8; fn free(p: *mut core::ffi::c_void); }
unsafe fn get_protocol(u: *mut u8) -> *mut u8 { malloc(8) }
unsafe fn get_auth(u: *mut u8) -> *mut u8 { u }
unsafe fn stash(slot: *mut *mut u8) { let _ = *slot; }
pub unsafe fn hostname(u: *mut u8, keep: *const u8) -> u8 {
    let mut protocol = get_protocol(u);
    let value = *keep;
    stash(&raw mut protocol);
    let _auth = get_auth(u);
    free(protocol as *mut core::ffi::c_void);
    value
}
"#;

/// A-W08 must-not-move: the `buffer_free` self-free pair stays Raw.
const SELF_FREE_PAIR: &str = r#"
unsafe extern "C" { fn free(p: *mut core::ffi::c_void); }
#[repr(C)] pub struct Buffer { alloc: *mut u8 }
pub unsafe fn buffer_free(s: *mut Buffer) {
    free((*s).alloc as *mut core::ffi::c_void);
    free(s as *mut core::ffi::c_void);
}
"#;

#[test]
fn a_w01_fresh_return_survives_a_non_allocator_local_call() {
    assert!(
        super::tests::accepts(ANCHOR, &[("hostname", 2, 0)]),
        "the middle call cannot reach `protocol`'s own cell, so the free keeps its exact Fresh root and the \
         unrelated incoming reference is not charged for it"
    );
}

#[test]
fn a_w02_an_address_taken_local_is_still_clobbered() {
    assert!(
        !super::tests::accepts(ANCHOR_ADDRESS_TAKEN, &[("hostname", 2, 0)]),
        "once `protocol`'s address escapes, a callee can reach that cell and Unknown must be preserved"
    );
}

#[test]
fn a_w08_buffer_free_self_free_pair_stays_raw() {
    assert!(
        !super::tests::accepts(SELF_FREE_PAIR, &[("buffer_free", 1, 0)]),
        "row (a) must not promote the self-free pair: freeing the container retires the subject itself"
    );
}

/// A-W03 (required by R318-4): a pointer stored BEHIND an argument is memory,
/// not a caller local, so an opaque local call must still clobber it. The
/// selection is at depth 1 -- the cell reached by dereferencing the argument.
const DEPTH_ONE_BEHIND_ARGUMENT: &str = r#"
unsafe extern "C" { fn free(p: *mut core::ffi::c_void); }
unsafe fn opaque(slot: *mut *mut u8) -> *mut u8 { *slot }
pub unsafe fn deep(pp: *mut *mut u8) -> *mut u8 {
    let inner = *pp;
    let _echo = opaque(pp);
    free(inner as *mut core::ffi::c_void);
    *pp
}
"#;

/// A-W03 is REPORT-ONLY, not an assertion, and that is a finding rather than a
/// concession. A-K01 (preserve depth >= 1 cells too) leaves this fixture green,
/// so an assertion here would witness nothing. The representation is why:
///   * a projected store (`*pp = ...`) is not `place.as_local()`, so `write`
///     falls to the whole-state `clobber` -- a depth >= 1 cell is therefore
///     never refined to a distinct known root;
///   * the only known depth >= 1 roots are a parameter's `Input` cells, and
///     `(Input, Input)` pairs to `PossibleInputAlias`, so preserving such a cell
///     instead of clobbering it does not change any overlap verdict.
/// So no fixture in this representation can make the depth >= 1 clobber
/// observable through `accepts`. The probe records the measurement; the
/// discriminating witness R318-4 asks for needs either a different observation
/// channel or row (b)'s Field roots, which do refine depth >= 1.
#[test]
fn a_w03_probe_depth_one_cell_behind_an_argument() {
    let accepted = super::tests::accepts(DEPTH_ONE_BEHIND_ARGUMENT, &[("deep", 1, 1)]);
    println!(
        "receipt.A-W03 depth1_behind_argument_accepted={accepted} (report-only: A-K01 cannot flip it)"
    );
}
