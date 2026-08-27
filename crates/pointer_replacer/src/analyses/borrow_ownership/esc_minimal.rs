//! ESC-GAP ②-minimal exact-site selector.

#[cfg(test)]
#[derive(Clone, Debug)]
struct FixtureSite {
    escaping: bool,
    resolved_origin: bool,
    live_after_syntactic: bool,
    live_after: bool,
    selected: bool,
}

#[cfg(test)]
fn fixture_sites(_code: &str) -> Vec<FixtureSite> {
    todo!("RED: port the approved N4 extraction boundary")
}

#[cfg(test)]
mod tests {
    use super::fixture_sites;

    const ESC_W1: &str = r#"
unsafe fn save(out: *mut *mut i32, x: *mut i32) { *out = x; *x = 1; }
unsafe fn caller() -> i32 {
    let mut cell = 0i32;
    let mut slot: *mut i32 = core::ptr::null_mut();
    save(&raw mut slot, &raw mut cell);
    *slot
}
"#;

    const NO_ESCAPE: &str = r#"
unsafe fn save(out: *mut *mut i32, x: *mut i32) { let _ = out; *x = 1; }
unsafe fn caller() -> i32 {
    let mut cell = 0i32;
    let mut slot: *mut i32 = core::ptr::null_mut();
    save(&raw mut slot, &raw mut cell);
    *slot
}
"#;

    const DEAD_AFTER: &str = r#"
unsafe fn save(out: *mut *mut i32, x: *mut i32) { *out = x; }
unsafe fn caller() -> i32 {
    let mut cell = 0i32;
    let mut slot: *mut i32 = core::ptr::null_mut();
    save(&raw mut slot, &raw mut cell);
    *slot
}
"#;

    #[test]
    fn escgap_selector_nonvacuity_escw1_copy_is_selected() {
        let rows = fixture_sites(ESC_W1);
        let selected = rows.iter().filter(|row| row.selected).collect::<Vec<_>>();
        assert_eq!(selected.len(), 1);
        let row = selected[0];
        assert!(row.escaping);
        assert!(row.resolved_origin);
        assert!(!row.live_after_syntactic);
        assert!(row.live_after);
    }

    #[test]
    fn escgap_selector_escape_column_discriminates() {
        assert!(
            fixture_sites(NO_ESCAPE)
                .iter()
                .all(|row| !row.selected && !row.escaping)
        );
    }

    #[test]
    fn escgap_selector_liveness_column_discriminates() {
        let rows = fixture_sites(DEAD_AFTER);
        let escaping = rows.iter().filter(|row| row.escaping).collect::<Vec<_>>();
        assert_eq!(escaping.len(), 1);
        assert!(!escaping[0].live_after);
        assert!(!escaping[0].selected);
    }
}
