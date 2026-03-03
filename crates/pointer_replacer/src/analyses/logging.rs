use std::sync::OnceLock;

fn env_truthy(name: &str) -> bool {
    std::env::var(name)
        .ok()
        .map(|value| {
            let value = value.trim();
            value == "1"
                || value.eq_ignore_ascii_case("true")
                || value.eq_ignore_ascii_case("yes")
                || value.eq_ignore_ascii_case("on")
        })
        .unwrap_or(false)
}

pub(crate) fn ownership_verbose() -> bool {
    static ENABLED: OnceLock<bool> = OnceLock::new();
    *ENABLED.get_or_init(|| {
        env_truthy("POINTER_REPLACER_OWNERSHIP_VERBOSE")
            || env_truthy("POINTER_REPLACER_ANALYSIS_VERBOSE")
    })
}
