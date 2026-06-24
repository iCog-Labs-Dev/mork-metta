use std::sync::OnceLock;

fn debug_flag(name: &str) -> bool {
    std::env::var_os(name).is_some()
}

pub(crate) fn logical_failure_warnings_enabled() -> bool {
    static ENABLED: OnceLock<bool> = OnceLock::new();
    *ENABLED.get_or_init(|| {
        debug_flag("MORK_DEBUG_FAILURES") || debug_flag("MORK_DEBUG_LOGICAL_FAILURES")
    })
}

pub(crate) fn logical_failure(message: impl FnOnce() -> String) {
    if logical_failure_warnings_enabled() {
        eprintln!("{}", message());
    }
}
