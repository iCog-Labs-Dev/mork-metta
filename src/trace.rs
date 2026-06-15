/// Debug tracing infrastructure for the evaluator.
///
/// When compiled with `--features trace`, `trace!` and related macros emit
/// indented debug output to stderr. Without the feature, all trace calls
/// compile to nothing — zero runtime cost.
///
/// # Depth limiting
///
/// Set `TRACE_DEPTH=N` env var to limit trace output to the first N levels
/// of eval nesting. Default is 6. This lets you see top-level structure
/// without drowning in deep recursion (e.g., fib(30) produces 2.7M trace
/// lines without a limit).
///
/// # Usage
///
/// ```bash
/// TRACE_DEPTH=4 cargo run --features trace -- file.metta
/// ```
///
/// ```rust,ignore
/// trace!("eval: dispatching {:?}", expr);
/// trace_enter!("call_function: {}", name);
/// // ... nested work produces indented output ...
/// trace_exit!();
/// ```

// ===== Depth tracking (only compiled when trace is on) =====

#[cfg(feature = "trace")]
mod depth {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static DEPTH: AtomicUsize = AtomicUsize::new(0);
    pub fn get() -> usize {
        DEPTH.load(Ordering::Relaxed)
    }
    pub fn inc() {
        DEPTH.fetch_add(1, Ordering::Relaxed);
    }
    pub fn dec() {
        DEPTH.fetch_sub(1, Ordering::Relaxed);
    }
}

// ===== Internal functions referenced by macros =====

#[cfg(feature = "trace")]
#[doc(hidden)]
pub fn __depth() -> usize {
    depth::get()
}

#[cfg(feature = "trace")]
#[doc(hidden)]
pub fn __inc() {
    depth::inc()
}

#[cfg(feature = "trace")]
#[doc(hidden)]
pub fn __dec() {
    depth::dec()
}

/// Maximum trace depth. Trace lines deeper than this are suppressed.
/// Override with `TRACE_DEPTH=N` env var (parsed at first access).
#[cfg(feature = "trace")]
pub static MAX_DEPTH: std::sync::LazyLock<usize> = std::sync::LazyLock::new(|| {
    std::env::var("TRACE_DEPTH")
        .ok()
        .and_then(|v| v.parse::<usize>().ok())
        .unwrap_or(6)
});

// ===== Macros =====

/// Emit a trace line with indentation reflecting current eval depth.
/// Only emits when depth ≤ TRACE_DEPTH (default 6).
/// Compiles to nothing when `trace` feature is off.
#[macro_export]
macro_rules! trace {
    ($($arg:tt)*) => {
        #[cfg(feature = "trace")]
        if crate::trace::__depth() <= *crate::trace::MAX_DEPTH {
            eprintln!("{:d$}{}", "", format_args!($($arg)*), d = crate::trace::__depth() * 2);
        }
    };
}

/// Emit a trace line and increment indentation. Depth is always tracked
/// (even when suppressed) so indentation stays correct.
#[macro_export]
macro_rules! trace_enter {
    ($($arg:tt)*) => {
        #[cfg(feature = "trace")]
        {
            if crate::trace::__depth() <= *crate::trace::MAX_DEPTH {
                eprintln!("{:d$}{}", "", format_args!($($arg)*), d = crate::trace::__depth() * 2);
            }
            crate::trace::__inc();
        }
    };
}

/// Decrement trace indentation.
#[macro_export]
macro_rules! trace_exit {
    () => {
        #[cfg(feature = "trace")]
        crate::trace::__dec();
    };
}
