mod mir_utils;
pub use self::mir_utils::*;

/// Runs statements on the same level as the macro call, timing and logging (info-level by default) how long it took.
#[macro_export]
macro_rules! run_timed {
    ($desc:expr, $($s:stmt;)*) => {
        run_timed!($desc, info, $($s;)*);
    };
    ($desc:expr, $log_level:ident, $($s:stmt;)*) => {
        let start = ::std::time::Instant::now();
        $($s;)*
        let duration = start.elapsed();
        $log_level!(
            "{} ({}.{} seconds)",
            $desc,
            duration.as_secs(),
            duration.subsec_millis() / 10
        );
    };
}

/// Runs a given function, timing and logging (info-level) how long it took, returning the function's result.
pub fn run_timed<F: FnOnce() -> T, T>(desc: &'static str, task: F) -> T {
    run_timed!(desc, let result = task(););
    result
}
