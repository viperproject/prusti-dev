// copied from prusti-common to avoid illogical dependency.
/// Runs statements on the same level as the macro call, timing and logging (info-level by default) how long it took.
#[macro_export]
macro_rules! run_timed {
    ($desc:expr, $($s:stmt;)*) => {
        run_timed!($desc, info, $($s;)*);
    };
    ($desc:expr, $log_level:ident, $($s:stmt;)*) => {
        $log_level!("Starting: {}", $desc);
        let start = ::std::time::Instant::now();
        $($s)*
        let duration = start.elapsed();
        $log_level!(
            "Completed: {} ({}.{} seconds)",
            $desc,
            duration.as_secs(),
            duration.subsec_millis() / 10
        );
    };
}
