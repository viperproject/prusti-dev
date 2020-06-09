// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#[macro_use]
extern crate log;
extern crate config as config_crate;
extern crate serde;
extern crate walkdir;
#[macro_use]
extern crate lazy_static;

pub mod config;
pub mod driver_utils;
pub mod report;

/// Runs statements on the same level as the macro call, timing and logging (info-level by default) how long it took.
#[macro_export]
macro_rules! run_timed {
    ($desc:expr, $($s:stmt;)*) => {
        run_timed!($desc, info, $($s;)*);
    };
    ($desc:expr, $log_level:ident, $($s:stmt;)*) => {
        $log_level!("Starting: {}", $desc);
        let start = ::std::time::Instant::now();
        $($s;)*
        let duration = start.elapsed();
        $log_level!(
            "Completed: {} ({}.{} seconds)",
            $desc,
            duration.as_secs(),
            duration.subsec_millis() / 10
        );
    };
}

/// Runs a given function, timing and logging (info-level) how long it took, returning the function's result.
pub fn run_timed<F: FnOnce() -> T, T>(desc: &str, task: F) -> T {
    run_timed!(desc, let result = task(););
    result
}
