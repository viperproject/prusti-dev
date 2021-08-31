// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::{
    fmt::Display,
    marker::PhantomData,
    time::{Duration, Instant},
};

pub trait LogLevel {
    fn log_start(prefix: &str, name: &str);
    fn log_finish(prefix: &str, name: &str, duration: Duration);
}

pub struct Stopwatch<Level: LogLevel> {
    start_time: Instant,
    prefix: String,
    section_name: String,
    is_finished: bool,
    level: PhantomData<Level>,
}

impl Stopwatch<log_level::Info> {
    /// Starts a stopwatch logging at info level, within the given domain, timing a section with the given name.
    pub fn start<D: Display, S: ToString>(domain: D, section_name: S) -> Self {
        Self::start_info(domain, section_name)
    }
}

impl<Level: LogLevel> Stopwatch<Level> {
    fn _start(prefix: String, section_name: String) -> Self {
        Level::log_start(&prefix, &section_name);

        Self {
            start_time: Instant::now(),
            prefix,
            section_name,
            is_finished: false,
            level: PhantomData,
        }
    }

    /// Finishes up the current section, logging the time taken, and starts timing the next one.
    pub fn start_next<S: ToString>(&mut self, section_name: S) {
        let now = Instant::now();
        Level::log_finish(
            &self.prefix,
            &self.section_name,
            now.duration_since(self.start_time),
        );
        self.section_name = section_name.to_string();
        Level::log_start(&self.prefix, &self.section_name);
        self.start_time = now;
    }

    /// Finishes up the current section, logging the time taken.
    ///
    /// - Note: Simply dropping the stopwatch has the same effect.
    pub fn finish(mut self) {
        self._finish();
    }

    fn _finish(&mut self) {
        Level::log_finish(&self.prefix, &self.section_name, self.start_time.elapsed());
        self.is_finished = true;
    }
}

impl<Level: LogLevel> Drop for Stopwatch<Level> {
    fn drop(&mut self) {
        if !self.is_finished {
            self._finish();
        }
    }
}

pub mod log_level {
    use super::*;

    macro_rules! log_level {
        ($name:ident, $level:ident, $start:ident) => {
            pub struct $name;

            impl LogLevel for $name {
                fn log_start(prefix: &str, name: &str) {
                    $level!("{}Starting: {}", prefix, name);
                }

                fn log_finish(prefix: &str, name: &str, duration: Duration) {
                    $level!(
                        "{}Completed: {} ({}.{:03} seconds)",
                        prefix,
                        name,
                        duration.as_secs(),
                        duration.subsec_millis()
                    )
                }
            }

            impl Stopwatch<$name> {
                /// Starts a stopwatch logging at this level, within the given domain, timing a section with the given name.
                pub fn $start<D: Display, S: ToString>(domain: D, section_name: S) -> Self {
                    Self::_start(format!("[{}] ", domain), section_name.to_string())
                }
            }
        };
    }

    log_level!(Error, error, start_error);
    log_level!(Warn, warn, start_warn);
    log_level!(Info, info, start_info);
    log_level!(Debug, debug, start_debug);
    log_level!(Trace, trace, start_trace);
}
