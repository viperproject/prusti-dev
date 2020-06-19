// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::{
    marker::PhantomData,
    time::{Duration, Instant},
};

pub trait LogLevel {
    fn log_start(name: &String);

    fn log_finish(name: &String, duration: Duration);
}

pub struct Stopwatch<Level: LogLevel> {
    start_time: Instant,
    section_name: String,
    is_finished: bool,
    level: PhantomData<Level>,
}

impl Stopwatch<log_level::Info> {
    pub fn start<S: ToString>(section_name: S) -> Self {
        Self::_start(section_name)
    }
}

impl<Level: LogLevel> Stopwatch<Level> {
    fn _start<S: ToString>(section_name: S) -> Self {
        let section_name = section_name.to_string();
        Level::log_start(&section_name);

        Self {
            start_time: Instant::now(),
            section_name,
            is_finished: false,
            level: PhantomData,
        }
    }

    pub fn start_next_section<S: ToString>(&mut self, section_name: S) {
        let now = Instant::now();
        Level::log_finish(&self.section_name, now.duration_since(self.start_time));
        self.section_name = section_name.to_string();
        Level::log_start(&self.section_name);
        self.start_time = now;
    }

    pub fn finish(mut self) {
        self._finish();
    }

    fn _finish(&mut self) {
        Level::log_finish(&self.section_name, self.start_time.elapsed());
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
                fn log_start(name: &String) {
                    $level!("Starting: {}", name);
                }

                fn log_finish(name: &String, duration: Duration) {
                    $level!(
                        "Completed: {} ({}.{} seconds)",
                        name,
                        duration.as_secs(),
                        duration.subsec_millis() / 10
                    )
                }
            }

            impl Stopwatch<$name> {
                pub fn $start<S: ToString>(section_name: S) -> Self {
                    Self::_start(section_name)
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
