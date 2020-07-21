// Copyright 2014-2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Code adapted from the Rust compiler source code, file `librustc_driver/lib.rs`.

use rustc::session::CompileIncomplete;
use rustc::session::CompileResult;
use rustc::session::{config, Session};
use rustc_driver::in_rustc_thread;
use rustc_errors as errors;
use std::panic;
use syntax_pos::MultiSpan;

static PRUSTI_BUG_REPORT_URL: &str = "<https://github.com/viperproject/prusti-dev/issues>";

/// Run a procedure which will detect panics in the compiler and print nicer
/// error messages rather than just failing the test.
///
/// The diagnostic emitter yielded to the procedure should be used for reporting
/// errors of the compiler.
fn monitor<F: FnOnce() + Send + 'static>(f: F) {
    let result = in_rustc_thread(move || f());

    if let Err(value) = result {
        // Thread panicked without emitting a fatal diagnostic
        if !value.is::<errors::FatalErrorMarker>() {
            // Emit a newline
            eprintln!("");

            let emitter = Box::new(errors::emitter::EmitterWriter::stderr(
                errors::ColorConfig::Auto,
                None,
                false,
                false,
            ));
            let handler = errors::Handler::with_emitter(true, false, emitter);

            // a .span_bug or .bug call has already printed what
            // it wants to print.
            if !value.is::<errors::ExplicitBug>() {
                handler.emit(&MultiSpan::new(), "unexpected panic", errors::Level::Bug);
            }

            let xs = vec![
                "the compiler or Prusti unexpectedly panicked.".to_string(),
                "possible reasons include the usage of Rust features that are not supported by Prusti.".to_string(),
                format!("we would appreciate a bug report for Prusti: {}", PRUSTI_BUG_REPORT_URL),
                format!("Prusti hash {} ({}) built on {}",
                        option_env!("COMMIT_HASH").unwrap_or("<unknown>"),
                        option_env!("COMMIT_TIME").unwrap_or("<unknown>"),
                        option_env!("BUILD_TIME").unwrap_or("<unknown>"),),
                format!("rustc {} running on {}",
                        option_env!("CFG_VERSION").unwrap_or("<unknown>"),
                        config::host_triple()),
            ];

            for note in &xs {
                handler.emit(&MultiSpan::new(), &note, errors::Level::Note);
            }
        }

        panic::resume_unwind(Box::new(errors::FatalErrorMarker));
    }
}

pub fn run<F>(run_compiler: F) -> isize
where
    F: FnOnce() -> (CompileResult, Option<Session>) + Send + 'static,
{
    monitor(move || {
        let (result, session) = run_compiler();

        if let Some(ref sess) = &session {
            sess.abort_if_errors();
        }

        if let Err(CompileIncomplete::Errored(_)) = result {
            match session {
                Some(_) => {
                    panic!("error reported but abort_if_errors didn't abort");
                }
                None => {
                    let emitter = errors::emitter::EmitterWriter::stderr(
                        errors::ColorConfig::Auto,
                        None,
                        true,
                        false,
                    );
                    let handler = errors::Handler::with_emitter(true, false, Box::new(emitter));
                    handler.emit(
                        &MultiSpan::new(),
                        "aborting due to previous error(s)",
                        errors::Level::Fatal,
                    );
                    panic::resume_unwind(Box::new(errors::FatalErrorMarker));
                }
            }
        }
    });
    0
}

pub fn silent_run<F>(run_compiler: F) -> isize
where
    F: FnOnce() -> (CompileResult, Option<Session>) + Send + 'static,
{
    let result = in_rustc_thread(move || {
        let (compile_result, session) = run_compiler();

        if let Some(ref sess) = &session {
            if sess.has_errors() {
                return 2;
            }
        }

        match compile_result {
            Err(CompileIncomplete::Errored(_)) => match session {
                Some(_) => 3,
                None => 4,
            },

            Err(CompileIncomplete::Stopped) => 0,

            Ok(_) => 0,
        }
    });

    match result {
        // Thread panicked
        Err(_value) => return 1,

        Ok(exit_code) => exit_code,
    }
}
