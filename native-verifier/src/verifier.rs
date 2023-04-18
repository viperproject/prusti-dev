// © 2022, Jakub Janaszkiewicz
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::smt_lib::*;
use backend_common::{VerificationError, VerificationResult};
use core::panic;
use lazy_static::lazy_static;
use log::{self, debug};
use prusti_common::vir::program::Program;
use prusti_utils::{report::log::report_with_writer, run_timed};
use regex::Regex;
use std::{
    error::Error,
    io::Write,
    process::{Command, Stdio},
};

// lazy regex for parsing z3 output
lazy_static! {
    static ref POSITION_REGEX: Regex = Regex::new(r#"^"?position: (\d+)"?"#).unwrap();
}

pub struct Verifier {
    smt_solver_exe: String,
}

impl Verifier {
    pub fn new(z3_exe: String) -> Self {
        Self {
            smt_solver_exe: z3_exe,
        }
    }

    pub fn verify(&mut self, program: &Program) -> VerificationResult {
        let Program::Low(program) = program else {
            panic!("Lithium backend only supports low programs");
        };

        let is_z3 = self.smt_solver_exe.ends_with("z3");

        run_timed!("Translation to SMT-LIB", debug,
            let mut smt = SMTLib::new(is_z3);
            program.build_smt(&mut smt);
            let smt_program = smt.to_string();

            report_with_writer(
                "smt",
                format!("lithium_{}.smt2", program.name),
                |writer| {
                    writer.write_all(smt_program.as_bytes()).unwrap();
                },
            );
        );

        run_timed!(format!("SMT verification with {}", if is_z3 {"Z3"} else {"CVC5"}), debug,
            let result: Result<String, Box<dyn Error>> = try {
                let mut command = Command::new(self.smt_solver_exe.clone());

                if is_z3 {
                    command.args(&["-smt2", "-in"]);
                } else {
                    command.args(&["--incremental"]);
                }

                let mut child = command.stdin(Stdio::piped())
                    .stderr(Stdio::piped())
                    .stdout(Stdio::piped())
                    .spawn()?;

                child.stdin
                    .as_mut()
                    .ok_or("Child process stdin has not been captured!")?
                    .write_all(smt_program.as_bytes())?;

                let output = child.wait_with_output()?;

                if output.status.success() {
                    String::from_utf8(output.stdout)?
                } else {
                    let err = String::from_utf8(output.stdout)?;

                    // only lines that contain "error" are actual errors
                    let err = err.lines().filter(|line| line.contains("error")).collect::<Vec<_>>().join("\n");

                    Err(err)?
                }
            };
        );

        let mut errors = vec![];

        // TODO: Actual unexpected error handling
        if let Err(err) = result {
            errors.push(VerificationError::new(
                "assert.failed:assertion.false".to_string(),
                Some("0".to_string()),
                Some("0".to_string()),
                Some("0".to_string()),
                format!("Z3 failed with error: {}", err),
                None,
            ));

            return VerificationResult::Failure(errors);
        }

        let mut last_pos: i32 = 0;
        for line in result.unwrap().lines() {
            if let Some(caps) = POSITION_REGEX.captures(line) {
                last_pos = caps[1].parse().unwrap();
            } else if line == "sat" || line == "unknown" {
                errors.push(VerificationError::new(
                    "assert.failed:assertion.false".to_string(),
                    Some("0".to_string()),
                    Some(last_pos.to_string()),
                    Some("0".to_string()),
                    format!("Assert might fail. Assertion might not hold."),
                    None,
                ));
            }
        }

        if errors.is_empty() {
            VerificationResult::Success
        } else {
            VerificationResult::Failure(errors)
        }
    }
}
