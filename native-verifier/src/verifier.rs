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
use prusti_utils::{config, report::log::report_with_writer, run_timed};
use regex::Regex;
use std::{
    error::Error,
    io::Write,
    process::{Command, Stdio},
};

// lazy regex for parsing z3 output
lazy_static! {
    static ref POSITION_REGEX: Regex =
        Regex::new(r#"^"?position: (\d+)(?:, reason: (\d+))?"?"#).unwrap();
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

        if !config::unsafe_core_proof() {
            panic!("Lithium backend only supports unsafe_core_proof=true");
        }

        let is_z3 = self.smt_solver_exe.ends_with("z3");
        let solver_name = if is_z3 { "Z3" } else { "CVC5" };

        let program_name = prusti_common::report::log::to_legal_file_name(&program.name);
        let program_name = format!("{}.smt2", program_name); // TODO: path mismatch when over config length

        run_timed!("Translation to SMT-LIB", debug,
            let mut smt = SMTLib::new(is_z3);
            program.build_smt(&mut smt);
            let smt_program = smt.to_string();

            report_with_writer(
                "smt",
                program_name.clone(),
                |writer| {
                    writer.write_all(smt_program.as_bytes()).unwrap();
                },
            );
        );

        run_timed!(format!("SMT verification with {}", solver_name), debug,
            let result: Result<String, Box<dyn Error>> = try {
                let mut command = Command::new(self.smt_solver_exe.clone());

                let path = config::log_dir().join("smt").join(program_name);
                let path = path.to_str().unwrap();

                if is_z3 {
                    command.args(["-smt2", path]);
                } else {
                    command.args(["--incremental", path]);
                }

                let mut child = command.stderr(Stdio::piped())
                    .stdout(Stdio::piped())
                    .spawn()?;

                // Check if child process is running
                let child_status = child.try_wait()?;
                if let Some(exit_status) = child_status {
                    if exit_status.success() {
                        Err::<String, String>("Child process terminated prematurely.".into())?;
                    } else {
                        let err = format!("Child process failed to start with exit status: {}", exit_status);
                        Err::<String, String>(err)?;
                    }
                }

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
                format!("{} failed with unexpected error: {}", solver_name, err),
                None,
            ));

            return VerificationResult::Failure(errors);
        }

        let mut last_pos: (i32, Option<i32>) = (0, None);
        for line in result.unwrap().lines() {
            if let Some(caps) = POSITION_REGEX.captures(line) {
                let pos = caps[1].parse().unwrap();
                let res = caps.get(2).map(|r| r.as_str().parse().unwrap());
                last_pos = (pos, res);
            } else if line == "sat" || line == "unknown" {
                errors.push(VerificationError::new(
                    "assert.failed:assertion.false".to_string(),
                    Some("0".to_string()),
                    Some(last_pos.0.to_string()),
                    last_pos.1.map(|r| r.to_string()),
                    "Assert might fail. Assertion might not hold.".to_string(),
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
