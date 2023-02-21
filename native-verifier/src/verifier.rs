// © 2022, Jakub Janaszkiewicz
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::smt_lib::*;
use backend_common::{VerificationError, VerificationResult};
use core::panic;
use log::{self, debug, info, warn};
use prusti_common::vir::program::Program;
use prusti_utils::{report::log::report_with_writer, run_timed};
use std::{
    error::Error,
    io::Write,
    process::{Command, Stdio},
};

pub struct Verifier {
    z3_exe: String,
}

impl Verifier {
    pub fn new(z3_exe: String) -> Self {
        Self { z3_exe }
    }

    pub fn verify(&mut self, program: &Program) -> VerificationResult {
        let Program::Low(program) = program else {
            panic!("Lithium backend only supports low programs");
        };

        run_timed!("Translation to SMT-LIB", debug,
            let mut smt = SMTLib::new();
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

        run_timed!("SMT verification", debug,
            let result: Result<String, Box<dyn Error>> = try {
                let mut child = Command::new(self.z3_exe.clone())
                    .args(["-smt2", "-in"])
                    .stdin(Stdio::piped())
                    .stderr(Stdio::piped())
                    .stdout(Stdio::piped())
                    .spawn()?;

                child.stdin
                    .as_mut()
                    .ok_or("Child process stdin has not been captured!")?
                    .write_all(smt_program.as_bytes())?;

                let output = child.wait_with_output()?;

                if output.status.success() {
                    let raw_output = String::from_utf8(output.stdout)?;
                    if raw_output.lines().any(|line| line == "sat" || line == "unknown") {
                        Err(raw_output)?
                    } else {
                        raw_output
                    }
                } else {
                    let err = String::from_utf8(output.stdout)?;
                    Err(err)?
                }
            };

            let is_failure = match result {
                Ok(output) => {
                    info!("SMT verification output:\n{}", output);
                    !output.contains("unsat")
                }
                Err(err) => {
                    warn!("SMT verification errors:\n{}", err.to_string());
                    true
                }
            };
        );

        if is_failure {
            let mut errors: Vec<VerificationError> = vec![];

            let error_full_id = "verification.error".to_string();
            let pos_id = None;
            let offending_pos_id = None;
            let reason_pos_id = None;
            let message = "At least one assertion was 'sat' or 'unknown'".to_string();
            let counterexample = None;

            errors.push(VerificationError::new(
                error_full_id,
                pos_id,
                offending_pos_id,
                reason_pos_id,
                message,
                counterexample,
            ));

            VerificationResult::Failure(errors)
        } else {
            VerificationResult::Success
        }
    }
}
