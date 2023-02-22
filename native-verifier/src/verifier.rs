// © 2022, Jakub Janaszkiewicz
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::smt_lib::*;
use backend_common::{VerificationError, VerificationResult};
use core::panic;
use log::{self, debug};
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
                    String::from_utf8(output.stdout)?
                } else {
                    let err = String::from_utf8(output.stdout)?;
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
            if line.starts_with("position: ") {
                let position_id = line.split("position: ").nth(1).unwrap();
                last_pos = position_id.parse().unwrap();
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
