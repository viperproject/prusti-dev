// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! A module that invokes the verifier `prusti-viper`

use prusti_common::{
    config, report::user, verification_service::*, verifier::VerifierBuilder, Stopwatch,
};
use prusti_interface::{
    data::{VerificationResult, VerificationTask},
    environment::Environment,
    specifications::TypedSpecificationMap,
};
use prusti_server::{PrustiServerConnection, ServerSideService, VerifierRunner};
use prusti_viper::verifier::Verifier;
use rustc_driver::driver;

/// Verify a (typed) specification on compiler state.
pub fn verify<'r, 'a: 'r, 'tcx: 'a>(
    state: &'r mut driver::CompileState<'a, 'tcx>,
    spec: TypedSpecificationMap,
) {
    trace!("[verify] enter");

    let env = Environment::new(state);

    if env.has_errors() {
        warn!("The compiler reported an error, so the program will not be verified.");
    } else {
        debug!("Specification consists of {} elements.", spec.len());

        debug!("Prepare verification task...");
        let annotated_procedures = env.get_annotated_procedures();
        let verification_task = VerificationTask {
            procedures: annotated_procedures,
        };
        debug!("Verification task: {:?}", &verification_task);

        user::message(format!(
            "Verification of {} items...",
            verification_task.procedures.len()
        ));

        let verification_result = if verification_task.procedures.is_empty() {
            VerificationResult::Success
        } else {
            debug!("Dump borrow checker info...");
            env.dump_borrowck_info(&verification_task.procedures);

            let mut verifier = Verifier::new(&env, &spec);
            let source_path = env.source_path();
            let program_name = source_path
                .file_name()
                .unwrap()
                .to_str()
                .unwrap()
                .to_owned();

            let verification_result = verifier.verify(&verification_task, |program| {
                if let Some(server_address) = config::server_address() {
                    let server_address = if server_address == "MOCK" {
                        ServerSideService::spawn_off_thread()
                    } else {
                        server_address.parse().unwrap_or_else(|e| {
                            panic!("Invalid server address: {} (error: {})", server_address, e)
                        })
                    };
                    let service = PrustiServerConnection::new(server_address);

                    let request = VerificationRequest {
                        program,
                        program_name: format!("{}.service", program_name),
                        backend_config: Default::default(),
                    };
                    service.verify(request)
                } else {
                    let stopwatch = Stopwatch::start("JVM startup");
                    let verifier_builder = VerifierBuilder::new();
                    stopwatch.finish();
                    VerifierRunner::with_default_configured_runner(&verifier_builder, |runner| {
                        runner.verify(program, program_name.as_str())
                    })
                }
            });
            debug!("Verifier returned {:?}", verification_result);

            verification_result
        };

        match verification_result {
            VerificationResult::Success => {
                user::message(format!(
                    "Successful verification of {} items",
                    verification_task.procedures.len()
                ));
            }
            VerificationResult::Failure => {
                user::message("Verification failed");
                assert!(env.has_errors());
            }
        };
    }

    trace!("[verify] exit");
}
