// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! A module that invokes the verifier `prusti-viper`

use prusti_common::report::user;
use prusti_interface::data::VerificationResult;
use prusti_interface::data::VerificationTask;
use prusti_interface::environment::Environment;
use prusti_interface::specifications::TypedSpecificationMap;
use prusti_server::PrustiServerConnection;
use prusti_server::VerifierRunner;
use prusti_viper::verification_service::*;
use prusti_viper::verifier::Verifier;
use prusti_viper::verifier::VerifierBuilder;
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
            // TODO: recreate structure of original sources in dumped sources
            let program_name = source_path
                .file_name()
                .unwrap()
                .to_str()
                .unwrap()
                .to_owned();
            let verification_result = verifier.verify(&verification_task, |program| {
                // FIXME: This is just for debugging. In the end, it would switch based on whether it has a server address, and actually connect to that rather than spawning its own server.
                if true {
                    run_timed!("JVM startup",
                        let verifier_builder = VerifierBuilder::new();
                    );
                    VerifierRunner::with_default_configured_runner(&verifier_builder, |runner| {
                        let program_name = format!("{}.direct", program_name);
                        runner.verify(program.clone(), program_name.as_str())
                    })
                } else {
                    let service = PrustiServerConnection::new_spawning_own_server();
                    let request = VerificationRequest {
                        program,
                        program_name: format!("{}.service", program_name),
                        backend_config: Default::default(),
                    };
                    service.verify(request)
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
