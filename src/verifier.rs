// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! A module that invokes the verifier `prusti-viper`

use specifications::TypedSpecificationMap;
use prusti_viper::verifier::VerifierBuilder as ViperVerifierBuilder;
use prusti_interface::verifier::VerifierBuilder;
use prusti_interface::verifier::VerificationContext;
use prusti_interface::verifier::Verifier;
use prusti_interface::data::VerificationTask;
use prusti_interface::data::VerificationResult;
use rustc_driver::driver;
use prusti_interface::environment::EnvironmentImpl as Environment;


/// Verify a (typed) specification on compiler state.
pub fn verify<'r, 'a: 'r, 'tcx: 'a>(
    state: &'r mut driver::CompileState<'a, 'tcx>,
    spec: TypedSpecificationMap,
) {
    trace!("[verify] enter");

    debug!("Specification consists of {} elements.", spec.len());

    let env = Environment::new(state);

    debug!("Prepare verification task...");
    let annotated_procedures = env.get_annotated_procedures();
    let verification_task = VerificationTask { procedures: annotated_procedures };
    debug!("Verification task: {:?}", &verification_task);

    debug!("Prepare verifier...");
    let verifier_builder = ViperVerifierBuilder::new();
    let verification_context = VerifierBuilder::new_verification_context(&verifier_builder);
    let mut verifier = verification_context.new_verifier(&env);

    debug!("Run verifier...");
    let verification_result = verifier.verify(&verification_task);
    debug!("Verifier returned {:?}", verification_result);

    match verification_result {
        VerificationResult::Success => info!("Prusti verification succeded"),
        VerificationResult::Failure => env.err("Prusti verification failed"),
    };

    trace!("[verify] exit");
}
