// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! A module that invokes the verifier `prusti-viper`

use specifications::TypedSpecificationMap;
use prusti_interface::verifier::Verifier;
use prusti_interface::data::VerificationTask;
use prusti_interface::data::VerificationResult;
use rustc_driver::driver;
use prusti_viper::verifier::VerifierBuilder;
use environment::Environment;

/// Verify a (typed) specification on compiler state.
pub fn verify<'r, 'a: 'r, 'tcx: 'a>(state: &'r mut driver::CompileState<'a, 'tcx>, typed_specifications: TypedSpecificationMap) {
    trace!("[verify] enter");

    debug!("typed_specifications: {:?}", typed_specifications);

    let mut environment = Environment::new(state);

    let verification_task = VerificationTask { procedures: vec![] };

    let mut verifier_builder = VerifierBuilder::new();
    let mut verification_context = verifier_builder.new_verification_context();
    let mut verifier = verification_context.new_verifier();

    let verification_result = verifier.verify(&mut environment, &verification_task);

    match verification_result {
        VerificationResult::Success => info!("Prusti verification succeded"),
        VerificationResult::Failure => info!("Prusti verification failed")
    };

    trace!("[verify] exit");
}
