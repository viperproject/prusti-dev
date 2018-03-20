extern crate env_logger;
extern crate prusti_interface;
extern crate prusti_viper;

use prusti_viper::verifier::VerifierBuilder as ViperVerifierBuilder;
use prusti_interface::verifier::Verifier;
use prusti_interface::verifier::VerificationContext;
use prusti_interface::verifier::VerifierBuilder;
use prusti_interface::environment::*;
use prusti_interface::data::VerificationTask;
use prusti_interface::data::VerificationResult;
use prusti_interface::data::ProcedureDefId;

/// A facade to the Rust compiler.
struct FakeEnvironment {}

impl FakeEnvironment {
    fn new() -> Self {
        FakeEnvironment {}
    }
}

impl Environment for FakeEnvironment {
    type ProcedureImpl = ();
    fn get_procedure(&self, proc_def_id: ProcedureDefId) -> Self::ProcedureImpl {
        unimplemented!()
    }
}

#[test]
fn verify_empty_program() {
    env_logger::init().expect("failed to initialize env_logger");

    let verifier_builder = ViperVerifierBuilder::new();
    let verification_context = verifier_builder.new_verification_context();

    let mut verifier = verification_context.new_verifier();
    let mut fake_environment = FakeEnvironment::new();

    let verification_task = VerificationTask { procedures: vec![] };

    let verification_result = verifier.verify(&mut fake_environment, &verification_task);
    assert_eq!(verification_result, VerificationResult::Success);
}
