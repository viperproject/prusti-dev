#[macro_use]
extern crate log;
#[macro_use]
extern crate lazy_static;
extern crate viper;
extern crate error_chain;
extern crate env_logger;

use std::sync::{Once, ONCE_INIT};
use viper::*;

static INIT: Once = ONCE_INIT;

lazy_static! {
    static ref VIPER: Viper = Viper::new();
}

/// Setup function that is only run once, even if called multiple times.
fn setup() {
    INIT.call_once(|| { env_logger::init().unwrap(); });
}

#[test]
fn empty_program() {
    setup();

    let verification_context: VerificationContext = VIPER.new_verification_context();

    let ast_factory = verification_context.new_ast_factory();

    let program = ast_factory.new_program(vec![]);

    let verifier = verification_context.new_verifier();

    let verification_result = verifier.verify(program);

    debug!("Verification result: {:?}", verification_result);

    assert_eq!(verification_result, VerificationResult::Success());
}

#[test]
fn assert_false() {
    setup();

    let verification_context: VerificationContext = VIPER.new_verification_context();

    let ast_factory = verification_context.new_ast_factory();

    let false_lit = ast_factory.new_false_lit();

    let pos = ast_factory.new_identifier_position(0, 0, "pos-id:123");

    let assertion = ast_factory.new_assert(&false_lit, pos);

    let seqn = ast_factory.new_seqn(vec![&assertion]);

    let method = ast_factory.new_method("foo", Some(&seqn), vec![], vec![]);

    let program = ast_factory.new_program(vec![&method]);

    let verifier = verification_context.new_verifier();

    let verification_result = verifier.verify(program);

    debug!("Verification result: {:?}", verification_result);

    assert_eq!(
        verification_result,
        VerificationResult::Failure(vec![
            VerificationError::new(
                "assert.failed".to_owned(),
                "pos-id:123".to_owned()
            ),
        ])
    );
}
