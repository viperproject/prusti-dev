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
fn left() {
    setup();

    let verification_context: VerificationContext = VIPER.new_verification_context();

    let verifier = verification_context.new_verifier_tmp();
}

#[test]
fn right() {
    setup();

    let verification_context: VerificationContext = VIPER.new_verification_context();

    let verifier = verification_context.new_verifier_tmp();
}
