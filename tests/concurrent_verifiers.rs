#[macro_use]
extern crate log;
#[macro_use]
extern crate lazy_static;
extern crate viper;
extern crate error_chain;
extern crate env_logger;

use viper::*;
use std::thread;
use std::thread::JoinHandle;

lazy_static! {
    static ref VIPER: Viper = Viper::new();
}

/// Test bug https://bitbucket.org/viperproject/silicon/issues/315/exception-while-building-silicon-instances
#[test]
fn concurrent_verifier_initialization() {
    env_logger::init().unwrap();

    let mut handlers: Vec<JoinHandle<()>> = vec![];

    let num_threads = 3;

    for i in 0..num_threads {
        handlers.push(thread::spawn(move || {
            debug!("Start of thread {:?}", i);
            let verification_context: VerificationContext = VIPER.new_verification_context();

            let ast = verification_context.new_ast_factory();

            let program = ast.new_program(vec![]);

            let verifier = verification_context.new_verifier();

            let verification_result = verifier.verify(program);

            assert_eq!(verification_result, VerificationResult::Success());

            debug!("End of thread {:?}", i);
        }));
    }

    for handler in handlers {
        handler.join().unwrap();
    }
}
