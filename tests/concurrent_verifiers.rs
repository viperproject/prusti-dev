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

/// Regression test for the following bug:
/// https://bitbucket.org/viperproject/silicon/issues/315/exception-while-building-silicon-instances
#[test]
fn concurrent_verifier_initialization() {
    env_logger::init().unwrap();

    const MAX_NUM_THREADS: u32 = 2;
    const MIN_NUM_THREADS: u32 = 10;

    for num_threads in MIN_NUM_THREADS..(MAX_NUM_THREADS + 1) {
        let mut handlers: Vec<JoinHandle<()>> = vec![];

        for _ in 0..num_threads {
            handlers.push(thread::spawn(move || {
                let verification_context: VerificationContext = VIPER.new_verification_context();

                let ast = verification_context.new_ast_factory();

                let program = ast.program(vec![], vec![], vec![], vec![], vec![]);

                let verifier = verification_context.new_verifier();

                let verification_result = verifier.verify(program);

                assert_eq!(verification_result, VerificationResult::Success());
            }));
        }

        for handler in handlers.drain(..) {
            handler.join().unwrap();
        }
    }
}
