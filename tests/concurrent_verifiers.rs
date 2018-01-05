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

#[test]
#[ignore] // Disabled because of bug https://bitbucket.org/viperproject/silicon/issues/315/exception-while-building-silicon-instances
fn concurrent_verifier_initialization() {
    env_logger::init().unwrap();

    let mut handlers: Vec<JoinHandle<()>> = vec![];

    let num_threads = 3;

    for i in 0..num_threads {
        handlers.push(thread::spawn(move || {
            debug!("Start of thread {:?}", i);
            let verification_context: VerificationContext = VIPER.new_verification_context();
            let _verifier = verification_context.new_verifier();
            debug!("End of thread {:?}", i);
        }));
    }

    for handler in handlers {
        handler.join().unwrap();
    }
}
