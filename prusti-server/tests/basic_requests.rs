extern crate prusti_common;
extern crate prusti_server;
extern crate viper;
#[macro_use]
extern crate lazy_static;

use prusti_common::{
    verification_service::{VerificationRequest, VerificationService},
    vir::*,
};
use prusti_server::{PrustiServerConnection, ServerSideService};
use viper::VerificationResult;

lazy_static! {
    // only start the jvm & server once
    static ref SERVER_ADDRESS: String = ServerSideService::spawn_off_thread().to_string();
}

#[test]
fn consistency_error() {
    let result = process_program(|program| {
        program.fields.push(Field {
            name: "field".to_string(), // reserved identifier
            typ: Type::Int,
        });
    });

    match result {
        VerificationResult::ConsistencyErrors(errors) => assert_eq!(errors.len(), 1),
        other => panic!(
            "consistency errors not identified, instead found {:?}",
            other
        ),
    }
}

#[test]
fn empty_program() {
    let result = process_program(|_| ());

    match result {
        VerificationResult::Success => {}
        other => panic!(
            "empty program not verified successfully, instead found {:?}",
            other
        ),
    }
}

fn process_program<F>(configure: F) -> VerificationResult
where
    F: FnOnce(&mut Program),
{
    let service =
        PrustiServerConnection::new(SERVER_ADDRESS.clone()).expect("Could not connect to server!");

    let mut program = Program {
        name: "dummy".to_string(),
        domains: vec![],
        fields: vec![],
        builtin_methods: vec![],
        methods: vec![],
        functions: vec![],
        viper_predicates: vec![],
    };
    configure(&mut program);

    let request = VerificationRequest {
        program,
        backend_config: Default::default(),
    };

    service.verify(request)
}
