extern crate prusti_common;
extern crate prusti_server;
extern crate viper;

use prusti_common::{
    verification_service::{VerificationRequest, VerificationService},
    vir::*,
};
use prusti_server::{PrustiServerConnection, ServerSideService};
use viper::VerificationResult;

#[test]
fn consistency_error() {
    let result = process_program(|program| {
        program.fields.push(Field {
            name: "field".to_string(), // reserved identifier
            typ: Type::Int,
        });
    });

    match result {
        VerificationResult::ConsistencyErrors(errors) => println!("errors: {:?}", errors),
        other => panic!(
            "consistency errors not identified, instead found {:?}",
            other
        ),
    }
}

fn process_program<F>(configure: F) -> VerificationResult
where
    F: FnOnce(&mut Program),
{
    let server_address = ServerSideService::spawn_off_thread();
    let service = PrustiServerConnection::new(server_address);

    let mut program = Program {
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
        program_name: "dummy".to_string(),
        backend_config: Default::default(),
    };

    service.verify(request)
}
