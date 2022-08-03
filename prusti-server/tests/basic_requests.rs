use lazy_static::lazy_static;
use prusti_common::vir::*;
use prusti_server::{
    spawn_server_thread, tokio::runtime::Builder, PrustiClient, VerificationRequest,
    ViperBackendConfig,
};
use viper::VerificationResult;

lazy_static! {
    // only start the jvm & server once
    static ref SERVER_ADDRESS: String = spawn_server_thread().to_string();
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
    let client = PrustiClient::new(SERVER_ADDRESS.clone()).expect("Could not connect to server!");

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
        program: prusti_common::vir::program::Program::Legacy(program),
        backend_config: ViperBackendConfig::new(prusti_common::config::viper_backend()),
    };

    Builder::new_current_thread()
        .enable_all()
        .build()
        .expect("failed to construct Tokio runtime")
        .block_on(client.verify(request))
        .expect("Verification request failed")
}
