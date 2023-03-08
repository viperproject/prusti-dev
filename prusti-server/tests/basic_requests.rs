use futures_util::stream::StreamExt;
use lazy_static::lazy_static;
use prusti_common::vir::*;
use prusti_server::{
    spawn_server_thread, tokio::runtime::Builder, PrustiClient, ServerMessage, VerificationRequest,
    ViperBackendConfig,
};
use viper::VerificationResultKind;

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
        VerificationResultKind::ConsistencyErrors(errors) => assert_eq!(errors.len(), 1),
        other => panic!("consistency errors not identified, instead found {other:?}"),
    }
}

#[test]
fn empty_program() {
    let result = process_program(|_| ());

    match result {
        VerificationResultKind::Success => {}
        other => panic!("empty program not verified successfully, instead found {other:?}"),
    }
}

fn process_program<F>(configure: F) -> VerificationResultKind
where
    F: FnOnce(&mut Program),
{
    let mut program = Program {
        name: "dummy".to_string(),
        backend_types: vec![],
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
        backend_config: ViperBackendConfig::new(
            prusti_common::config::viper_backend().parse().unwrap(),
        ),
    };

    Builder::new_current_thread()
        .enable_all()
        .build()
        .expect("failed to construct Tokio runtime")
        .block_on(async {
            PrustiClient::verify(SERVER_ADDRESS.clone(), request)
                .await
                .collect::<Vec<ServerMessage>>()
                .await
                .into_iter()
                .find_map(|m| match m {
                    ServerMessage::Termination(res) => Some(res.kind),
                    _ => None,
                })
                .unwrap_or_else(|| VerificationResultKind::Failure(vec![]))
        })
}
