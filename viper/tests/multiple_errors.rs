use std::{sync::Once, vec};
use viper::*;

static INIT: Once = Once::new();

lazy_static::lazy_static! {
    static ref VIPER: Viper = Viper::new_for_tests();
}

/// Setup function that is only run once, even if called multiple times.
fn setup() {
    INIT.call_once(|| {
        env_logger::init();
    });
}

fn verify_multiple_errors(backend: viper::VerificationBackend, args: Vec<String>) {
    setup();

    let verification_context: VerificationContext = VIPER.attach_current_thread();
    let ast = verification_context.new_ast_factory();

    let pos_1 = ast.identifier_position(123, 0, "pos-id:123");
    let pos_1b = ast.identifier_position(1230, 0, "pos-id:1230");
    let assertion_1 = ast.assert(
        ast.eq_cmp_with_pos(ast.local_var("x", ast.int_type()), ast.int_lit(0), pos_1b),
        pos_1,
    );

    let havoc = ast.local_var_assign(
        ast.local_var("x", ast.int_type()),
        ast.local_var("v", ast.int_type()),
    );

    let pos_2 = ast.identifier_position(456, 0, "pos-id:456");
    let pos_2b = ast.identifier_position(4560, 0, "pos-id:4560");
    let assertion_2 = ast.assert(
        ast.eq_cmp_with_pos(ast.local_var("x", ast.int_type()), ast.int_lit(0), pos_2b),
        pos_2,
    );

    let body = ast.seqn(
        &[assertion_1, havoc, assertion_2],
        &[ast.local_var_decl("x", ast.int_type()).into()],
    );
    let method = ast.method(
        "foo",
        &[ast.local_var_decl("v", ast.int_type())],
        &[],
        &[],
        &[],
        Some(body),
    );
    let program = ast.program(&[], &[], &[], &[], &[method]);

    let mut verifier =
        verification_context.new_verifier_with_default_smt_and_extra_args(backend, args);

    let verification_result = verifier.verify(program);

    if let VerificationResult::Failure(errors) = verification_result {
        assert_eq!(errors.len(), 2);
        assert_eq!(
            errors[0].full_id,
            "assert.failed:assertion.false".to_string()
        );
        assert_eq!(
            errors[1].full_id,
            "assert.failed:assertion.false".to_string()
        );
        assert_eq!(errors[0].offending_pos_id, Some("pos-id:123".to_string()));
        assert_eq!(errors[1].offending_pos_id, Some("pos-id:456".to_string()));
    } else {
        unreachable!("{:?}", verification_result);
    }
}

#[test]
fn report_multiple_errors_with_silicon() {
    verify_multiple_errors(
        viper::VerificationBackend::Silicon,
        vec![
            "--logLevel=INFO".to_string(),
            "--numberOfErrorsToReport=0".to_string(),
        ],
    );
}
