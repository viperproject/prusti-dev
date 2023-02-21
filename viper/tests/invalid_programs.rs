use backend_common::VerificationResult;
use std::sync::Once;
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

#[test]
fn runtime_error() {
    setup();

    let verification_context: VerificationContext = VIPER.attach_current_thread();
    let ast = verification_context.new_ast_factory();

    // This is an error, as Silicon expects the method body to be a Seqn statement.
    let method_body = ast.assert(ast.true_lit(), ast.no_position());
    let method = ast.method("foo", &[], &[], &[], &[], Some(method_body));
    let program = ast.program(&[], &[], &[], &[], &[method]);

    let mut verifier =
        verification_context.new_verifier_with_default_smt(viper::VerificationBackend::Silicon);
    let verification_result = verifier.verify(program);

    assert!(matches!(
        verification_result,
        VerificationResult::JavaException(_)
    ));
}

#[test]
fn consistency_error() {
    test_consistency_error_for_method_body(|ast| {
        let local_var = ast.local_var("x", ast.bool_type());

        let assignment = ast.local_var_assign(local_var, ast.true_lit());

        let if_stmt = ast.if_stmt(
            local_var,
            ast.seqn(&[ast.assert(local_var, ast.no_position())], &[]),
            ast.seqn(&[ast.assert(ast.false_lit(), ast.no_position())], &[]),
        );

        ast.seqn(
            &[assignment, if_stmt],
            &[
                // consistency error: we omit the declaration of the local variable x
                // ast.local_var_decl("x", ast.bool_type())
            ],
        )
    });
}

#[test]
fn type_error() {
    test_consistency_error_for_method_body(|ast| {
        let local_var = ast.local_var("x", ast.int_type());

        let assignment = ast.local_var_assign(local_var, ast.true_lit()); // type error

        let if_stmt = ast.if_stmt(
            local_var,                                                  // type error
            ast.seqn(&[ast.assert(local_var, ast.no_position())], &[]), // type error
            ast.seqn(&[ast.assert(ast.false_lit(), ast.no_position())], &[]),
        );

        ast.seqn(
            &[assignment, if_stmt],
            &[ast.local_var_decl("x", ast.int_type()).into()],
        )
    });
}

fn test_consistency_error_for_method_body<F>(body_constructor: F)
where
    for<'v> F: FnOnce(&AstFactory<'v>) -> Stmt<'v>,
{
    setup();

    let verification_context: VerificationContext = VIPER.attach_current_thread();
    let ast = verification_context.new_ast_factory();

    let method_body = body_constructor(&ast);

    let method = ast.method("foo", &[], &[], &[], &[], Some(method_body));

    let program = ast.program(&[], &[], &[], &[], &[method]);

    let mut verifier =
        verification_context.new_verifier_with_default_smt(viper::VerificationBackend::Silicon);

    let verification_result = verifier.verify(program);
    match verification_result {
        VerificationResult::ConsistencyErrors(_) => (),
        other => panic!("consistency errors not identified, instead found {other:?}"),
    }
}
