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
fn success_with_empty_program() {
    setup();

    let verification_context: VerificationContext = VIPER.attach_current_thread();

    let ast = verification_context.new_ast_factory();

    let program = ast.program(&[], &[], &[], &[], &[]);

    let mut verifier =
        verification_context.new_verifier_with_default_smt(viper::VerificationBackend::Silicon);

    let verification_result = verifier.verify(program);

    assert!(verification_result.is_success());
}

#[test]
fn failure_with_assert_false() {
    setup();

    let verification_context: VerificationContext = VIPER.attach_current_thread();
    let ast = verification_context.new_ast_factory();

    let false_lit = ast.false_lit();

    let pos = ast.identifier_position(0, 0, "pos-id:123");

    let assertion = ast.assert(false_lit, pos);

    let body = ast.seqn(&[assertion], &[]);

    let method = ast.method("foo", &[], &[], &[], &[], Some(body));

    let program = ast.program(&[], &[], &[], &[], &[method]);

    let mut verifier =
        verification_context.new_verifier_with_default_smt(viper::VerificationBackend::Silicon);

    let verification_result = verifier.verify(program);

    if let VerificationResult::Failure(errors) = verification_result {
        assert_eq!(errors.len(), 1);
        assert_eq!(
            errors[0].full_id,
            "assert.failed:assertion.false".to_string()
        );
        assert_eq!(errors[0].offending_pos_id, Some("pos-id:123".to_string()));
    } else {
        unreachable!()
    }
}

#[test]
fn success_with_assert_with_boolean_operations() {
    setup();

    let verification_context: VerificationContext = VIPER.attach_current_thread();
    let ast = verification_context.new_ast_factory();

    let true_lit = ast.true_lit();

    let false_lit = ast.false_lit();

    let and = ast.and(false_lit, true_lit);

    let or = ast.or(false_lit, true_lit);

    let implication = ast.implies(and, or);

    let pos = ast.no_position();

    let assertion = ast.assert(implication, pos);

    let body = ast.seqn(&[assertion], &[]);

    let method = ast.method("foo", &[], &[], &[], &[], Some(body));

    let program = ast.program(&[], &[], &[], &[], &[method]);

    let mut verifier =
        verification_context.new_verifier_with_default_smt(viper::VerificationBackend::Silicon);

    let verification_result = verifier.verify(program);

    assert!(verification_result.is_success());
}

#[test]
fn success_with_assert_false_in_dead_code() {
    setup();

    let verification_context: VerificationContext = VIPER.attach_current_thread();
    let ast = verification_context.new_ast_factory();

    let assert_false = ast.assert(ast.false_lit(), ast.no_position());
    let assert_true = ast.assert(ast.true_lit(), ast.no_position());

    let if_stmt = ast.if_stmt(
        ast.false_lit(),
        ast.seqn(&[assert_false], &[]),
        ast.seqn(&[assert_true], &[]),
    );

    let body = ast.seqn(&[if_stmt], &[]);

    let method = ast.method("foo", &[], &[], &[], &[], Some(body));

    let program = ast.program(&[], &[], &[], &[], &[method]);

    let mut verifier =
        verification_context.new_verifier_with_default_smt(viper::VerificationBackend::Silicon);

    let verification_result = verifier.verify(program);

    assert!(verification_result.is_success());
}

#[test]
fn success_with_assign_if_and_assert() {
    setup();

    let verification_context: VerificationContext = VIPER.attach_current_thread();
    let ast = verification_context.new_ast_factory();

    let local_var = ast.local_var("x", ast.bool_type());

    let assignment = ast.local_var_assign(local_var, ast.true_lit());

    let if_stmt = ast.if_stmt(
        local_var,
        ast.seqn(&[ast.assert(local_var, ast.no_position())], &[]),
        ast.seqn(&[ast.assert(ast.false_lit(), ast.no_position())], &[]),
    );

    let method_body = ast.seqn(
        &[assignment, if_stmt],
        &[ast.local_var_decl("x", ast.bool_type()).into()],
    );

    let method = ast.method("foo", &[], &[], &[], &[], Some(method_body));

    let program = ast.program(&[], &[], &[], &[], &[method]);

    let mut verifier =
        verification_context.new_verifier_with_default_smt(viper::VerificationBackend::Silicon);

    let verification_result = verifier.verify(program);

    assert!(verification_result.is_success());
}

#[test]
fn failure_with_assign_if_and_assert() {
    setup();

    let verification_context: VerificationContext = VIPER.attach_current_thread();
    let ast = verification_context.new_ast_factory();

    let local_var = ast.local_var("x", ast.bool_type());

    let assignment = ast.local_var_assign(local_var, ast.true_lit());

    let if_stmt = ast.if_stmt(
        local_var,
        ast.seqn(
            &[ast.assert(ast.false_lit(), ast.identifier_position(3, 0, "then"))],
            &[],
        ),
        ast.seqn(
            &[ast.assert(local_var, ast.identifier_position(5, 0, "else"))],
            &[],
        ),
    );

    let method_body = ast.seqn(
        &[assignment, if_stmt],
        &[ast.local_var_decl("x", ast.bool_type()).into()],
    );

    let method = ast.method("foo", &[], &[], &[], &[], Some(method_body));

    let program = ast.program(&[], &[], &[], &[], &[method]);

    let mut verifier =
        verification_context.new_verifier_with_default_smt(viper::VerificationBackend::Silicon);

    let verification_result = verifier.verify(program);

    if let VerificationResult::Failure(errors) = verification_result {
        assert_eq!(errors.len(), 1);
        assert_eq!(
            errors[0].full_id,
            "assert.failed:assertion.false".to_string()
        );
        assert_eq!(errors[0].offending_pos_id, Some("then".to_string()));
    } else {
        unreachable!()
    }
}

#[test]
fn success_with_complex_post_condition() {
    setup();

    let verification_context: VerificationContext = VIPER.attach_current_thread();
    let ast = verification_context.new_ast_factory();

    let condition = ast.and(
        ast.and(
            ast.eq_cmp(
                ast.empty_multiset(ast.int_type()),
                ast.empty_multiset(ast.int_type()),
            ),
            ast.eq_cmp(
                ast.explicit_set(&(0..10).map(|x| ast.int_lit(x)).collect::<Vec<Expr>>()),
                ast.explicit_set(&(0..10).map(|x| ast.int_lit(x)).collect::<Vec<Expr>>()),
            ),
        ),
        ast.eq_cmp(
            ast.seq_take(
                ast.explicit_seq(&(0..10).map(|x| ast.int_lit(x)).collect::<Vec<Expr>>()),
                ast.int_lit(3),
            ),
            ast.explicit_seq(&(0..3).map(|x| ast.int_lit(x)).collect::<Vec<Expr>>()),
        ),
    );

    let assertion = ast.assert(condition, ast.no_position());

    let body = ast.seqn(&[assertion], &[]);

    let method = ast.method("foo", &[], &[], &[], &[], Some(body));

    let program = ast.program(&[], &[], &[], &[], &[method]);

    let mut verifier =
        verification_context.new_verifier_with_default_smt(viper::VerificationBackend::Silicon);

    let verification_result = verifier.verify(program);

    assert!(verification_result.is_success());
}
