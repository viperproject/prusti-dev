#[macro_use]
extern crate lazy_static;
extern crate viper;
extern crate error_chain;
extern crate env_logger;

use std::sync::{Once, ONCE_INIT};
use viper::*;

static INIT: Once = ONCE_INIT;

lazy_static! {
    static ref VIPER: Viper = Viper::new();
}

/// Setup function that is only run once, even if called multiple times.
fn setup() {
    INIT.call_once(|| { env_logger::init().unwrap(); });
}

#[test]
fn success_with_empty_program() {
    setup();

    let verification_context: VerificationContext = VIPER.new_verification_context();

    let ast = verification_context.new_ast_factory();

    let program = ast.program(vec![], vec![], vec![], vec![], vec![]);

    let verifier = verification_context.new_verifier();

    let verification_result = verifier.verify(program);

    assert_eq!(verification_result, VerificationResult::Success());
}

#[test]
fn failure_with_assert_false() {
    setup();

    let verification_context: VerificationContext = VIPER.new_verification_context();
    let ast = verification_context.new_ast_factory();

    let false_lit = ast.false_lit();

    let pos = ast.identifier_position(0, 0, "pos-id:123");

    let assertion = ast.assert(false_lit, pos);

    let body = vec![assertion];

    let method = ast.method("foo", vec![], vec![], vec![], vec![], Some(body));

    let program = ast.program(vec![], vec![], vec![], vec![], vec![method]);

    let verifier = verification_context.new_verifier();

    let verification_result = verifier.verify(program);

    assert_eq!(
        verification_result,
        VerificationResult::Failure(vec![
            VerificationError::new(
                "assert.failed".to_owned(),
                "pos-id:123".to_owned()
            ),
        ])
    );
}

#[test]
fn success_with_assert_with_boolean_operations() {
    setup();

    let verification_context: VerificationContext = VIPER.new_verification_context();
    let ast = verification_context.new_ast_factory();

    let true_lit = ast.true_lit();

    let false_lit = ast.false_lit();

    let and = ast.and(false_lit.clone(), true_lit.clone());

    let or = ast.or(false_lit.clone(), true_lit.clone());

    let implication = ast.implies(and, or);

    let pos = ast.no_position();

    let assertion = ast.assert(implication, pos);

    let body = vec![assertion];

    let method = ast.method("foo", vec![], vec![], vec![], vec![], Some(body));

    let program = ast.program(vec![], vec![], vec![], vec![], vec![method]);

    let verifier = verification_context.new_verifier();

    let verification_result = verifier.verify(program);

    assert_eq!(verification_result, VerificationResult::Success());
}

#[test]
fn success_with_assert_false_in_dead_code() {
    setup();

    let verification_context: VerificationContext = VIPER.new_verification_context();
    let ast = verification_context.new_ast_factory();

    let assert_false = ast.assert(ast.false_lit(), ast.no_position());
    let assert_true = ast.assert(ast.true_lit(), ast.no_position());

    let if_stmt = ast.if_stmt(ast.false_lit(), vec![assert_false], vec![assert_true]);

    let body = vec![if_stmt];

    let method = ast.method("foo", vec![], vec![], vec![], vec![], Some(body));

    let program = ast.program(vec![], vec![], vec![], vec![], vec![method]);

    let verifier = verification_context.new_verifier();

    let verification_result = verifier.verify(program);

    assert_eq!(verification_result, VerificationResult::Success());
}

#[test]
fn success_with_assign_if_and_assert() {
    setup();

    let verification_context: VerificationContext = VIPER.new_verification_context();
    let ast = verification_context.new_ast_factory();

    let local_var = ast.local_var("x", ast.bool_type());

    let assignment = ast.local_var_assign(local_var.clone(), ast.true_lit());

    let if_stmt = ast.if_stmt(
        local_var.clone(),
        vec![ast.assert(local_var.clone(), ast.no_position())],
        vec![ast.assert(ast.false_lit(), ast.no_position())],
    );

    let method_body = vec![assignment, if_stmt];

    let method = ast.method("foo", vec![], vec![], vec![], vec![], Some(method_body));

    let program = ast.program(vec![], vec![], vec![], vec![], vec![method]);

    let verifier = verification_context.new_verifier();

    let verification_result = verifier.verify(program);

    assert_eq!(verification_result, VerificationResult::Success());
}

#[test]
fn failure_with_assign_if_and_assert() {
    setup();

    let verification_context: VerificationContext = VIPER.new_verification_context();
    let ast = verification_context.new_ast_factory();

    let local_var = ast.local_var("x", ast.bool_type());

    let assignment = ast.local_var_assign(local_var.clone(), ast.true_lit());

    let if_stmt = ast.if_stmt(
        local_var.clone(),
        vec![
            ast.assert(ast.false_lit(), ast.identifier_position(3, 0, "then")),
        ],
        vec![
            ast.assert(local_var.clone(), ast.identifier_position(5, 0, "else")),
        ],
    );

    let method_body = vec![assignment, if_stmt];

    let method = ast.method("foo", vec![], vec![], vec![], vec![], Some(method_body));

    let program = ast.program(vec![], vec![], vec![], vec![], vec![method]);

    let verifier = verification_context.new_verifier();

    let verification_result = verifier.verify(program);

    assert_eq!(
        verification_result,
        VerificationResult::Failure(vec![
            VerificationError::new(
                "assert.failed".to_owned(),
                "then".to_owned()
            ),
        ])
    );
}


#[test]
fn success_with_complex_post_condition() {
    setup();

    let verification_context: VerificationContext = VIPER.new_verification_context();
    let ast = verification_context.new_ast_factory();

    let condition = ast.and(
        ast.and(
            ast.eq_cmp(
                ast.empty_multi_set(ast.int_type()),
                ast.empty_multi_set(ast.int_type()),
            ),
            ast.eq_cmp(
                ast.explicit_set((0..10).map(|x| ast.int_lit(x)).collect()),
                ast.explicit_set((0..10).map(|x| ast.int_lit(x)).collect()),
            ),
        ),
        ast.eq_cmp(
            ast.seq_take(
                ast.explicit_seq((0..10).map(|x| ast.int_lit(x)).collect()),
                ast.int_lit(3),
            ),
            ast.explicit_seq((0..3).map(|x| ast.int_lit(x)).collect()),
        ),
    );

    let assertion = ast.assert(condition, ast.no_position());

    let body = vec![assertion];

    let method = ast.method("foo", vec![], vec![], vec![], vec![], Some(body));

    let program = ast.program(vec![], vec![], vec![], vec![], vec![method]);

    let verifier = verification_context.new_verifier();

    let verification_result = verifier.verify(program);

    assert_eq!(verification_result, VerificationResult::Success());
}
