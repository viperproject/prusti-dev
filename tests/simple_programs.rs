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

    let program = ast.new_program(vec![], vec![], vec![], vec![], vec![]);

    let verifier = verification_context.new_verifier();

    let verification_result = verifier.verify(program);

    assert_eq!(verification_result, VerificationResult::Success());
}

#[test]
fn failure_with_assert_false() {
    setup();

    let verification_context: VerificationContext = VIPER.new_verification_context();
    let ast = verification_context.new_ast_factory();

    let false_lit = ast.new_false_lit();

    let pos = ast.new_identifier_position(0, 0, "pos-id:123");

    let assertion = ast.new_assert(false_lit, pos);

    let body = vec![assertion];

    let method = ast.new_method("foo", vec![], vec![], vec![], vec![], Some(body));

    let program = ast.new_program(vec![], vec![], vec![], vec![], vec![method]);

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

    let true_lit = ast.new_true_lit();

    let false_lit = ast.new_false_lit();

    let and = ast.new_and(false_lit.clone(), true_lit.clone());

    let or = ast.new_or(false_lit.clone(), true_lit.clone());

    let implication = ast.new_implies(and, or);

    let pos = ast.new_no_position();

    let assertion = ast.new_assert(implication, pos);

    let body = vec![assertion];

    let method = ast.new_method("foo", vec![], vec![], vec![], vec![], Some(body));

    let program = ast.new_program(vec![], vec![], vec![], vec![], vec![method]);

    let verifier = verification_context.new_verifier();

    let verification_result = verifier.verify(program);

    assert_eq!(verification_result, VerificationResult::Success());
}

#[test]
fn success_with_assert_false_in_dead_code() {
    setup();

    let verification_context: VerificationContext = VIPER.new_verification_context();
    let ast = verification_context.new_ast_factory();

    let assert_false = ast.new_assert(ast.new_false_lit(), ast.new_no_position());
    let assert_true = ast.new_assert(ast.new_true_lit(), ast.new_no_position());

    let if_stmt = ast.new_if(ast.new_false_lit(), vec![assert_false], vec![assert_true]);

    let body = vec![if_stmt];

    let method = ast.new_method("foo", vec![], vec![], vec![], vec![], Some(body));

    let program = ast.new_program(vec![], vec![], vec![], vec![], vec![method]);

    let verifier = verification_context.new_verifier();

    let verification_result = verifier.verify(program);

    assert_eq!(verification_result, VerificationResult::Success());
}

#[test]
fn success_with_assign_if_and_assert() {
    setup();

    let verification_context: VerificationContext = VIPER.new_verification_context();
    let ast = verification_context.new_ast_factory();

    let local_var = ast.new_local_var("x", ast.new_bool_type());

    let assignment = ast.new_local_var_assign(local_var.clone(), ast.new_true_lit());

    let if_stmt = ast.new_if(
        local_var.clone(),
        vec![ast.new_assert(local_var.clone(), ast.new_no_position())],
        vec![ast.new_assert(ast.new_false_lit(), ast.new_no_position())],
    );

    let method_body = vec![assignment, if_stmt];

    let method = ast.new_method("foo", vec![], vec![], vec![], vec![], Some(method_body));

    let program = ast.new_program(vec![], vec![], vec![], vec![], vec![method]);

    let verifier = verification_context.new_verifier();

    let verification_result = verifier.verify(program);

    assert_eq!(verification_result, VerificationResult::Success());
}

#[test]
fn failure_with_assign_if_and_assert() {
    setup();

    let verification_context: VerificationContext = VIPER.new_verification_context();
    let ast = verification_context.new_ast_factory();

    let local_var = ast.new_local_var("x", ast.new_bool_type());

    let assignment = ast.new_local_var_assign(local_var.clone(), ast.new_true_lit());

    let if_stmt =
        ast.new_if(
            local_var.clone(),
            vec![
                ast.new_assert(
                    ast.new_false_lit(),
                    ast.new_identifier_position(3, 0, "then")
                ),
            ],
            vec![
                ast.new_assert(local_var.clone(), ast.new_identifier_position(5, 0, "else")),
            ],
        );

    let method_body = vec![assignment, if_stmt];

    let method = ast.new_method("foo", vec![], vec![], vec![], vec![], Some(method_body));

    let program = ast.new_program(vec![], vec![], vec![], vec![], vec![method]);

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

    let condition = ast.new_and(
        ast.new_and(
            ast.new_eq_cmp(
                ast.new_empty_multi_set(ast.new_int_type()),
                ast.new_empty_multi_set(ast.new_int_type()),
            ),
            ast.new_eq_cmp(
                ast.new_explicit_set((0..10).map(|x| ast.new_int_lit(x)).collect()),
                ast.new_explicit_set((0..10).map(|x| ast.new_int_lit(x)).collect()),
            ),
        ),
        ast.new_eq_cmp(
            ast.new_seq_take(
                ast.new_explicit_seq((0..10).map(|x| ast.new_int_lit(x)).collect()),
                ast.new_int_lit(3),
            ),
            ast.new_explicit_seq((0..3).map(|x| ast.new_int_lit(x)).collect()),
        ),
    );

    let assertion = ast.new_assert(condition, ast.new_no_position());

    let body = vec![assertion];

    let method = ast.new_method("foo", vec![], vec![], vec![], vec![], Some(body));

    let program = ast.new_program(vec![], vec![], vec![], vec![], vec![method]);

    let verifier = verification_context.new_verifier();

    let verification_result = verifier.verify(program);

    assert_eq!(verification_result, VerificationResult::Success());
}
