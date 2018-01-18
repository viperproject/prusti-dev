extern crate env_logger;
extern crate error_chain;
#[macro_use]
extern crate lazy_static;
extern crate viper;

use std::sync::{Once, ONCE_INIT};
use viper::*;

static INIT: Once = ONCE_INIT;

lazy_static! {
    static ref VIPER: Viper = Viper::new();
}

/// Setup function that is only run once, even if called multiple times.
fn setup() {
    INIT.call_once(|| {
        env_logger::init().unwrap();
    });
}

#[test]
#[should_panic]
fn panic_on_consistency_error() {
    setup();

    let verification_context: VerificationContext = VIPER.new_verification_context();
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
        &[
            // consistency error: we omit the declaration of the local variable x
            // ast.local_var_decl("x", ast.bool_type())
        ],
    );

    let method = ast.method("foo", &[], &[], &[], &[], Some(method_body));

    let program = ast.program(&[], &[], &[], &[], &[method]);

    let verifier = verification_context.new_verifier();

    let _verification_result = verifier.verify(program);
}

#[test]
#[should_panic]
fn panic_on_type_error() {
    setup();

    let verification_context: VerificationContext = VIPER.new_verification_context();
    let ast = verification_context.new_ast_factory();

    let local_var = ast.local_var("x", ast.int_type());

    let assignment = ast.local_var_assign(local_var, ast.true_lit()); // type error

    let if_stmt = ast.if_stmt(
        local_var,                                                  // type error
        ast.seqn(&[ast.assert(local_var, ast.no_position())], &[]), // type error
        ast.seqn(&[ast.assert(ast.false_lit(), ast.no_position())], &[]),
    );

    let method_body = ast.seqn(
        &[assignment, if_stmt],
        &[ast.local_var_decl("x", ast.int_type()).into()],
    );

    let method = ast.method("foo", &[], &[], &[], &[], Some(method_body));

    let program = ast.program(&[], &[], &[], &[], &[method]);

    let verifier = verification_context.new_verifier();

    let _verification_result = verifier.verify(program);
}
