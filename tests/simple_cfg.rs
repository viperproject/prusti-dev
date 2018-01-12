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
fn success_with_single_chain() {
    setup();

    let verification_context: VerificationContext = VIPER.new_verification_context();
    let ast = verification_context.new_ast_factory();

    let mut cfg = verification_context.new_cfg_method(&ast, "foo", vec![], vec![], vec![ast.local_var_decl("a", ast.int_type())]);

    let local_var = ast.local_var("a", ast.int_type());

    // a = 1
    let block_1 = cfg.add_block(ast.local_var_assign(local_var, ast.int_lit(1)));

    // assert(a == 2)
    let block_2 = cfg.add_block(ast.assert(ast.eq_cmp(local_var, ast.int_lit(2)), ast.no_position()));

    // a = 2
    let block_3 = cfg.add_block(ast.local_var_assign(local_var, ast.int_lit(2)));

    cfg.set_successor(block_1, Successor::Goto(block_3));
    cfg.set_successor(block_3, Successor::Goto(block_2));

    let program = ast.program(vec![], vec![], vec![], vec![], vec![cfg.to_ast().ok().unwrap()]);

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
