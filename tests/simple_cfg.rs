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
fn success_with_simple_chain() {
    setup();

    let verification_context: VerificationContext = VIPER.new_verification_context();
    let ast = verification_context.new_ast_factory();
    let cfg_factory = verification_context.new_cfg_factory();

    let mut cfg = cfg_factory.new_cfg_method(
        "foo",
        vec![],
        vec![],
        vec![ast.local_var_decl("a", ast.int_type())],
    );

    let local_var = ast.local_var("a", ast.int_type());

    // a = 1
    let block_1 = cfg.add_block(
        "_1",
        vec![],
        vec![ast.local_var_assign(local_var, ast.int_lit(1))]
    );

    // assert(a == 2)
    let block_2 = cfg.add_block(
        "_2",
        vec![],
        vec![ast.assert(ast.eq_cmp(local_var, ast.int_lit(2)), ast.no_position())],
    );

    // a = 2
    let block_3 = cfg.add_block(
        "_3",
        vec![],
        vec![ast.local_var_assign(local_var, ast.int_lit(2))]
    );

    cfg.set_successor(block_1, Successor::Goto(block_3));
    cfg.set_successor(block_2, Successor::Return);
    cfg.set_successor(block_3, Successor::Goto(block_2));

    let program = ast.program(&[], &[], &[], &[], &[cfg.to_ast().ok().unwrap()]);

    let verifier = verification_context.new_verifier();

    let verification_result = verifier.verify(program);

    assert_eq!(verification_result, VerificationResult::Success());
}

#[test]
fn success_with_simple_loop() {
    setup();

    let verification_context: VerificationContext = VIPER.new_verification_context();
    let ast = verification_context.new_ast_factory();
    let cfg_factory = verification_context.new_cfg_factory();

    let mut cfg = cfg_factory.new_cfg_method(
        "foo",
        vec![],
        vec![],
        vec![ast.local_var_decl("a", ast.int_type())],
    );

    let local_var = ast.local_var("a", ast.int_type());

    // a = 0
    let block_1 = cfg.add_block(
        "_1",
        vec![],
        vec![ast.local_var_assign(local_var, ast.int_lit(0))]);

    // invariant a <= 10
    // skip
    let block_2 = cfg.add_block(
        "_2",
        vec![ast.le_cmp(local_var, ast.int_lit(10))],
        vec![],
    );

    // a = a + 1
    let block_3 = cfg.add_block(
        "_3",
        vec![],
        vec![ast.local_var_assign(local_var, ast.add(local_var, ast.int_lit(1)))],
    );

    // assert(a == 10)
    let block_4 = cfg.add_block(
        "_4",
        vec![],
        vec![ast.assert(ast.eq_cmp(local_var, ast.int_lit(10)), ast.no_position())],
    );

    cfg.set_successor(block_1, Successor::Goto(block_2));
    cfg.set_successor(
        block_2,
        Successor::GotoIf(ast.lt_cmp(local_var, ast.int_lit(10)), block_3, block_4),
    );
    cfg.set_successor(block_3, Successor::Goto(block_2));
    cfg.set_successor(block_4, Successor::Return);

    let program = ast.program(&[], &[], &[], &[], &[cfg.to_ast().ok().unwrap()]);

    let verifier = verification_context.new_verifier();

    let verification_result = verifier.verify(program);

    assert_eq!(verification_result, VerificationResult::Success());
}
