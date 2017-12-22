#[macro_use]
extern crate lazy_static;
extern crate viper;
extern crate error_chain;

use viper::*;

lazy_static! {
    static ref VIPER: Viper = Viper::new();
}

#[test]
fn empty_program() {
    let verification_context: VerificationContext = VIPER.new_verification_context();

    let ast_factory = verification_context.new_ast_factory();

    let program = ast_factory.new_program(vec![]);

    let error_manager = verification_context.new_error_manager();

    let verifier = verification_context.new_verifier();

    /* TODO:
    error_manager.register(/* ... */);
    error_manager.register(/* ... */);
    */

    let verification_result = verifier.verify(program, error_manager);

    println!("Verification result: {:?}", verification_result);
}

#[test]
fn assert_false() {
    let verification_context: VerificationContext = VIPER.new_verification_context();

    let ast_factory = verification_context.new_ast_factory();

    let false_lit = ast_factory.new_false_lit();

    let assertion = ast_factory.new_assert(&false_lit);

    let seqn = ast_factory.new_seqn(vec![&assertion]);

    let method = ast_factory.new_method("foo", Some(&seqn), vec![], vec![]);

    let program = ast_factory.new_program(vec![&method]);

    let error_manager = verification_context.new_error_manager();

    let verifier = verification_context.new_verifier();

    /* TODO:
    error_manager.register(/* ... */);
    error_manager.register(/* ... */);
    */

    let verification_result = verifier.verify(program, error_manager);

    println!("Verification result: {:?}", verification_result);
}
