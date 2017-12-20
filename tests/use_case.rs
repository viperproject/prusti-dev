extern crate viper;
extern crate error_chain;

use viper::*;

#[test]
fn use_case() {
    let viper: Viper = Viper::new();

    let verification_context: VerificationContext = viper.new_verification_context();

    let ast_factory = verification_context.new_ast_factory();

    let program = ast_factory.new_program(vec![]);

    let error_manager = verification_context.new_error_manager();

    let verifier = verification_context.new_verifier();

    /*error_manager.register(/* ... */);
    error_manager.register(/* ... */);*/

    let verification_result = verifier.verify(program, error_manager);

    println!("Verification result: {:?}", verification_result);
}
