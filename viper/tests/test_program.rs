extern crate env_logger;
extern crate error_chain;
#[macro_use]
extern crate lazy_static;
extern crate viper;

use viper::*;

lazy_static! {
    static ref VIPER: Viper = Viper::new();
}

#[test]
fn test_program() {
    env_logger::init();

    
    let verification_context: VerificationContext = VIPER.new_verification_context();
    let ast = verification_context.new_ast_factory();

    let foo= ast.function(
        "foo",
        &[],
        ast.backend_f64_type(),
        &[],
        &[],
        ast.no_position(),
        Some(
            ast.backend_f64_lit(4591870180066957722),
        )
    );


    let program = ast.program(
        &[],
        &[],
        &[foo],
        &[],
        &[],
    );

    let verifier = verification_context.new_verifier(viper::VerificationBackend::Silicon, None);
    let verification_result = verifier.verify(program);

    assert_eq!(verification_result, VerificationResult::Success());
}