use std::fs::File;
use std::io::Write;

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
    let ast_utils = verification_context.new_ast_utils();



    let val_float = ast.field("val_float", ast.backend_f64_type());

    let pred = ast.predicate(
        "f64",
        &[ast.local_var_decl("self", ast.ref_type())],
         Some( ast.field_access_predicate(
             ast.field_access(ast.local_var("self", ast.ref_type()), ast.field("val_float", ast.backend_f64_type())),
             ast.full_perm()
    )));
    
    let id= ast.method(
        "foo",
        &[],
        &[ast.local_var_decl("_0", ast.ref_type())],
        &[],
        &[],
        Some(ast.seqn(
            &[
            ast.inhale(
                ast.predicate_access_predicate(
                        ast.predicate_access(
                            &[ast.local_var("_0", ast.ref_type())], 
                            "f64"),
                        ast.full_perm()
                ),
                ast.no_position()
            ),

            ast.field_assign(
            ast.field_access(ast.local_var("_0", ast.ref_type()), val_float),
            ast.backend_f64_lit(4591870180066957722)
            ),

            ast.fold(
                ast.predicate_access_predicate(
                    ast.predicate_access(&[ast.local_var("_0", ast.ref_type())], "f64"),
                    ast.full_perm()
                ),
            ),
            ast.exhale(
                ast.predicate_access_predicate(
                        ast.predicate_access(&[ast.local_var("_0", ast.ref_type())], "f64"),
                        ast.full_perm()
                ),
                ast.no_position()
            ),
            ], 
        &[]
        ))
        
    );


    let program = ast.program(
        &[],
        &[val_float],
        &[],
        &[pred],
        &[id],
    );

    let verifier = verification_context.new_verifier(viper::VerificationBackend::Silicon, None);
    let verification_result = verifier.verify(program);
    
    let pretty_printed = ast_utils.pretty_print(program);

    let mut w = File::create("./tmp/pretty-print.txt").unwrap();
    writeln!(&mut w, "{}", pretty_printed).unwrap();

    eprintln!("Pretty printed:\n{}", pretty_printed);

    assert_eq!(verification_result, VerificationResult::Success());
}