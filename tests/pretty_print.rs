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
fn success_with_complex_program() {
    env_logger::init().unwrap();

    let verification_context: VerificationContext = VIPER.new_verification_context();
    let ast = verification_context.new_ast_factory();
    let ast_utils = verification_context.new_ast_utils();

    let method = ast.method(
        "foobar",
        vec![ast.local_var_decl("arg", ast.int_type())],
        vec![ast.local_var_decl("res", ast.int_type())],
        vec![ast.false_lit()],
        vec![ast.true_lit()],
        Some(ast.seqn(
            vec![
                ast.local_var_assign(
                    ast.local_var("res", ast.int_type()),
                    ast.local_var("arg", ast.int_type()),
                ),
            ],
            vec![],
        )),
    );

    let program = ast.program(vec![], vec![], vec![], vec![], vec![method]);

    let pretty_printed = ast_utils.pretty_print(program);

    assert!(pretty_printed.contains("method foobar(arg: Int)"));
    assert!(pretty_printed.contains("returns (res: Int)"));
    assert!(pretty_printed.contains("requires false"));
    assert!(pretty_printed.contains("ensures true"));
    assert!(pretty_printed.contains("res := arg"));
}
