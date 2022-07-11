use viper::*;

lazy_static::lazy_static! {
    static ref VIPER: Viper = Viper::new_for_tests();
}

#[test]
fn success_with_complex_program() {
    env_logger::init();

    let verification_context: VerificationContext = VIPER.attach_current_thread();
    let ast = verification_context.new_ast_factory();
    let ast_utils = verification_context.new_ast_utils();

    let method = ast.method(
        "foobar",
        &[ast.local_var_decl("arg", ast.int_type())],
        &[ast.local_var_decl("res", ast.int_type())],
        &[ast.false_lit()],
        &[ast.true_lit()],
        Some(ast.seqn(
            &[ast.local_var_assign(
                ast.local_var("res", ast.int_type()),
                ast.local_var("arg", ast.int_type()),
            )],
            &[],
        )),
    );

    let program = ast.program(&[], &[], &[], &[], &[method]);

    let pretty_printed = ast_utils.pretty_print(program);

    assert!(pretty_printed.contains("method foobar(arg: Int)"));
    assert!(pretty_printed.contains("returns (res: Int)"));
    assert!(pretty_printed.contains("requires false"));
    assert!(pretty_printed.contains("ensures true"));
    assert!(pretty_printed.contains("res := arg"));
}
