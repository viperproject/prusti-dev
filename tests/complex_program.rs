#[macro_use]
extern crate lazy_static;
extern crate viper;
extern crate error_chain;
extern crate env_logger;

use viper::*;

lazy_static! {
    static ref VIPER: Viper = Viper::new();
}

#[test]
fn success_with_complex_program() {
    env_logger::init().unwrap();

    let verification_context: VerificationContext = VIPER.new_verification_context();
    let ast = verification_context.new_ast_factory();

    // TODO: add some type parameters, functions, and axioms to this domain
    let empty_domain = ast.domain("D0", vec![], vec![], vec![]);

    let value_field = ast.field("value", ast.int_type());

    let even_function = ast.function(
        "even",
        vec![ast.local_var_decl("v", ast.int_type())],
        ast.bool_type(),
        vec![],
        vec![],
        Some(
            // x % 2 == 0
            ast.eq_cmp(
                ast.module(ast.local_var("v", ast.int_type()), ast.int_lit(2)),
                ast.int_lit(0),
            ),
        ),
    );

    let even_num_box_predicate = ast.predicate(
        "EvenNumBox",
        vec![ast.local_var_decl("box", ast.ref_type())],
        Some(
            // acc(box.value) && even(box.value)
            ast.and(
                ast.field_access_predicate(
                    ast.field_access(
                        ast.local_var("box", ast.ref_type()),
                        ast.field("value", ast.int_type()),
                    ),
                    ast.full_perm(),
                ),
                ast.func_app(
                    &even_function,
                    vec![
                        ast.field_access(
                            ast.local_var("box", ast.ref_type()),
                            ast.field("value", ast.int_type())
                        ),
                    ],
                ),
            ),
        ),
    );

    let method =
        ast.method(
            "build_even_num_box",
            vec![ast.local_var_decl("v", ast.int_type())],
            vec![ast.local_var_decl("box", ast.ref_type())],
            vec![
                // even(v)
                ast.func_app(&even_function, vec![ast.local_var("v", ast.int_type())]),
            ],
            vec![
                // EvenNumBox(box)
                ast.predicate_access_predicate(
                    ast.predicate_access(vec![ast.local_var("box", ast.ref_type())], "EvenNumBox"),
                    ast.full_perm()
                ),
            ],
            Some(vec![
                // box = new(value)
                ast.new_stmt(
                    ast.local_var("box", ast.ref_type()),
                    vec![ast.field("value", ast.int_type())]
                ),
                // box.value = v
                ast.field_assign(
                    ast.field_access(
                        ast.local_var("box", ast.ref_type()),
                        ast.field("value", ast.int_type()),
                    ),
                    ast.local_var("v", ast.int_type())
                ),
                // fold EvenNumBox(box)
                ast.fold(ast.predicate_access_predicate(
                    ast.predicate_access(
                        vec![ast.local_var("box", ast.ref_type())],
                        "EvenNumBox",
                    ),
                    ast.full_perm(),
                )),
            ]),
        );

    let program = ast.program(
        vec![empty_domain],
        vec![value_field],
        vec![even_function],
        vec![even_num_box_predicate],
        vec![method],
    );

    let verifier = verification_context.new_verifier();

    let verification_result = verifier.verify(program);

    assert_eq!(verification_result, VerificationResult::Success());
}
