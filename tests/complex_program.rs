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
    let empty_domain = ast.new_domain("D0", vec![], vec![], vec![]);

    let value_field = ast.new_field("value", ast.new_int_type());

    let even_function = ast.new_function(
        "even",
        vec![ast.new_local_var_decl("v", ast.new_int_type())],
        ast.new_bool_type(),
        vec![],
        vec![],
        Some(
            // x % 2 == 0
            ast.new_eq_cmp(
                ast.new_mod(
                    ast.new_local_var("v", ast.new_int_type()),
                    ast.new_int_lit(2),
                ),
                ast.new_int_lit(0),
            ),
        ),
    );

    let even_num_box_predicate = ast.new_predicate(
        "EvenNumBox",
        vec![ast.new_local_var_decl("box", ast.new_ref_type())],
        Some(
            // acc(box.value) && even(box.value)
            ast.new_and(
                ast.new_perm_ge_cmp(
                    ast.new_current_perm(ast.new_field_access(
                        ast.new_local_var("box", ast.new_ref_type()),
                        ast.new_field("value", ast.new_int_type()),
                    )),
                    ast.new_full_perm(),
                ),
                ast.new_func_app(
                    &even_function,
                    vec![
                        ast.new_field_access(
                            ast.new_local_var("box", ast.new_ref_type()),
                            ast.new_field("value", ast.new_int_type())
                        ),
                    ],
                ),
            ),
        ),
    );

    let method = ast.new_method(
        "build_even_num_box",
        vec![ast.new_local_var_decl("v", ast.new_int_type())],
        vec![ast.new_local_var_decl("box", ast.new_ref_type())],
        vec![
            // even(v)
            ast.new_func_app(
                &even_function,
                vec![ast.new_local_var("v", ast.new_int_type())]
            ),
        ],
        vec![
            // EvenNumBox(box)
            ast.new_predicate_access_predicate(
                ast.new_predicate_access(
                    vec![ast.new_local_var("box", ast.new_ref_type())],
                    "EvenNumBox",
                ),
                ast.new_full_perm()
            ),
        ],
        Some(vec![
            // box = new(value)
            ast.new_new_stmt(
                ast.new_local_var("box", ast.new_ref_type()),
                vec![ast.new_field("value", ast.new_int_type())]
            ),
            // box.value = v
            ast.new_field_assign(
                ast.new_field_access(
                    ast.new_local_var("box", ast.new_ref_type()),
                    ast.new_field("value", ast.new_int_type()),
                ),
                ast.new_local_var("v", ast.new_int_type())
            ),
            // fold EvenNumBox(box)
            ast.new_fold(ast.new_predicate_access_predicate(
                ast.new_predicate_access(
                    vec![
                        ast.new_local_var(
                            "box",
                            ast.new_ref_type()
                        ),
                    ],
                    "EvenNumBox",
                ),
                ast.new_full_perm(),
            )),
        ]),
    );

    let program = ast.new_program(
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
