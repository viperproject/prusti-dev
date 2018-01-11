#[macro_use]
extern crate bencher;
#[macro_use]
extern crate lazy_static;
extern crate viper;

use bencher::Bencher;
use viper::*;

lazy_static! {
    static ref VIPER: Viper = Viper::new();
}

benchmark_main!(ast_factory);
benchmark_group!(ast_factory, build_program);

fn build_program(bench: &mut Bencher) {
    let verification_context: VerificationContext = VIPER.new_verification_context();
    let ast = verification_context.new_ast_factory();

    bench.iter(move || {
        let wrap_domain_function = ast.domain_func(
            "wrap",
            vec![ast.local_var_decl("x", ast.type_var("T"))],
            ast.domain_type(
                "Wrapper",
                vec![(ast.type_var("T"), ast.type_var("T"))],
                vec![ast.type_var("T")],
            ),
            false,
            "Wrapper",
        );

        let unwrap_domain_function = ast.domain_func(
            "unwrap",
            vec![
                ast.local_var_decl(
                    "x",
                    ast.domain_type(
                        "Wrapper",
                        vec![(ast.type_var("T"), ast.type_var("T"))],
                        vec![ast.type_var("T")],
                    )
                ),
            ],
            ast.type_var("T"),
            false,
            "Wrapper",
        );

        let wrapper_domain = ast.domain(
            "Wrapper",
            vec![wrap_domain_function, unwrap_domain_function],
            vec![
                ast.domain_axiom(
                    "unwrap_wrapper",
                    // forall x: T :: unwrap(wrap(x)) == x
                    ast.forall(
                        vec![ast.local_var_decl("x", ast.type_var("T"))],
                        vec![],
                        ast.eq_cmp(
                            ast.domain_func_app(
                                unwrap_domain_function,
                                vec![
                                    ast.domain_func_app(
                                        wrap_domain_function,
                                        vec![ast.local_var("x", ast.type_var("T"))],
                                        vec![(ast.type_var("T"), ast.type_var("T"))]
                                    ),
                                ],
                                vec![(ast.type_var("T"), ast.type_var("T"))],
                            ),
                            ast.local_var("x", ast.type_var("T")),
                        ),
                    ),
                    "Wrapper"
                ),
            ],
            vec![ast.type_var("T")],
        );

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
                        even_function,
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

        let method = ast.method(
            "build_even_num_box",
            vec![ast.local_var_decl("v", ast.int_type())],
            vec![ast.local_var_decl("box", ast.ref_type())],
            vec![
                // even(v)
                ast.func_app(even_function, vec![ast.local_var("v", ast.int_type())]),
            ],
            vec![
                // EvenNumBox(box)
                ast.predicate_access_predicate(
                    ast.predicate_access(
                        vec![ast.local_var("box", ast.ref_type())],
                        "EvenNumBox",
                    ),
                    ast.full_perm()
                ),
            ],
            Some(ast.seqn(
                vec![
                    // box = new(value)
                    ast.new_stmt(
                        ast.local_var("box", ast.ref_type()),
                        vec![ast.field("value", ast.int_type())]
                    ),
                    // box.value = unwrap(wrap(v))
                    ast.field_assign(
                        ast.field_access(
                            ast.local_var("box", ast.ref_type()),
                            ast.field("value", ast.int_type()),
                        ),
                        ast.domain_func_app(
                            unwrap_domain_function,
                            vec![
                                ast.domain_func_app(
                                    wrap_domain_function,
                                    vec![ast.local_var("v", ast.int_type())],
                                    vec![
                                        (ast.type_var("T"), ast.int_type()),
                                    ]
                                ),
                            ],
                            vec![(ast.type_var("T"), ast.int_type())],
                        )
                    ),
                    // fold EvenNumBox(box)
                    ast.fold(ast.predicate_access_predicate(
                        ast.predicate_access(
                            vec![ast.local_var("box", ast.ref_type())],
                            "EvenNumBox",
                        ),
                        ast.full_perm(),
                    )),
                ],
                vec![],
            )),
        );

        ast.program(
            vec![wrapper_domain],
            vec![value_field],
            vec![even_function],
            vec![even_num_box_predicate],
            vec![method],
        )
    });
}
