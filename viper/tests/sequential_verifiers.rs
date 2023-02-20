use viper::*;

lazy_static::lazy_static! {
    static ref VIPER: Viper = Viper::new_for_tests();
}

#[test]
fn sequential_verifier_initialization() {
    env_logger::init();

    for iteration in 0..5 {
        println!("Iteration #{iteration}...");
        let verification_context: VerificationContext = VIPER.attach_current_thread();

        let ast = verification_context.new_ast_factory();

        let condition = ast.and(
            ast.and(
                ast.eq_cmp(
                    ast.empty_multiset(ast.int_type()),
                    ast.empty_multiset(ast.int_type()),
                ),
                ast.eq_cmp(
                    ast.explicit_set(&(0..10).map(|x| ast.int_lit(x)).collect::<Vec<Expr>>()),
                    ast.explicit_set(&(0..10).map(|x| ast.int_lit(x)).collect::<Vec<Expr>>()),
                ),
            ),
            ast.eq_cmp(
                ast.seq_take(
                    ast.explicit_seq(&(0..10).map(|x| ast.int_lit(x)).collect::<Vec<Expr>>()),
                    ast.int_lit(3),
                ),
                ast.explicit_seq(&(0..3).map(|x| ast.int_lit(x)).collect::<Vec<Expr>>()),
            ),
        );

        let assertion = ast.assert(condition, ast.no_position());

        let body = ast.seqn(&[assertion], &[]);

        let method = ast.method("foo", &[], &[], &[], &[], Some(body));

        let program = ast.program(&[], &[], &[], &[], &[method]);

        let mut verifier =
            verification_context.new_verifier_with_default_smt(viper::VerificationBackend::Silicon);

        let verification_result = verifier.verify(program);

        assert!(verification_result.is_success());
    }
}
