use std::{thread, thread::JoinHandle};
use viper::*;

lazy_static::lazy_static! {
    static ref VIPER: Viper = Viper::new_for_tests();
}

/// Regression test for https://github.com/viperproject/silicon/issues/315
#[ignore] // Open issue: https://github.com/viperproject/silicon/issues/578
#[test]
fn concurrent_verifier_initialization() {
    env_logger::init();

    const MIN_NUM_THREADS: u32 = 2;
    const MAX_NUM_THREADS: u32 = 10;

    for iteration in 0..10 {
        println!("Iteration #{iteration}...");
        for num_threads in MIN_NUM_THREADS..(MAX_NUM_THREADS + 1) {
            let mut handlers: Vec<JoinHandle<()>> = vec![];

            for _ in 0..num_threads {
                handlers.push(thread::spawn(move || {
                    let verification_context: VerificationContext = VIPER.attach_current_thread();

                    let ast = verification_context.new_ast_factory();

                    let condition = ast.and(
                        ast.and(
                            ast.eq_cmp(
                                ast.empty_multiset(ast.int_type()),
                                ast.empty_multiset(ast.int_type()),
                            ),
                            ast.eq_cmp(
                                ast.explicit_set(
                                    &(0..10).map(|x| ast.int_lit(x)).collect::<Vec<Expr>>(),
                                ),
                                ast.explicit_set(
                                    &(0..10).map(|x| ast.int_lit(x)).collect::<Vec<Expr>>(),
                                ),
                            ),
                        ),
                        ast.eq_cmp(
                            ast.seq_take(
                                ast.explicit_seq(
                                    &(0..10).map(|x| ast.int_lit(x)).collect::<Vec<Expr>>(),
                                ),
                                ast.int_lit(3),
                            ),
                            ast.explicit_seq(
                                &(0..3).map(|x| ast.int_lit(x)).collect::<Vec<Expr>>(),
                            ),
                        ),
                    );

                    let assertion = ast.assert(condition, ast.no_position());

                    let body = ast.seqn(&[assertion], &[]);

                    let method = ast.method("foo", &[], &[], &[], &[], Some(body));

                    let program = ast.program(&[], &[], &[], &[], &[method]);

                    let mut verifier = verification_context
                        .new_verifier_with_default_smt_and_extra_args(
                            viper::VerificationBackend::Silicon,
                            vec!["--numberOfParallelVerifiers=1".to_string()],
                        );

                    let verification_result = verifier.verify(program);

                    assert!(verification_result.is_success());
                }));
            }

            for handler in handlers.drain(..) {
                handler.join().unwrap();
            }
        }
    }
}
