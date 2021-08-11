extern crate env_logger;
extern crate error_chain;
#[macro_use]
extern crate lazy_static;
extern crate viper;

use std::thread;
use std::thread::JoinHandle;
use viper::*;

lazy_static! {
    static ref VIPER: Viper = Viper::new();
}

/// Regression test for the following bug:
/// <https://bitbucket.org/viperproject/silicon/issues/315/exception-while-building-silicon-instances>
#[ignore] // Ignored because Prusti doesn't need to concurrently verify programs
#[test]
fn concurrent_verifier_initialization() {
    env_logger::init();

    const MIN_NUM_THREADS: u32 = 2;
    const MAX_NUM_THREADS: u32 = 10;

    for iteration in 0..100 {
        println!("Iteration #{}...", iteration);
        for num_threads in MIN_NUM_THREADS..(MAX_NUM_THREADS + 1) {
            let mut handlers: Vec<JoinHandle<()>> = vec![];

            for _ in 0..num_threads {
                handlers.push(thread::spawn(move || {
                    let verification_context: VerificationContext = VIPER.new_verification_context();

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
                            ast.explicit_seq(&(0..3).map(|x| ast.int_lit(x)).collect::<Vec<Expr>>()),
                        ),
                    );

                    let assertion = ast.assert(condition, ast.no_position());

                    let body = ast.seqn(&[assertion], &[]);

                    let method = ast.method("foo", &[], &[], &[], &[], Some(body));

                    let program = ast.program(&[], &[], &[], &[], &[method]);

                    let verifier =
                        verification_context.new_verifier(viper::VerificationBackend::Silicon, None);

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
