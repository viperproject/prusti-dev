#[derive(Clone, Copy)]
struct IntBox {
    val: i32
}

#[derive(Clone, Copy)]
enum Expr {
    Sum(IntBox, IntBox),
    Constant(IntBox)
}

fn compute(expr: Expr) -> i32 {
    let expr_depth = match expr {
        Expr::Sum(_, _) => 2,
        Expr::Constant(_) => 1
    };

    let simplified = match expr {
        Expr::Sum(a, b) => Expr::Constant(
            IntBox {
                val: a.val + b.val
            }
        ),
        x => x
    };

    let simplified_depth = match simplified {
        Expr::Sum(_, _) => 2,
        Expr::Constant(_) => 1
    };

    // Some invariants
    debug_assert!(simplified_depth <= expr_depth);
    debug_assert!(simplified_depth == 1);

    let value = match simplified {
        Expr::Sum(_, _) => {
            // We want to prove that this is never reached
            unreachable!()
        },
        Expr::Constant(IntBox { val }) => val
    };

    value
}

fn main() {}
