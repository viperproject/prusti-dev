struct IntBox {
    val: i32
}

enum Expr {
    Sum(IntBox, IntBox),
    Constant(IntBox)
}

fn compute(expr: Expr) -> i32 {
    let simplified = match expr {
        Expr::Sum(a, b) => Expr::Constant(
            IntBox {
                val: a.val + b.val
            }
        ),
        x => x
    };

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
