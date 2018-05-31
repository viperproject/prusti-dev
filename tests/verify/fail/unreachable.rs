// error-pattern:

#![feature(nll)]

extern crate prusti_contracts;

struct IntBox {
    val: i32
}

enum Expr {
    Sum(IntBox, IntBox),
    Constant(IntBox)
}

fn compute(expr: Expr) -> i32 {
    let simplified = match expr {
        Expr::Sum(a, b) => Expr::Sum(b, a),
        x => x
    };

    let value = match simplified {
        Expr::Sum(_, _) => {
            // This must fail
            unreachable!()
        },
        Expr::Constant(IntBox { val }) => val
    };

    value
}

fn main() {}
