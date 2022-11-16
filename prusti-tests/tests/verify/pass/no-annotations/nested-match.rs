enum Num {
    Integer(i32),
    Rational(i32, i32),
}

enum Expr {
    Sum(Num, Num),
    Diff(Num, Num),
    Constant(Num)
}

fn check(expr: Expr) -> bool {
    let result = match expr {
        Expr::Sum(left, right) |
        Expr::Diff(left, right) => {
            match left {
                Num::Integer(_) => match right {
                    Num::Integer(_) => true,
                    _ => false,
                },
                Num::Rational(_, left_den) => match right {
                    Num::Rational(_, right_den) => left_den != 0 && right_den != 0,
                    _ => false,
                }
            }
        }
        Expr::Constant(Num::Integer(_)) => true,
        Expr::Constant(Num::Rational(_, den)) => den != 0
    };

    result
}

fn main() {}
