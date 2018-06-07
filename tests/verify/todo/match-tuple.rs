//! Example: match of a tuple that uses references internally

#![feature(nll)]

extern crate prusti_contracts;

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
            // This match of a tuple uses references internally
            match (left, right) {
                (Num::Integer(_), Num::Integer(_)) => true,
                (Num::Rational(_, left_den), Num::Rational(_, right_den))
                if left_den != 0 && right_den != 0 => true,
                _ => false,
            }
        }
        Expr::Constant(Num::Integer(_)) => true,
        Expr::Constant(Num::Rational(_, den)) => den != 0
    };

    result
}

fn main() {}
