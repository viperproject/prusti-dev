// compile-flags: -Pcounterexample=true

use prusti_contracts::*;

enum BinOp {
    Add(i32, i32),
    Sub(i32, i32),
    Div(i32, i32),
}

fn apply(op: BinOp) -> i32 {
    match op {
        BinOp::Add(a, b) => a + b,
        BinOp::Sub(c, d) => c - d,
        BinOp::Div(e, f) => {
            if e == 1 { // force specific counterexample
                e / f
            } else {
                0
            }
        }
    }
}

fn main() {}
