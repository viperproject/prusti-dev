enum Expr {
    Sum(i32, i32)
}

fn eval(expr: Expr) -> i32 {
    match expr {
        Expr::Sum(left, right) => left + right
    }
}

fn main() {}
