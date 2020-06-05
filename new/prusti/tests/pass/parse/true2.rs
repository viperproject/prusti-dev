// compile-flags: -Zprint-desugared-specs

#![feature(register_tool)]
#![register_tool(prusti)]
#![feature(stmt_expr_attributes)]
#![feature(custom_inner_attributes)]

#[prusti::requires(true)]
fn test1() {}

#[prusti::ensures(true)]
fn test2() {}

fn test3() {
    for _ in 0..2 {
        #![prusti::invariant(true)]
    }
}

#[prusti::requires(true)]
#[prusti::ensures(true)]
fn test4() {
    for _ in 0..2 {
        #![prusti::invariant(true)]
    }
}

fn main() {}
