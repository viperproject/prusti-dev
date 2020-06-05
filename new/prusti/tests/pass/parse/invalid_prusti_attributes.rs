#![feature(register_tool)]
#![register_tool(prusti)]
#![feature(stmt_expr_attributes)]
#![feature(custom_inner_attributes)]

#[prusti::requires::something(true)]
fn test1() {}

#[prusti::ensures2(true)]
fn test2() {}

fn test3() {
    for _ in 0..2 {
        #![prusti::invariant2(true)]
    }
}

fn test4() {
    for _ in 0..2 {
        #![prusti::invariant::something(true)]
    }
}

#[prusti::requires(true)]
#[prusti::ensures(true)]
fn test5() {
    for _ in 0..2 {
        #![prusti::invariant2(true)]
    }
}

#[prusti::requires(true)]
#[prusti::ensures(true)]
fn test6() {
    for _ in 0..2 {
        #![prusti::invariant::something(true)]
    }
}

fn main() {}
