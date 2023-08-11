use prusti_contracts::*;

obligation! {
    fn alloced(amount: usize, loc: usize);
}

#[requires(a > 0 || alloced(1, 1))]
#[ensures(a > 0 || alloced(1, 1))]
fn f1(a: i32) {}

#[ensures(a > 0 && alloced(1, 1))]
#[requires(a > 0 && alloced(1, 1))]
fn f2(a: i32) -> i32 { 0 }

#[ensures(if a > 0 { alloced(1, 1) } else { alloced(33, 42) })]
#[requires(if a > 0 { alloced(1, 1) } else { alloced(33, 42) })]
fn f3(a: i32) -> i32 { 0 }

fn main() {}
