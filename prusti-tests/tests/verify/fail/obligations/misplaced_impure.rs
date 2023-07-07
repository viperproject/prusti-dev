use prusti_contracts::*;

obligation! {
    fn alloced(amount: usize, loc: usize);
}

#[ensures((result > 0) | alloced(1, 1))] //~ ERROR resource access is illegal inside disjunctions
fn f1() -> i32 { 0 }

#[ensures(alloced(1, 1) | (result > 0))] //~ ERROR resource access is illegal inside disjunctions
fn f2() -> i32 { 0 }

#[ensures(alloced(1, 1) == (result > 0))] //~ ERROR resource access is illegal inside equality comparisons
fn f3() -> i32 { 0 }

#[ensures(alloced(1, 1) != (result > 0))] //~ ERROR resource access is illegal inside equality comparisons
fn f4() -> i32 { 0 }

#[ensures((result > 0) == alloced(1, 1))] //~ ERROR resource access is illegal inside equality comparisons
fn f5() -> i32 { 0 }

#[ensures((result > 0) != alloced(1, 1))] //~ ERROR resource access is illegal inside equality comparisons
fn f6() -> i32 { 0 }

// TODO add obligations in conditionals to this test

fn main() {}
