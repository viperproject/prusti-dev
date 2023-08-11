use prusti_contracts::*;

obligation! {
    fn alloced(amount: usize, loc: usize);
}

#[pure]
fn f(flag: bool) -> bool {
    true
}

resource! {
    fn rsrc(amount: usize, flag: bool);
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

#[ensures(!alloced(1, 1))] //~ ERROR resource access is illegal inside negations
fn f7() -> i32 { 0 }

#[ensures(f(alloced(1, 1)))] //~ ERROR resource access is illegal inside function arguments
fn f8() -> i32 { 0 }

#[ensures(rsrc(1, alloced(1, 1)))] //~ ERROR resource access is illegal inside resource access arguments
fn f9() -> i32 { 0 }

#[ensures(exists(|loc: usize| alloced(1, loc)))] //~ ERROR resource access is illegal inside existential quantifiers
fn f10() -> i32 { 0 }

// FIXME the following tests report confusing places for where the impurity is

// TODO add test for resource access in the guard of a conditional when the error messages there are made to work properly in future

#[ensures(alloced(1, 1) || result > 0)] //~ ERROR resource access is illegal inside
fn f11() -> i32 { 0 }

#[ensures(alloced(1, 1) && result > 0)] //~ ERROR resource access is illegal inside
fn f12() -> i32 { 0 }

fn main() {}
