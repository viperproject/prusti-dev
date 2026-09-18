use prusti_contracts::*;

fn foo(x: Vec<i32>) {
    let l = x.len();
    prusti_assert!(l == x.len());
}
