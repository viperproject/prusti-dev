//@run: 101
use prusti_contracts::*;

fn main() {
    // passes
    test1(&mut 1);
    // passes
    test2(&mut 10);
    // fails:
    test3(&mut 2);
}

#[trusted]
fn test1(x: &mut i32) {
    *x = 2;
    let a = x;
    prusti_assert!(#[insert_runtime_check] old(*a) == 2);
}

#[trusted]
fn test2(x: &mut i32) {
    *x = 1;
    prusti_assert!(#[insert_runtime_check] {let a = x; old(*a) == 1});
}

#[trusted]
fn test3(x: &mut i32) {
    *x = 1;
    // fails: *a is assigned x in old state.
    prusti_assert!(#[insert_runtime_check] old({let a = x; *a == 1}));
}
