//@run
use prusti_contracts::*;

fn main() {
    test1(&mut 1);
    test2(&mut 10);
    test3(&mut 5);
}

#[trusted]
fn test1(x: &mut i32) {
    *x = 2;
    let a = x;
    prusti_assert!(old(*a) == 2);
}

#[trusted]
fn test2(x: &mut i32) {
    *x = 1;
    prusti_assert!({let a = x; old(*a) == 1});
}

#[trusted]
fn test3(x: &mut i32) {
    *x = 1;
    prusti_assert!(old({let a = x; *a == 5}));
}
