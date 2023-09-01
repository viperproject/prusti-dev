//@run: 101
use prusti_contracts::*;

fn main() {
    mul(&mut 50);
}

#[trusted]
fn mul(x: &mut i32) {
    let mut res = 1;
    while *x > 0 {
        body_invariant!(#[insert_runtime_check]old(*x) * 5 == res + *x * 5);
        res = res + 5;
        *x = *x-1;
    }
}
