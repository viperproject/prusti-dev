//@run
use prusti_contracts::*;

fn main() {
    mul(&mut 50);
}

#[trusted]
fn mul(x: &mut i32) {
    let mut res = 0;
    while *x > 0 {
        body_invariant!(old(*x) * 5 == res + *x * 5);
        res = res + 5;
        *x = *x-1;
    }
}
