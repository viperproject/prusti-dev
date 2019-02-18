extern crate prusti_contracts;

use std::marker::PhantomData;

struct Neg;
struct Pos;

struct Number<S> {
    i: i32,
    s: PhantomData<S>,
}

impl<X> Number<X> {
    #[requires="X == Neg ~~> self.i < 0"]
    #[requires="X == Pos ~~> self.i > 0"]
    #[ensures="X == Neg ~~> self.i < 0"]
    #[ensures="X == Pos ~~> self.i > 0"]
    #[ensures="self.i >= -1 && self.i <= 1"]
    fn to_sign(&mut self) {
        if self.i <= -1 {
            self.i = -1;
        } else if self.i >= 1 {
            self.i = 1;
        }
    }
}

#[requires="n.i < 0"]
fn test1(mut n: Number<Neg>) {
    n.to_sign();
    assert!(n.i == 1); //~ ERROR assert!(..) statement might not hold
}

#[requires="n.i > 0"]
fn test2(mut n: Number<Pos>) {
    n.to_sign();
    assert!(n.i == -1); //~ ERROR assert!(..) statement might not hold
}

fn main() {}
