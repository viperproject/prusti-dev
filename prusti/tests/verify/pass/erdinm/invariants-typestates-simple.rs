extern crate prusti_contracts;

struct Neg;

#[invariant="S == Neg ~~> self.i < 0"]
struct Number<S> {
    i: i32,
    s: S,
}

impl<X> Number<X> {
    #[ensures="-1 <= self.i && self.i <= 1"]
    fn to_sign(&mut self) {
        if self.i <= -1 {
            self.i = -1;
        } else if self.i >= 1 {
            self.i = 1;
        }
    }
}

fn test1(mut n: Number<Neg>) {
    n.to_sign();
    assert!(n.i == -1);
}

fn main() {}
