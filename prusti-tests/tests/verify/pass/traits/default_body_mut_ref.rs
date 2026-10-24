use prusti_contracts::*;

// A default body returning a mutable reference is verified against the
// trait's own contract, not against the abstract pledge function that calls
// through the trait get.
trait Pick {
    fn pick<'a>(&self, x: &'a mut i32) -> &'a mut i32 {
        x
    }

    #[after_expiry(*x == before_expiry(*result))]
    fn pick_pledged<'a>(&self, x: &'a mut i32) -> &'a mut i32 {
        x
    }
}

struct S;

impl Pick for S {}

fn client<T: Pick>(t: &T) {
    let mut v = 1;
    let r = t.pick_pledged(&mut v);
    *r = 5;
    prusti_assert!(v == 5);
}

fn main() {}
