use prusti_contracts::*;

// A default body returning a mutable reference must still establish the
// trait method's own pledges.
trait Pick {
    #[after_expiry(*x == 0)] //~ ERROR: pledge postcondition might not hold
    fn pick<'a>(&self, x: &'a mut i32) -> &'a mut i32 {
        x
    }
}

fn main() {}
