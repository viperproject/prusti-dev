use prusti_contracts::*;

// A value after a call through a trait that the call cannot know is unknown,
// rather than the value before the call.
pub struct S<'a> {
    pub r: &'a mut i32,
}

trait T {
    // `x` is borrowed by the result, so it has no value after the call.
    #[ensures(*x == old(*x) + 1)]
    fn inc<'a>(&self, x: &'a mut i32) -> &'a mut i32;

    // The value behind a mutable reference inside an argument is not tracked.
    #[ensures(*s.r == 5)]
    fn set(&self, s: S<'_>);
}

fn blocked<X: T>(t: &X, x: &mut i32) {
    *x = 0;
    t.inc(x);
    prusti_assert!(false); //~ ERROR: assertion might not hold
}

fn nested<X: T>(t: &X, r: &mut i32) {
    *r = 1;
    t.set(S { r: &mut *r });
    prusti_assert!(false); //~ ERROR: assertion might not hold
}

// A trait's pledge is assumed for every impl, so each impl must satisfy it.
trait Pick {
    #[after_expiry(*x == before_expiry(*result))] //~ ERROR: pledge postcondition might not hold
    fn pick<'a>(&self, x: &'a mut i32, y: &'a mut i32) -> &'a mut i32;
}

struct Wrong;

impl Pick for Wrong {
    fn pick<'a>(&self, _x: &'a mut i32, y: &'a mut i32) -> &'a mut i32 {
        y
    }
}

fn main() {}
