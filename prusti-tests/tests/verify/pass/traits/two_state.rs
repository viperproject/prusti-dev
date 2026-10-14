use prusti_contracts::*;

// Through a trait, the postconditions see the arguments after the call and
// the pledges see them once the borrow of the result expires.
trait T {
    #[ensures(*x == old(*x) + 1)]
    fn bump(&self, x: &mut i32);

    #[ensures(*result == old(*x))]
    #[after_expiry(*x == before_expiry(*result))]
    fn get<'a>(&self, x: &'a mut i32) -> &'a mut i32;
}

fn client<X: T>(t: &X, x: &mut i32) {
    *x = 0;
    t.bump(x);
    assert!(*x == 1);
    let r = t.get(x);
    assert!(*r == 1);
    *r = 7;
    assert!(*x == 7);
}

fn main() {}
