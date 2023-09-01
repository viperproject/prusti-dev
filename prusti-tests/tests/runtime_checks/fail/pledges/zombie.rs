//@run: 101
use prusti_contracts::*;
#[derive(Clone)]
struct Percentage(usize);

#[trusted]
#[insert_runtime_check]
#[requires(p.0 <= 100)]
#[insert_runtime_check]
#[assert_on_expiry(*result <= 100, p.0 <= 100)]
#[insert_runtime_check]
#[ensures(old(p.0) == p.0)]
fn index_mut(p: &mut Percentage) -> &mut usize {
    &mut p.0
}

fn main() {
    // runs through correctly, because at expiration p.0 is 72
    foo(true);
    // fails because p.0 = 102
    foo(false);
}

#[trusted]
fn foo(b: bool) {
    let mut p = Percentage(50);
    let mut r = index_mut(&mut p);
    let mut z = 1;
    if !b {
        let s = r;
        *s = 102;
    } else {
        // this branch doesn't cause a failure!
        *r = 105;
        let t = r;
        r = &mut z;
        *t = 78; // temporary violate pledge
                 // expiration
        p.0 = 105;
        // violating the condition right after pledge should be checked,
        // increases chances of us catching an error if it's inserted in the
        // wrong place
    }
    p.0 = 32;
}
