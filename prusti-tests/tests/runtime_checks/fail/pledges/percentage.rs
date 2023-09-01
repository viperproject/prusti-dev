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
    // this one passes because *r will be set to 72
    foo(true);
    // this one fails because *r is set to 101
    foo(false);
}

#[trusted]
fn foo(b: bool) {
    let mut p = Percentage(50);
    let r = index_mut(&mut p);
    if b {
        *r = 72;
    } else {
        // this assignment violates the pledge
        *r = 101;
        p.0 = 43
    }
    p.0 = 32;
}
