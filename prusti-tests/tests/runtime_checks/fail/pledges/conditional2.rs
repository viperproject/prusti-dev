//@run: 101
use prusti_contracts::*;
#[derive(Clone)]
struct Percentage(usize);

// if these are not trusted, prusti fails.. is it a bug?
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

#[trusted]
#[insert_runtime_check]
#[requires(p.0 >= 100)]
#[insert_runtime_check]
#[assert_on_expiry(*result >= 100, p.0 >= 100)]
#[insert_runtime_check]
#[ensures(old(p.0) == p.0)]
fn index_mut_other(p: &mut Percentage) -> &mut usize {
    &mut p.0
}

fn main() {
    // this once succeeds because index_mut is called
    // and *r = 72 right before expiration
    foo(true, true);

    // this one succeeds because index_mut_other is
    // called and *r is assigned 101 before expiry
    foo(false, false);

    // this one fails!
    foo(true, false);
}

#[trusted]
fn foo(b1: bool, b2: bool) {
    let mut p = Percentage(100);
    let r = if b1 {
        index_mut(&mut p)
    } else {
        index_mut_other(&mut p)
    };
    *r = 101;
    if b2 {
        *r = 72;
        // pledge expires here, if !b1 this causes
        // an error
    } else {
        // pledge expires here, before assignment
        // if b1, this should cause an error!
        p.0 = 101;
    }
}
