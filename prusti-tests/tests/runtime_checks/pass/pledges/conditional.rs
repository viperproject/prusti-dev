//@run
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
    // this one passes because index_mut is called
    foo(true);
}

#[trusted]
fn foo(b: bool) {
    let mut p = Percentage(100);
    let r = if b {
        index_mut(&mut p)
    } else {
        index_mut_other(&mut p)
    };
    // this is only a "valid" assignment if foo is called with
    // b = true
    *r = 72;
}
