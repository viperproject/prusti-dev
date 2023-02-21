// compile-flags: -Popt_in_verification=false
use prusti_contracts::*;

fn main() {}

fn i_am_not_verified() {
    unreachable!(); //~ ERROR
}

#[verified]
fn i_am_verified() {
    assert!(1 == 2); //~ ERROR
}

#[verified]
#[trusted]
fn i_am_trusted() {
    unreachable!();
}
