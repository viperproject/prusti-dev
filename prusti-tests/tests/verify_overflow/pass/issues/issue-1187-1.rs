// compile-flags: -Popt_in_verification=true
use prusti_contracts::*;

fn main() {}

fn i_am_not_verified() {
    unreachable!();
}

#[verified]
fn i_am_verified() {
    assert!(1 != 2);
}

#[verified]
#[pure]
fn i_am_pure() {
    assert!(true);
}

#[verified]
#[trusted]
fn i_am_trusted() {
    unreachable!();
}
