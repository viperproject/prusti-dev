// Checking whether the params of pure methods are copy or not
use prusti_contracts::*;

#[pure]
#[trusted]
fn foo<'a, T: Copy>(val: T) -> Option<&'a T> { unimplemented!() }

#[pure]
#[trusted]
fn bar<'a, T: Copy>(val: T) -> &'a Option<&'a T> { unimplemented!() }

#[pure]
#[trusted]
fn baz<'a, T>(val: &'a T) -> Option<&'a T> { unimplemented!() }

fn main() {
}