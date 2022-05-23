use prusti_contracts::*;

#[pure]
#[trusted]
// TODO: add spec for `std::ptr::eq`
#[ensures(result == true)]
fn ptr_eq<T>(l: &T, r: &T) -> bool { std::ptr::eq(l, r) }

#[after_expiry(
    ptr_eq(t, before_expiry(result))
)]
fn identity<T>(t: &mut T) -> &mut T {
    t
}

fn main() {}
