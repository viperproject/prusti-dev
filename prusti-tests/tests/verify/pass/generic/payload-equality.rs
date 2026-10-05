use prusti_contracts::*;

// Generic payloads are equal when their concrete values are, and payloads of
// zero-field types are always equal.

pub struct W<T> {
    pub f: T,
}

pub struct S {
    pub x: u32,
}

pub struct U;

pub struct C<const N: usize>;

#[requires(a.f.x == b.f.x)]
#[ensures(a === b)]
pub fn equal_struct_payload(a: W<S>, b: W<S>) {}

#[requires(a.f == b.f)]
#[ensures(a === b)]
pub fn equal_primitive_payload(a: W<u32>, b: W<u32>) {}

#[ensures(a === b)]
pub fn unit_payload(a: W<()>, b: W<()>) {}

#[ensures(a === b)]
pub fn unit_struct_payload(a: W<U>, b: W<U>) {}

#[ensures(a === b)]
pub fn const_generic_unit_payload(a: W<C<3>>, b: W<C<3>>) {}

#[requires(match a { Some(_) => true, None => false })]
#[requires(match b { Some(_) => true, None => false })]
#[ensures(a === b)]
pub fn unit_option(a: Option<()>, b: Option<()>) {}

#[ensures(match result { Ok(_) => true, Err(_) => false })]
fn ok_unit() -> Result<(), u32> {
    Ok(())
}

pub fn unit_result() {
    let r = ok_unit();
    prusti_assert!(r === Ok(()));
}
