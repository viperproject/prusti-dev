// A negative impl states that a trait is *not* implemented. Encoding it like
// a positive impl would make `u8: Tr` hold, so that the blanket impl below
// would apply to `u8` alongside the concrete one, resolving `<u8 as Foo>::A`
// to both `u32` and `u64`.

#![feature(negative_impls, with_negative_coherence)]

use prusti_contracts::*;

pub trait Tr {}
impl !Tr for u8 {}

pub trait Foo {
    type A;
}
impl<T: Tr> Foo for T {
    type A = u32;
}
impl Foo for u8 {
    type A = u64;
}

pub fn foo<T: Foo>(_t: T) {}

pub fn use_u8(x: u8) {
    foo(x);
}

#[ensures(false)] //~ ERROR: postcondition might not hold
pub fn canary() {}
