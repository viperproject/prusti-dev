#![allow(dead_code)]
#![allow(unused_variables)]
extern crate prusti_contracts;

#[invariant="self.value <= self.inner.value"]
struct Outer {
    value: u8,
    inner: Inner,
}

#[invariant="self.value <= 100"]
struct Inner {
    value: u8,
}

impl Outer {
    #[ensures="assert_on_expiry(old(self.value) <= result.value)"]
    fn inner_mut(&mut self) -> &mut Inner {
        &mut self.inner
    }
}

fn test(outer: &mut Outer) {
    assert!(outer.value <= 100);
    outer.inner_mut().value = outer.value;
}

fn main() {}
