// ignore-test #[concrete] is troublesome

use prusti_contracts::*;

/// External traits
trait MyTrait<T> {
    fn get_value(&self) -> T;
}
/// External traits

#[extern_spec]
trait MyTrait<#[concrete] i32 > {
    #[ensures(result == 42)]
    fn get_value(&self) -> i32;
}

struct Impl;
impl MyTrait<i32> for Impl {
    fn get_value(&self) -> i32 {
        42
    }
}

fn main() {
    let s = Impl{};
    assert!(MyTrait::<i32>::get_value(&s) == 42);
    assert!(s.get_value() == 42);
}
