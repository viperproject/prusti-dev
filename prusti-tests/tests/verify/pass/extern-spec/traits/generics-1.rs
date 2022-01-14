extern crate prusti_contracts;
use prusti_contracts::*;

/// External traits
trait MyTrait<T> {
    fn get_value(&self) -> T;
}
/// External traits
#[extern_spec]
trait MyTrait<#[generic] T > {
    #[ensures(true)]
    fn get_value(&self) -> T;
}

struct Impl;
#[refine_trait_spec]
impl MyTrait<i32> for Impl {
    #[ensures(result == 42)]
    fn get_value(&self) -> i32 {
        42
    }
}


fn main() {
    let s = Impl{};
    assert!(MyTrait::<i32>::get_value(&s) == 42 as i32);
}