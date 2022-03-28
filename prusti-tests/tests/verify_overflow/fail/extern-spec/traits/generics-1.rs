// ignore-test #[concrete] currently not supported

use prusti_contracts::*;

trait MyTrait<T> {
    fn get_value(&self) -> T;
}

#[extern_spec]
trait MyTrait<#[concrete] i32> {
    #[ensures(result == 42)]
    fn get_value(&self) -> i32;
}

#[extern_spec]
trait MyTrait<#[concrete] u32> {
    #[ensures(result == 43)] //~ ERROR: duplicate specification for MyTrait::get_value
    fn get_value(&self) -> u32; 
}

struct Impl;
impl MyTrait<i32> for Impl {
    fn get_value(&self) -> i32 {
        42
    }
}
impl MyTrait<u32> for Impl {
    fn get_value(&self) -> u32 {
        43
    }
}

fn main() {
    let s = Impl {};
    assert!(MyTrait::<i32>::get_value(&s) == 42);
    assert!(MyTrait::<u32>::get_value(&s) == 43);
}
