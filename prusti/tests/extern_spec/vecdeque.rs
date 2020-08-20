#![feature(register_tool)]
#![register_tool(prusti)]

extern crate prusti_contracts;
use prusti_contracts::*;

use std::collections::VecDeque;
use std::option::Option;

#[extern_spec]
impl<T> std::option::Option::<T> {
    #[pure]
    #[ensures(matches!(*self, Some(_)) == result)]
    pub fn is_some(&self) -> bool;

    #[pure]
    #[ensures(self.is_some() == !result)]
    pub fn is_none(&self) -> bool;

    #[requires(self.is_some())]
    pub fn unwrap(self) -> T;

    #[requires(self.is_some())]
    pub fn expect(self, msg: &str) -> T;
}

#[extern_spec]
impl<T> VecDeque::<T> {

    #[ensures(result.len() == 0)]
    pub fn new() -> VecDeque<T>;

    // #[pure]
    // pub fn get(&self, index: usize) -> Option<&T>;

    #[pure]
    pub fn get_mut(&mut self, index: usize) -> Option<&mut T>;

    #[pure]
    pub fn len(&self) -> usize;
    //
    // pub fn pop_front(&mut self) -> Option<T>;

    #[ensures(self.len() == old(self.len()) + 1)]
    // #[ensures(*self.get(0).unwrap() == value)]
    pub fn push_front(&mut self, value: T);
}

#[ensures(true)]
fn test(op: Option<&i32>) {

}

fn main() {
    // let mut vecd = VecDeque::new();
    // vecd.push_back(3);
    // vecd.push_front(2);
    // vecd.get_mut(0);
    let i = 2;
    test(Some(&i));
}
