extern crate prusti_contracts;
use prusti_contracts::*;

// ignore-test This works, but the error reporting crashes the compiler.

use std::collections::LinkedList;

#[extern_spec]
impl LinkedList::<i32> {
    #[ensures(true)]
    pub fn new() -> LinkedList<i32>;
}

#[extern_spec] //~ ERROR duplicate specification
impl<T> LinkedList<T> {
    #[ensures(true)]
    pub fn new() -> LinkedList<T>;
}

fn main() {
    let mut f = LinkedList::new();
    f.push_back(3);
}
