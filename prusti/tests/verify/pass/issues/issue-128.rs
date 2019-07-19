#![feature(nll)]

extern crate prusti_contracts;

pub trait MyMulAddAssign<A> {
    fn op(&mut self, a: A);
}

impl MyMulAddAssign<isize> for isize {
    fn op(&mut self, a: isize) {}
}

fn main(){}
