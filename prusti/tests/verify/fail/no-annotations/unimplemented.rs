#![feature(nll)]

extern crate prusti_contracts;

fn foo(x: i32) -> i32 {
    unimplemented!(); //~ ERROR unimplemented!(..) statement might be reachable
}

fn main(){}
