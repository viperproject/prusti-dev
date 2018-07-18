#![feature(never_type)]

extern crate prusti_contracts;

fn diverging() -> ! {
    panic!();  //~ ERROR panic!(..) statement might panic
}

fn main() {
}
