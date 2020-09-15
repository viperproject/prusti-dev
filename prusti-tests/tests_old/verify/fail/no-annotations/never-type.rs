#![feature(never_type)]

use prusti_contracts::*;

fn diverging() -> ! {
    panic!();  //~ ERROR panic!(..) statement might panic
}

fn main() {
}
