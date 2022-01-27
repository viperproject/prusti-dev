extern crate prusti_contracts;
use prusti_contracts::*;

use std::vec::Vec;

#[model]
struct Vec<T> { //~ ERROR: cannot find type `T` in this scope [E0412]
    fld: i32,
}

fn main() {
}
