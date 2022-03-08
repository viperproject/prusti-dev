extern crate prusti_contracts;
use prusti_contracts::*;

use std::vec::Vec;

#[model]
struct Vec<T> { //~ ERROR: Type parameters must be annotated with exactly one of #[generic] or #[concrete]
    fld: i32,
}

fn main() {
}
