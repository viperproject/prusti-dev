// compile-flags: --deny warnings
use prusti_contracts::*;

use std::io::Empty; // An external type which has no fields
#[model]
struct Empty {
    val: i32,
}

fn main() {
}