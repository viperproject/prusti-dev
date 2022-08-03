// compile-flags: -Punsafe_core_proof=true

extern crate prusti_contracts;
use prusti_contracts::*;


#[requires(x > 0)]
#[ensures(result != 2)]
fn fail (x: i32) -> i32 {
    let mut y = x;
    y = y + 1;
    y
}


fn main(){}