/// Tests that parser handles spans correctly.

use prusti_contracts::*;

#[requires((true))]
pub fn test_1(x: i32) {}

#[requires(   (    12345))]
pub fn test_2(x: i32) {}

#[requires(   (    12345 && (

    true &&
        ((false && 1234) ||
            x > 0 + 1)
        
        )
        ))]
pub fn test_3(x: i32) {}

fn main() {}
