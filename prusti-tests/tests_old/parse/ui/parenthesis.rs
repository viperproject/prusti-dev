/// Tests that parser handles spans correctly.

use prusti_contracts::*;

#[requires((true))]
pub fn test1a(x: i32) {}

#[requires((true)]
pub fn test1b(x: i32) {}

#[requires(true))]
pub fn test1c(x: i32) {}

#[requires(   (    12345))]
pub fn test1d(x: i32) {}

#[requires(   (    12345 && (

    true &&
        (false && 1234 || 
            x > 0 + 1)
        
        )
        ))]
pub fn test1e(x: i32) {}

fn main() {}
