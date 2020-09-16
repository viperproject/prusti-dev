/// Tests that parser handles spans correctly.

use prusti_contracts::*;


#[requires(forall(|x: i32, y: usize| x > 0 ==> x + 2 > 2, triggers=[(x + 2, x + 3), (x + 4,)]))]
pub fn test1a(x: i32) {}

#[requires(forall(|x: 32, y: usize| x > 0 ==> x > -1, triggers=[]))]
pub fn test1b(x: i32) {}

#[requires(forall)]
pub fn test1c(x: i32) {}

#[requires(forall(|x: i32, y: usize|
    x > 0 ==> x + 2 > 2 ==> true,
    triggers=[(x + 2, x + 3), (x + 4,)]
))]
pub fn test1d(x: i32) {}


fn main() {}
