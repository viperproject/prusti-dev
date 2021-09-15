/// Tests that parser handles spans correctly.

use prusti_contracts::*;


#[requires(exists(|x: i32, y: usize| x > 0 ==> x + 2 > 2, triggers=[(x + 2, x + 3), (x + 4,)]))]
pub fn good_1(x: i32) {}

#[requires(exists(|x: 32, y: usize| x > 0 ==> x > -1, triggers=[]))]
pub fn good_2(x: i32) {}

#[requires(exists)]
pub fn wrong_1(x: i32) {}

#[requires(exists(|x: i32, y: usize|
    x > 0 ==> x + 2 > 2 ==> true,
    triggers=[(x + 2, x + 3), (x + 4,)]
))]
pub fn wrong_2(x: i32) {}


fn main() {}

