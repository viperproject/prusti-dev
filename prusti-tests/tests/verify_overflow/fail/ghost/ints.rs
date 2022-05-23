// compile-flags: -Punsafe_core_proof=true

use prusti_contracts::*;

#[requires(a == Int::new(5))]
fn test1(a: Int) {}

#[ensures(a == Int::new(5))]    //~ ERROR: postcondition might not hold.
fn test2(a: Int) {}

#[ensures(Int::new(1) == Int::new(1))]
fn test3() {}

#[ensures(Int::new(1) == Int::new(2))]    //~ ERROR: postcondition might not hold.
fn test4() {}

#[ensures(result == Int::new(5))]
fn test5() -> Int {
    let b = 5;
    let a = Int::new(b);
    a
}

#[ensures(result == Int::new(5))]
#[ensures(false)]    //~ ERROR: postcondition might not hold.
fn test6() -> Int {
    let b = 5;
    let a = Int::new(b);
    a
}

fn main() {}

