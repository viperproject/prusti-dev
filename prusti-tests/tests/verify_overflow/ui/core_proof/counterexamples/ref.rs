// compile-flags: -Punsafe_core_proof=true -Pcounterexample=true -Pcheck_overflows=false

use prusti_contracts::*;

#[requires(*x != 0)]
#[ensures(result != 0)]
fn test1(x: &mut i32) -> i32 {
    let mut y = *x;
    y = y * 3 - 12;
    *x = y;
    y
}

#[requires(*x != 0)]
#[ensures(result != 14)]
fn test2(x: &i32) -> i32 {
    let y = *x + 1;
    match y {
        x => x * 2
    }
}

fn test3() {
    let mut a = 1;
    let _b = &mut a;
    *_b = 2;
    *_b = 10;
    assert!(a == 1); 
}

fn main() {}
