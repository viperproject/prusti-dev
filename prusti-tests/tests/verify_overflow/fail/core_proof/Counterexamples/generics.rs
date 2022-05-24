// compile-flags: -Punsafe_core_proof=true -Pcounterexample=true

use prusti_contracts::*;

fn test1<T>(a: T) -> T {
    a
}

fn test2<T>(a: T) -> T {
    let b = a;
    let c = test1(b);
    c
}

trait Validity {
    #[pure]
    fn valid(&self) -> bool;
}

#[requires(a.valid())]
#[ensures(result.valid())]
fn test3<T: Validity>(a: T) -> T {
    a
}

#[requires(a.valid())]
#[ensures(result.valid())]
fn test4<T: Validity>(a: T) -> T {
    let b = a;
    let c = test3(b);
    c
}

#[requires(a.valid())]
#[ensures(result.valid())]  //~ ERROR: postcondition might not hold.
fn test5<T: Validity>(a: T) -> T {
    let b = a;
    let c = test1(b);
    c
}

struct U1<T> {
    value: T,
}

#[ensures(result.value.valid())]
fn test6<T:Validity>(a: U1<T>) -> U1<T> {
    a
}

fn main() {}
