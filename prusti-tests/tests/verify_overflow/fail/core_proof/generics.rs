// compile-flags: -Punsafe_core_proof=true -Puse_smt_wrapper=true -Psmt_quantifier_instantiations_bound_global=10000 -Psmt_quantifier_instantiations_bound_trace=200 -Psmt_quantifier_instantiations_bound_trace_kind=10 -Psmt_quantifier_instantiations_bound_global_kind=100

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

fn test6<T>(a: U1<T>) -> U1<T> {
    a
}

fn test7<T: Default>() {
    let a = T::default();
    let _b = a;
}

fn test8<T, U: Default>(a: T) -> T {
    let b = a;
    let c = U::default();
    let _d = c;
    b
}

fn test9<T, U: Default>(a: T) -> T {
    let b = a;
    let c = U::default();
    let _d = c;
    assert!(false);  //~ ERROR: the asserted expression might not hold
    b
}

fn main() {}
