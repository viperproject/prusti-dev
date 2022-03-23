// The client code still causes crashes:
// ignore-test
use prusti_contracts::*;
use std::cmp::{Ord, Ordering::{self, Equal, Less}};
fn main() {
    let mut v = 42;
    client(&mut v, true);
}

#[pure]
fn tautology<T>(_arg: &T, _arg2: &T) -> bool { true }

#[requires(forall(|other: &T| tautology(&x, other)))]
#[ensures(forall(|other: T| tautology(&other, &result)))]
fn foo<T>(x: T) -> T { x }

#[extern_spec]
trait Ord {
    #[pure]
    fn cmp(&self, other: &Self) -> Ordering;
}

#[requires(forall(|other: &T|
    matches!(_lower.cmp(other), Less)
    && matches!(other.cmp(_upper), Less)
        ==> matches!(_only_middle.cmp(other), Equal)))]
fn bar<T: Ord>(_lower: &T, _only_middle: &T, _upper: &T) { }

fn client<U: Ord, T: Ord + Copy>(x1: U, y1: T) {
    let x2 = foo(x1);
    bar(&x2, &x2, &x2);

    let y2 = foo(y1);
    let y3 = y2;
    bar(&y2, &y1, &y3);

    let val1 = 10;
    let val2 = foo(val1);
    let val3 = val1;
    bar(&val1, &val3, &val2);
}
