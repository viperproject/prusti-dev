// compile-flags: -Punsafe_core_proof=true

#![allow(unused)]

use prusti_contracts::*;

#[requires(a == Int::new(5))]
fn precond_test(a: Int) {}

#[ensures(a == Int::new(5))] //~ ERROR: postcondition might not hold.
fn postcond_test(a: Int) {}

fn int_equality(a: i64) {
    prusti_assert!(Int::new(a) == Int::new(a));
    prusti_assert!(Int::new(1) == Int::new(2)); //~ ERROR: the asserted expression might not hold

    let x = 5;
    let x_int = Int::new(x);
    prusti_assert!(Int::new(5) == x_int);
}

#[requires(x > -10000 && x < 10000 && y > -10000 && y < 10000 && y != 0)]
fn operations_equivalent(x: i64, y: i64) {
    prusti_assert!(Int::new(-x) == -Int::new(x));
    prusti_assert!(Int::new(x + y) == Int::new(x) + Int::new(y));
    prusti_assert!(Int::new(x - y) == Int::new(x) - Int::new(y));
}

// We need to assume y == 5 to avoid non-linear arithmetic when doing
// the bounds checks that choke Z3.
#[requires(x > -10000 && x < 10000 && y == 5)]
fn operations_equivalent2(x: i64, y: i64) {
    prusti_assert!(Int::new(-x) == -Int::new(x));
    prusti_assert!(Int::new(x + y) == Int::new(x) + Int::new(y));
    prusti_assert!(Int::new(x - y) == Int::new(x) - Int::new(y));
    prusti_assert!(Int::new(x * y) == Int::new(x) * Int::new(y));
    prusti_assert!(Int::new(x / y) == Int::new(x) / Int::new(y));
    prusti_assert!(Int::new(x % y) == Int::new(x) % Int::new(y));
}

fn neutral_elements(a: Int) {
    let i0 = Int::new(0);
    let i1 = Int::new(1);

    prusti_assert!(i0 + a == a);
    prusti_assert!(i1 * a == a);
    prusti_assert!(i0 * a == i0);
    prusti_assert!(-i0 == i0);
}

fn associativity(a: Int, b: Int, c: Int) {
    prusti_assert!(a + (b + c) == (a + b) + c);
    prusti_assert!(a * (b * c) == (a * b) * c);
}

fn commutativity(a: Int, b: Int) {
    prusti_assert!(a + b == b + a);
    prusti_assert!(a * b == b * a);
}

fn distributivity(a: Int, b: Int, c: Int) {
    prusti_assert!(a * (b + c) == a * b + a * c);
}

fn negations(a: Int, b: Int) {
    prusti_assert!(a + (-b) == a - b);
    prusti_assert!(a - a == Int::new(0));
    prusti_assert!(-(-a) == a);
    prusti_assert!((-a) * b == -(a * b));
    prusti_assert!(-a == Int::new(0) - a);
    prusti_assert!(-(a + b) == (-a) + (-b));
}

#[requires(a > Int::new(0) && b > Int::new(0))]
fn remainder1(a: Int, b: Int) {
    prusti_assert!(a % b >= Int::new(0));
}

#[requires(a > Int::new(0) && b > Int::new(0))]
fn remainder2(a: Int, b: Int) {
    let r = a % b;
    prusti_assert!(r >= Int::new(0));
}

#[requires(a > Int::new(0) && b > Int::new(0))]
fn divisions(a: Int, b: Int) {
    let c = a / b;
}

fn cmp(a: Int, b: Int, c: Int) {
    // reflexivity
    prusti_assert!(a <= a);

    // antisymmetry
    prusti_assert!(a <= b && b <= a ==> a == b);

    // transitivity
    prusti_assert!(a < b && b < c ==> a < c);
    prusti_assert!(a <= b && b <= c ==> a <= c);

    // totality
    prusti_assert!(a <= b || b <= a);

    // lt and gt, le and ge should be consistent
    prusti_assert!((a < b) == (b > a));
    prusti_assert!((a <= b) == (b >= a));

    prusti_assert!(!(a < b && b < a));

    prusti_assert!(a < b ==> a <= b);
    prusti_assert!(a <= b ==> a < b || a == b);
}

fn eq(a: Int, b: Int, c: Int) {
    // reflexivity
    prusti_assert!(a == a);

    // symmetry
    prusti_assert!((a == b) == (b == a));

    // transitivity
    prusti_assert!(a == b && b == c ==> a == c);

    // not all Ints are the same, i.e. no trivial equivalence
    prusti_assert!(a == b); //~ ERROR: the asserted expression might not hold

    // != and == are consistent with each other
    prusti_assert!((a == b) == !(a != b));
}

fn mixed_test(a: Int, b: Int, c: Int, x: Int, y: Int, z: Int) {
    prusti_assert!(a < b ==> a + c < b + c);
}

fn main() {
    eq(Int::new(0), Int::new(1), Int::new(2));
}
