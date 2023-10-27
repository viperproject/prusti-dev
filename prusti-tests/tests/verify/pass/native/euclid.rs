// compile-flags: -Pviper_backend=Lithium

use prusti_contracts::*;

macro_rules! divides_prop {
    ($x:expr, $y:expr, $z:expr) => {
        $z >= 0 && $x * $z == $y
    };
}

#[pure]
#[terminates]
#[trusted]
#[requires(x > 0 && y > 0)]
#[ensures(x <= y)]
fn divides(x: i32, y: i32) -> bool {
    unimplemented!()
}

#[pure]
#[terminates]
#[trusted]
#[requires(x > 0 && y > 0)]
#[ensures(result >= 1)]
#[ensures(divides(result, x))]
#[ensures(divides(result, y))]
#[ensures(forall(|z: i32| z >= 1 && divides(z, x) && divides(z, y) ==> z <= result))]
fn gcd(x: i32, y: i32) -> i32 {
    if x > y {
        gcd(x - y, y)
    } else if x < y {
        gcd(x, y - x)
    } else {
        x
    }
}

#[trusted]
#[requires(x > 0 && y > 0)]
#[requires(divides_prop!(x, y, z))]
#[ensures(divides(x, y))]
fn lemma_show_divides(x: i32, y: i32, z: i32) {}

#[trusted]
#[requires(x > 0 && y > 0)]
#[requires(divides(x, y))]
#[ensures(divides_prop!(x, y, result))]
fn lemma_divides(x: i32, y: i32) -> i32 {
    unimplemented!()
}

#[requires(x > 0 && y > 0)]
#[ensures(gcd(x + y, y) == gcd(x, y))]
fn lemma_gcd(x: i32, y: i32) {
    lemma_gcd_lower(x, y);
    lemma_gcd_upper(x, y);
}

#[requires(x > 0 && y > 0)]
#[ensures(gcd(x + y, y) >= gcd(x, y))]
fn lemma_gcd_upper(x: i32, y: i32) {
    let z: i32 = x + y;
    let m: i32 = gcd(z, y);
    let n: i32 = gcd(y, x);

    let c: i32 = lemma_divides(n, y);
    let d: i32 = lemma_divides(n, x);

    lemma_show_divides(n, z, c + d);
}

#[requires(x > 0 && y > 0)]
#[ensures(gcd(x + y, y) <= gcd(x, y))]
fn lemma_gcd_lower(x: i32, y: i32) {
    let z: i32 = x + y;
    let m: i32 = gcd(z, y);

    let c: i32 = lemma_divides(m, z);
    let d: i32 = lemma_divides(m, y);

    lemma_show_divides(m, x, c - d);
}

#[requires(x > 0)]
#[ensures(gcd(x, x) == x)]
fn lemma_gcd_idempotent(x: i32) {
    lemma_show_divides(x, x, 1);
}

#[requires(n > 0 && m > 0)]
#[ensures(result == gcd(n, m))]
fn euclid(n: i32, m: i32) -> i32 {
    let mut a: i32 = n;
    let mut b: i32 = m;

    while a != b {
        body_invariant!(a > 0 && b > 0);
        body_invariant!(gcd(a, b) == gcd(n, m));

        if a > b {
            a -= b;
            lemma_gcd(a, b);
        } else {
            b -= a;
            lemma_gcd(b, a);
        }
    }

    lemma_gcd_idempotent(a);

    a
}

fn main() {}
