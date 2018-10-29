// MIT License
//
// Copyright (c) 2017 Aram Ebtekar
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in all
// copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.

//! Number-theoretic utilities for contest problems.

extern crate prusti_contracts;

#[trusted]
#[ensures="result == if old(x) < 0 { -old(x) } else { old(x) }"]
fn abs(x: i64) -> i64 {
    x.abs()
}

#[trusted]
#[ensures="result == if old(x) == 0 { 0 } else if old(x) > 0  { 1 } else { -1 }"]
fn signum(x: i64) -> i64 {
    x.signum()
}

/*
/// Modular exponentiation by repeated squaring: returns base^exp % m.
///
/// # Panics
///
/// Panics if m == 0. May panic on overflow if m * m > 2^63.
#[requires="m != 0"]
pub fn mod_pow(mut base: i64, mut exp: u32, m: i64) -> i64 {
    let m = m;
    let mut result = 1 % m;
    while exp > 0 {
        if exp % 2 == 1 {
            result = (result * base) % m;
        }
        base = (base * base) % m;
        exp /= 2;
    }
    result
}
*/

/// Finds (d, x, y) such that d = gcd(a, b) = ax + by.
#[ensures="{ let (d, x, y) = result; d == old(a) * x + old(b) * y }"]
pub fn extended_gcd(a: i64, b: i64) -> (i64, i64, i64) {
    if b == 0 {
        (abs(a), signum(a), 0)
    } else {
        let (d, x, y) = extended_gcd(b, a % b);
        (d, y, x - y * (a / b))
    }
}

/// Assuming a != 0, finds smallest y >= 0 such that ax + by = c.
///
/// # Panics
///
/// Panics if a == 0.
#[requires="a != 0"]
#[ensures="match result {
    Some((d, x, y)) => old(a) * x + old(b) * y == c,
    None => true,
}"]
pub fn canon_egcd(a: i64, b: i64, c: i64) -> Option<(i64, i64, i64)> {
    let (d, _, yy) = extended_gcd(a, b);
    if c % d == 0 {
        let z = abs(a / d);
        let y = (yy * (c / d) % z + z) % z;
        let x = (c - b * y) / a;
        Some((d, x, y))
    } else {
        None
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_mod_inverse() {
        let p = 1_000_000_007;
        let base = 31;

        let base_inv = mod_pow(base, p - 2, p);
        let identity = (base * base_inv) % p;

        assert_eq!(identity, 1);
    }

    #[test]
    fn test_egcd() {
        let (a, b) = (14, 35);

        let (d, x, y) = extended_gcd(a, b);
        assert_eq!(d, 7);
        assert_eq!(a * x + b * y, d);

        assert_eq!(canon_egcd(a, b, d), Some((d, -2, 1)));
        assert_eq!(canon_egcd(b, a, d), Some((d, -1, 3)));
    }
}

fn main(){}
