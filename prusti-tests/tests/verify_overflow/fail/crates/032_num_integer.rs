/// Source: https://github.com/rust-num/num-integer
use prusti_contracts::*;

trait Integer {
    fn lcm(&self, other: &Self) -> Self;
    fn gcd(&self, other: &Self) -> Self;
}

impl Integer for i8 {
    fn lcm(&self, other: &Self) -> Self {
        // should not have to recalculate abs
        (*self * (*other / self.gcd(other))).abs() //~ ERROR
    }

    #[trusted]
    fn gcd(&self, other: &Self) -> Self {
        // Use Stein's algorithm
        let mut m = *self;
        let mut n = *other;
        if m == 0 || n == 0 {
            return m | n;
        }

        // find common factors of 2
        let shift = (m | n).trailing_zeros();

        // divide n and m by 2 until odd
        m >>= m.trailing_zeros();
        n >>= n.trailing_zeros();

        while m != n {
            if m > n {
                m -= n;
                m >>= m.trailing_zeros();
            } else {
                n -= m;
                n >>= n.trailing_zeros();
            }
        }
        m << shift
    }
}

fn main(){}
