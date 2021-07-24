use prusti_contracts::*;

/// The fused multiply-add assignment operation.
pub trait MyMulAddAssign<A = Self, B = Self> {
    /// Performs the fused multiply-add operation.
    fn my_mul_add_assign(&mut self, a: A, b: B);
}

impl MyMulAddAssign for isize {
    fn my_mul_add_assign(&mut self, a: Self, b: Self) {
        *self = (*self * a) + b
    }
}

fn main(){}
