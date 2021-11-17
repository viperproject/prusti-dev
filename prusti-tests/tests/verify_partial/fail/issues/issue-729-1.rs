// error-pattern: Precondition of function snap$__$TY$__struct$m_A$Snap$struct$m_A might not hold
// FIXME: https://github.com/viperproject/prusti-dev/issues/729
#![allow(unused_comparisons)]
use prusti_contracts::*;

pub struct A {
    inner: [usize; 4],
}

impl A {
    #[pure]
    #[requires(index < self.inner.len())]
    pub fn is_valid(&self, index: usize) -> bool {
        self.inner[index] <= isize::MAX as usize
    }

    #[pure]
    #[ensures(forall(|i: usize| (result && index < self.inner.len() && 0 <= i && i <= index) ==> (self.is_valid(i))) )]
    pub fn test(&self, index: usize) -> bool {
        match index {
            index if 0 < index && index < self.inner.len() => {
                self.is_valid(index) && self.test(index - 1)
            }
            index if index == 0 => self.is_valid(index),
            _ => false,
        }
    }
}

fn main() {}
