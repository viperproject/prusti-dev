use prusti_contracts::*;
use core::ops::*;

pub struct Vector<T>(Vec<T>);

impl<T> Vector<T> {
    #[trusted]
    #[ensures(result.len() == 0)]
    pub fn new() -> Self {
        Self(Vec::new())
    }

    pub fn from_vec(vec: Vec<T>) -> Self {
        Self(vec)
    }

    #[trusted]
    #[pure]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    #[trusted]
    #[requires(idx < self.len())]
    pub fn index(&self, idx: usize) -> &T {
        &self.0[idx]
    }

    #[trusted]
    #[requires(idx < self.len())]
    #[after_expiry(self.len() == old(self.len()))]
    pub fn index_mut(&mut self, idx: usize) -> &mut T {
        &mut self.0[idx]
    }
}

impl<T: Clone> Vector<T> {
    #[trusted]
    #[ensures(result.len() == len)]
    pub fn init(init: T, len: usize) -> Self {
        Self(vec![init; len])
    }
}