use prusti_contracts::*;

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
    pub fn len(&self) -> u64 {
        self.0.len() as _
    }

    #[trusted]
    #[requires(idx < self.len())]
    pub fn index(&self, idx: u64) -> &T {
        &self.0[idx as usize]
    }

    #[trusted]
    #[requires(idx < self.len())]
    #[after_expiry(self.len() == old(self.len()))]
    pub fn index_mut(&mut self, idx: u64) -> &mut T {
        &mut self.0[idx as usize]
    }
}

impl<T: Clone> Vector<T> {
    #[trusted]
    #[ensures(result.len() == len)]
    pub fn init(init: T, len: u64) -> Self {
        Self(vec![init; len as usize])
    }
}
