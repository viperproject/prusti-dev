// compile-flags: -Pverification_deadline=30

//! See https://github.com/viperproject/prusti-dev/issues/721

use prusti_contracts::*;

pub const MAX_DEPTH: usize = usize::BITS as usize;

pub struct Path {
    current: usize,
    depth: usize,
    entries: [usize; MAX_DEPTH],
    max_counts: [usize; MAX_DEPTH],
}

impl Path {
    #[pure]
    pub fn invariant(&self) -> bool {
        self.entries.len() == MAX_DEPTH
            && self.max_counts.len() == MAX_DEPTH
            && self.entries.len() == self.max_counts.len()
            && self.current < MAX_DEPTH
            && self.depth < MAX_DEPTH
            && self.current <= self.depth
    }

    #[requires(self.invariant())]
    #[ensures(self.current == 0)]
    #[ensures(self.depth == 0)]
    #[ensures(self.entries[0] == 0)]
    #[ensures(self.invariant())]
    pub fn reset(&mut self) {
        self.current = 0;
        self.depth = 0;
        self.entries[0] = 0;
        assert!(self.entries.len() == self.max_counts.len());
        assert!(self.current < MAX_DEPTH);
        assert!(self.depth < MAX_DEPTH);
        assert!(self.current <= self.depth);
        assert!(self.entries[0] == 0);
    }
}

fn main() {}
