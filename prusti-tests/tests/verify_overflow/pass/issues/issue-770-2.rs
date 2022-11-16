use prusti_contracts::*;

pub struct A {
    entries: [usize; 4],
}

impl A {
    #[pure]
    #[requires(index < 4)]
    #[ensures(0 <= result)]
    pub fn get(&self, index: usize) -> usize {
        self.entries[index]
    }

    pub fn test(&self) {
        self.get(2);
    }
}

pub struct B {
    entries: [usize],
}

impl B {
    #[pure]
    #[requires(index < self.entries.len())]
    #[ensures(0 <= result)]
    pub fn get(&self, index: usize) -> usize {
        self.entries[index]
    }

    #[requires(self.entries.len() > 2)]
    pub fn test(&self) {
        self.get(2);
    }
}

fn main() {}
