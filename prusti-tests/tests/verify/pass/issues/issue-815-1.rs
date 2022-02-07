use prusti_contracts::*;

#[derive(Clone, Copy)]
pub struct A {
    inner: isize,
}

impl A {
    #[pure]
    #[requires(num < isize::MAX as usize)]
    pub fn new(num: usize) -> Self {
        Self {
            inner: num as isize + isize::MIN,
        }
    }

    #[pure]
    pub fn test(&self) {
        let _ = Self::new(2);
    }
}

fn main() {}
