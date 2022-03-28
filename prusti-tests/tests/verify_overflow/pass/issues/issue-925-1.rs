use prusti_contracts::*;

fn main() {
    let a = A::new(2, 3);
    A::test(a, 4);
}

#[derive(Clone, Copy)]
pub struct A {
    foo: isize,
    bar: usize,
}

impl A {
    #[pure]
    #[requires(num < isize::MAX as usize)]
    pub fn new(num: usize, bar: usize) -> Self {
        Self {
            foo: num as isize + isize::MIN,
            bar,
        }
    }

    #[pure]
    pub fn bar(&self) -> usize {
        self.bar
    }

    #[pure]
    #[requires(num < isize::MAX as usize)]
    pub fn test(a: A, num: usize) -> A {
        A::new(num, a.bar)
    }
}
