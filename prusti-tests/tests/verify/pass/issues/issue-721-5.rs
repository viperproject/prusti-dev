use prusti_contracts::*;

const SIZE: usize = 64;

#[trusted]
#[pure]
#[requires(index < array.len())]
#[ensures(result == array[index])]
const fn get(array: &[isize; SIZE], index: usize) -> isize {
    unimplemented!()
}

pub struct A {
    inner: [isize; SIZE],
}

impl A {
    #[pure]
    pub const fn start(&self) -> isize {
        get(&self.inner, 0)
    }

    pub const fn test(&self) -> isize {
        self.start()
    }
}

fn main() {}
