use prusti_contracts::*;

#[derive(Clone, Copy)]
pub struct A {
    count: isize,
}

impl A {
    #[pure]
    #[ensures(result <= isize::MAX as usize)]
    pub const fn len(&self) -> usize {
        if self.count < 0 {
            ((1_isize + self.count) + isize::MAX) as usize
        } else {
            self.count as usize
            //~^ ERROR value might not fit into the target type.
            // FIXME: https://github.com/viperproject/prusti-dev/issues/738
        }
    }
}

#[pure]
#[requires(slice.len() > 0)]
#[requires(slice[0].len() == 0)]
pub fn test(slice: &[A]) -> bool {
    true
}

fn main() {}
