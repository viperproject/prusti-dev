use prusti_contracts::*;

pub struct B(isize);

impl B {
    #[pure]
    #[ensures(result <= 16)]
    pub const fn get_non_negative(&self) -> isize {
        match self.get_saturated() {
            i if i < 0 => 0,
            i => i,
        }
    }

    #[pure]
    pub const fn get_saturated(&self) -> isize {
        match self.0 {
            isize::MIN..=-17 => -16,
            17.. => 16,
            i => i,
        }
    }

    #[requires(_i < self.get_non_negative())]
    pub const fn test(&self, _i: isize) {}
}

fn main() {}
