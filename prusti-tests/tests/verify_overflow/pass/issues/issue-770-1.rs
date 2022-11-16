use prusti_contracts::*;

pub struct A {
    b: isize,
}

impl A {
    #[pure]
    #[ensures(result == true)]
    pub const fn invariant(&self) -> bool {
        self.is_negative() != self.is_non_negative()
    }

    #[pure]
    pub const fn is_non_negative(&self) -> bool {
        self.b >= 0
    }

    #[pure]
    pub const fn is_negative(&self) -> bool {
        self.b < 0
    }

    #[requires(self.invariant())]
    pub const fn test(&self) {}
}

fn main() {}
