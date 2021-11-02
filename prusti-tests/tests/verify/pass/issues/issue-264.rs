use prusti_contracts::*;

struct T {
    f: u32,
}

impl T {
    #[pure]
    #[ensures(result == (self.f * (self.f + 1)) / 2)]
    fn sum(&self) -> u32 {
        if self.f == 0 {
            0
        } else {
            self.f + (T { f: self.f - 1 }.sum())
        }
    }
}

fn main() {}
