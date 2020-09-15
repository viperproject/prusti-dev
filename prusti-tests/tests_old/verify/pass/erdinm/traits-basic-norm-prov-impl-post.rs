use prusti_contracts::*;

trait Percentage {
    #[ensures(result <= 100)]
    fn get(&self) -> u8 {
        100
    }
}

struct Effective {}

impl Percentage for Effective {
    fn get(&self) -> u8 {
        100
    }
}

fn main() {}
