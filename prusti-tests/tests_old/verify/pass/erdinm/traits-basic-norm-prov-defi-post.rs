use prusti_contracts::*;

trait Percentage {
    #[ensures(result <= 100)]
    fn get(&self) -> u8 {
        100
    }
}

fn main() {}
