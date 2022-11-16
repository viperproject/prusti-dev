use prusti_contracts::*;

trait Percentage {
    #[ensures(result <= 100)]
    fn get(&self) -> u8;
}

fn test<T: Percentage>(t: &T) {
    let p = t.get();
    assert!(p <= 100);
}

fn main() {}
