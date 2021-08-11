use prusti_contracts::*;

trait Percentage {
    #[requires(arg <= 100)]
    fn set(&mut self, arg: u8);
}

fn test<T: Percentage>(t: &mut T) {
    t.set(100);
}

fn main() {}
