use prusti_contracts::*;

trait Percentage {
    #[requires(arg <= 100)]
    fn set(&mut self, arg: u8) {
        assert!(arg <= 100);
    }
}

fn test<T: Percentage>(t: &mut T) {
    t.set(123); //~ ERROR precondition might not hold
}

fn main() {}
