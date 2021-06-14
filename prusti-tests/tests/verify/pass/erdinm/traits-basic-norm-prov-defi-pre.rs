use prusti_contracts::*;

trait Percentage {
    #[requires(arg <= 100)]
    fn set(&mut self, arg: u8) {
        assert!(arg <= 100);
    }
}

fn main() {}
