use prusti_contracts::*;

struct MyWrapper(u32);

impl MyWrapper {
    #[pure]
    #[ensures(old(self.0) == self.0)]
    fn unwrap(&self) -> u32 { //~ ERROR old expressions should not appear in the postconditions of pure functions
        self.0
    }
}

fn test(x: &MyWrapper) -> u32 {
    // Following error is due to stub encoding of invalid spec for function `unwrap()`
    x.unwrap() //~ ERROR precondition of pure function call might not hold
}

fn main() { }
