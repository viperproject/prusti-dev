// compile-flags: -Pviper_backend=Lithium
use prusti_contracts::*;

pub struct MyStructure {}

impl MyStructure {
    #[pure]
    #[terminates]
    #[ensures (0 <= result)]
    pub fn len(&self) -> i32 {
        17
    }
}

#[pure]
#[terminates]
#[ensures (0 <= result)]
#[ensures(result == s.len())]
fn len_of(s: &MyStructure) -> i32 {
    17
}

#[ensures(forall(|s: MyStructure| len_of(&s) >= 0))]
#[ensures(forall(|s: MyStructure| s.len() >= 10))]
fn test(min: i32) {}

fn main() {}
