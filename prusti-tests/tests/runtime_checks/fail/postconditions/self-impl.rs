//@run: 101
use prusti_contracts::*;

#[trusted]
fn main() {
    let mut yxe = Something::new();
    yxe.increment();
    println!("getting to the end");
}

#[derive(Clone)]
struct Something {
    x: i32,
}

impl Something {
    pub fn new() -> Self {
        Self {
            x: 5,
        }
    }

    #[trusted]
    // failing postcondition
    #[insert_runtime_check]
    #[ensures(old(self.x) == self.x)]
    pub fn increment(&mut self) {
        self.x += 1;
    }
}
