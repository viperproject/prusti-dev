//@run: 101
use prusti_contracts::*;

fn main() {
    let a: i32 = 50;
    let x = GenericStruct { x: a};
    let y = GenericStruct { x: a};
    let c = x.stuff(&y);
}

#[derive(Clone)]
struct GenericStruct<T> {
    pub x: T,
}

impl GenericStruct<i32> {
    #[trusted]
    // fails because of the +1
    #[insert_runtime_check]
    #[ensures(result == self.x + other.x + 1)]
    pub fn stuff(&self, other: &Self) -> i32 {
        self.x + other.x
    }
}

