//@run: 101
use prusti_contracts::*;

fn main() {
    let mut x = GenericStruct { x: 40};
    let mut y = GenericStruct { x: 32};
    let c = x.stuff(&mut y);
}

#[derive(Clone)]
struct GenericStruct<T> {
    pub x: T,
}

impl<T: PartialEq + Copy + std::ops::Add<Output=T>> GenericStruct<T> {
    #[trusted]
    // fails because of the +1
    #[insert_runtime_check]
    #[ensures(self.x == old(other.x))]
    #[insert_runtime_check]
    #[ensures(other.x == old(self.x))]
    pub fn stuff(&mut self, other: &mut Self) {
        std::mem::swap(&mut self.x, &mut other.x);
        // make check fail:
        self.x = self.x + other.x;
    }
}

