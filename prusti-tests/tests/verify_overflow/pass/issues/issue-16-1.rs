use prusti_contracts::*;

trait Val {
    #[pure]
    fn value(&self) -> i32;
}

struct Foo<T> {
    x: T,
}

impl<T: Val> Foo<T> {
    fn get(&self) -> i32 {
        self.x.value()
    }
}

#[requires(x.value() > 0)]
fn use_val_in_spec<T: Val>(x: &T) {}

#[trusted]
fn main() {}
