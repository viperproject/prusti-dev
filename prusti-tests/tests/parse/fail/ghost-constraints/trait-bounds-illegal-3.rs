use prusti_contracts::*;

struct MyStruct<T> {
    x: T,
}

impl<T> MyStruct<T> {
    #[ghost_constraint(Self: MyStruct<i32> , [ //~ ERROR: expected trait, found struct `MyStruct`
        requires(x > 0)
    ])]
    fn set_x(&mut self, x: T) {
        self.x = x;
    }
}
fn main() {
}