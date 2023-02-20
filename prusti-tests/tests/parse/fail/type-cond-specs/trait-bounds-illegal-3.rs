use prusti_contracts::*;

struct MyStruct<T> {
    x: T,
}

impl<T> MyStruct<T> {
    #[refine_spec(where elf: MyStruct<i32>, [ //~ ERROR: expected trait, found struct `MyStruct`
        requires(x > 0)
    ])]
    //~| ERROR: cannot find type `elf` in this scope [E0412]
    fn set_x(&mut self, x: T) {
        self.x = x;
    }
}
fn main() {
}
