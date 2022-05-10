use prusti_contracts::*;

trait Foo {
    type Type;

    #[pure]
    fn foo(&self) -> Self::Type;
}

struct Bar;
impl Foo for Bar {
    type Type = i32;

    #[pure]
    fn foo(&self) -> Self::Type {
        42
    }
}

struct Baz<T: Copy>(std::marker::PhantomData<T>);
impl<T: Copy> Foo for Baz<T> {
    type Type = T;

    #[pure]
    #[trusted]
    fn foo(&self) -> Self::Type {
        unimplemented!()
    }
}

fn main() {

}