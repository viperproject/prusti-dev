use prusti_contracts::*;

trait Trait {
    #[pure]
    fn foo(&self) -> i32;
}

struct Foo<T>(std::marker::PhantomData<T>);
impl<T> Trait for Foo<T> {
    #[pure]
    fn foo(&self) -> i32 {
        42
    }
}

#[requires(arg.foo() == 42)]
fn verify_in_precondition<T>(arg: &Foo<T>) {
}

fn main() {
    let f = Foo::<u32>(std::marker::PhantomData);
    assert!(f.foo() == 42);
    verify_in_precondition(&f);

    let f = Foo::<i32>(std::marker::PhantomData);
    assert!(f.foo() == 42);
    verify_in_precondition(&f);
}