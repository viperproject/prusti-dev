use prusti_contracts::*;

trait Trait<X> {
    #[pure]
    fn foo(&self) -> i32;
}

struct Foo<U, V>(std::marker::PhantomData<U>, std::marker::PhantomData<V>);
impl<U, V, W> Trait<W> for Foo<U, V> {
    #[pure]
    fn foo(&self) -> i32 {
        42
    }
}

// Assuming function is called with T0,T1,T2, encoder should be smart enough to map
// A->U->T0, B->U->T1, C->X->T2
#[requires(Trait::<C>::foo(arg) == 42)]
fn verify_generic_precondition_1<A,B,C>(arg: &Foo<A,B>) {
}

// Generics in function have same name as generics in trait impl
#[requires(Trait::<W>::foo(arg) == 42)]
fn verify_generic_precondition_2<U,V,W>(arg: &Foo<U,V>) {
}

fn main() {
    let f = Foo::<u32, i32>(std::marker::PhantomData, std::marker::PhantomData);
    assert!(Trait::<usize>::foo(&f) == 42);
    verify_generic_precondition_1::<u32, i32, usize>(&f);
    verify_generic_precondition_2::<u32, i32, usize>(&f);

    let f = Foo::<i32, u32>(std::marker::PhantomData,std::marker::PhantomData);
    assert!(Trait::<usize>::foo(&f) == 42);
    verify_generic_precondition_1::<i32, u32, usize>(&f);
    verify_generic_precondition_2::<i32, u32, usize>(&f);
}