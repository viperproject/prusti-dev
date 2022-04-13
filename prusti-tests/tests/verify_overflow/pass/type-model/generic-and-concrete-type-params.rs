use prusti_contracts::*;

struct Foo<A, B, C>(
    std::marker::PhantomData<A>,
    std::marker::PhantomData<B>,
    std::marker::PhantomData<C>
);

#[model]
struct Foo<#[generic] A: Copy, #[concrete] i32, #[concrete] u32> {
    fld_a: A,
}

#[trusted]
#[ensures(result.model().fld_a == model_val)]
fn create_foo<A: Copy+PartialEq>(model_val: A) -> Foo<A,i32, u32>{
    Foo::<A, i32, u32> (std::marker::PhantomData, std::marker::PhantomData, std::marker::PhantomData)
}

#[trusted]
#[requires(foo.model().fld_a == model_val)]
fn verify_model<A: Copy+PartialEq>(foo: &Foo<A, i32, u32>, model_val: A) {
}

fn main() {
    let foo_i32 = create_foo(123 as i32);
    verify_model(&foo_i32, 123);

    let foo_u32 = create_foo(123 as u32);
    verify_model(&foo_u32, 123);
}