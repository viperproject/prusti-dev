use prusti_contracts::*;

trait TraitWithAssocType {
    type Input;
    type Output;

    fn do_something(&self, x: Self::Input) -> Self::Output;
}

struct Foo;

#[refine_trait_spec]
impl TraitWithAssocType for Foo {
    type Input = i32;
    type Output = u32;

    #[requires(x > 0)]
    #[ensures(result > 1)]
    fn do_something(&self, x: Self::Input) -> Self::Output {
        let y: u32 = x as u32;
        y + 1
    }
}

fn main() {
    let v = Foo;
    let result = v.do_something(42);
    assert!(result > 1);
}