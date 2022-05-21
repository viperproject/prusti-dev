use prusti_contracts::*;

trait Trait {
    fn do_foo(&self) -> i32;
}

#[refine_trait_spec]
impl Trait for Vec<i32> {
    #[ensures(result == 42)]
    fn do_foo(&self) -> i32 {
        42
    }
}

trait TraitWithAssocType {
    type Input;
    type Output;

    fn do_bar(&self, x: Self::Input) -> Self::Output;
}

#[refine_trait_spec]
impl TraitWithAssocType for Vec<i32> {
    type Input = i32;
    type Output = u32;

    #[requires(x > 0)]
    #[ensures(result > 1)]
    fn do_bar(&self, x: Self::Input) -> Self::Output {
        let y: u32 = x as u32;
        y + 1
    }
}

fn main() {
    let v = Vec::new();
    let result = v.do_foo();
    assert!(result == 42);

    let result = v.do_bar(42);
    assert!(result > 1);
}