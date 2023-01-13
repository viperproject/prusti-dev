use prusti_contracts::*;

/// External traits
trait MyTrait<T> {
    fn get_value(&self) -> T;
}
/// External traits

#[extern_spec]
trait MyTrait<T> {
    // no equality constraints yet
    #[refine_spec(where T: SpecifiedGeneric, [
        ensures(result === T::my_trait__get_value()),
    ])]
    fn get_value(&self) -> T;
}

struct Impl;
impl MyTrait<i32> for Impl {
    fn get_value(&self) -> i32 {
        42
    }
}

fn main() {
    let s = Impl {};
    assert!(MyTrait::<i32>::get_value(&s) == 42);
    assert!(s.get_value() == 42);
}

// equality constraint workaround (in the general case, this would take an `&impl MyTrait<Self>` as arg)
trait SpecifiedGeneric {
    #[pure]
    fn my_trait__get_value() -> Self;
}

impl SpecifiedGeneric for i32 {
    #[pure]
    fn my_trait__get_value() -> Self {
        42
    }
}
