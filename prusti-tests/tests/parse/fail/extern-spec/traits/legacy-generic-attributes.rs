use prusti_contracts::*;

/// External traits
trait MyTrait<T> {
    fn get_value(&self) -> T;
}
/// External traits

#[extern_spec]
trait MyTrait<#[concrete] i32> {
    //~^ ERROR: The `#[concrete]` and `#[generic]` attributes are deprecated. To refine specs for specific concrete types, use type-conditional spec refinements instead.
    #[ensures(result == 42)]
    fn get_value(&self) -> i32;
}

#[extern_spec]
trait MyTrait<#[generic] T> {
    //~^ ERROR: The `#[concrete]` and `#[generic]` attributes are deprecated. To refine specs for specific concrete types, use type-conditional spec refinements instead.
    #[ensures(true)]
    fn get_value(&self) -> T;
}

fn main() {}
