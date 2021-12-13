// Fixed by https://github.com/viperproject/prusti-dev/pull/777
use prusti_contracts::*;

#[pure]
fn pure_fn() -> bool { true }
//#[pure]
//fn pure_fn_generics<T: ?Sized>() -> bool { true }

trait Trait {
    #[requires(pure_fn())]
    //#[ensures(pure_fn_generics::<Self>())]
    fn foo();
}

struct Struct;
impl Trait for Struct {
    fn foo() {}
}

fn main() {
    Struct::foo();
}