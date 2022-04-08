// compile-flags: -Penable_ghost_constraints=true

use prusti_contracts::*;

trait A {
    #[pure]
    fn a(&self) -> i32 { -1 }
}
trait B {
    #[pure]
    fn b(&self) -> i32 { -1 }
}
impl A for i32 {
    #[pure]
    fn a(&self) -> i32 { 42 }
}

impl B for i32 {
    #[pure]
    fn b(&self) -> i32 { 42 }
}

// The specs under the constraint `T: B` are also aware of the fact that `T: A` (defined on the function)
#[trusted]
#[ghost_constraint(T: B, [
    requires(x.a() == 42),
    ensures(result == x.b())
])]
fn foo<T>(x: T) -> i32 where T: A {
    x.a()
}

fn main() {
    let result = foo(1 as i32);
    assert!(result == 42);
}
