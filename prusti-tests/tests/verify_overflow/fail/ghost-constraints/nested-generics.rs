// compile-flags: -Penable_ghost_constraints=true

use prusti_contracts::*;

trait A {}
trait B<X> {}
trait C<Y> {}

impl A for i32 {}
// impl B<i32> for i32 {}
impl B<u32> for i32 {}

#[trusted]
#[ghost_constraint(T: A + B<i32> + B<u32> , [
    ensures(result > 0)
])]
fn foo<T>(_x: T) -> i32 {
    42
}

fn main() {
    let result = foo(1);
    assert!(result > 0); //~ ERROR: [Prusti: verification error] the asserted expression might not hold
}
