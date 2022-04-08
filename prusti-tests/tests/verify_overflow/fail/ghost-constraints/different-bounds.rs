// compile-flags: -Penable_ghost_constraints=true

// Note: For now, it is completely fine to _declare_ two ghost constraints with different bounds
// since resolving happens for specific callsites. That is, without the call in main, this
// file verifies.
use prusti_contracts::*;

trait A {}
trait B {}

#[trusted]
#[ghost_constraint(T: A, [ //~ ERROR: [Prusti: unsupported feature] Multiple ghost constraints with different bounds defined
    requires(true),
    ensures(true),
])]
#[ghost_constraint(T: B, [
    requires(true),
    ensures(true),
])]
fn foo<T>(_x: T) {
}

fn main() {
    foo::<i32>(42);
}
