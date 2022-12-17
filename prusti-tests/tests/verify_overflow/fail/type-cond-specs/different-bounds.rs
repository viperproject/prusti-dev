// Note: For now, it is completely fine to _declare_ two type-conditional spec refinements with different bounds
// since resolving happens for specific callsites. That is, without the call in main, this
// file verifies.
use prusti_contracts::*;

trait A {}
trait B {}

#[trusted]
#[refine_spec(where T: A, [ //~ ERROR: [Prusti: unsupported feature] Multiple type-conditional spec refinements with different bounds defined
    requires(true),
    ensures(true),
])]
#[refine_spec(where T: B, [
    requires(true),
    ensures(true),
])]
fn foo<T>(_x: T) {
}

fn main() {
    foo::<i32>(42);
}
