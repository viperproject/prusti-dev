use prusti_contracts::*;

trait A { }

#[refine_spec(where T: 'static + A, [ //~ ERROR: lifetimes are not allowed in type-conditional spec refinement trait bounds
    ensures(result > 0)
])]
fn foo<T>(_x: T) -> i32 {
    42
}

fn main() {
}
