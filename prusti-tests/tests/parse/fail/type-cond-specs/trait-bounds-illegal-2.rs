use prusti_contracts::*;

trait A<X> { }

#[refine_spec(where T: for<'a> A<&'a i32> [ //~ ERROR: lifetimes are not allowed in type-conditional spec refinement trait bounds
    ensures(result > 0)
])]
fn foo<T>(_x: T) -> i32 {
    42
}

fn main() {
}
