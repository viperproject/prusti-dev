use prusti_contracts::*;

trait A<X> { }

#[ghost_constraint(T: for<'a> A<&'a i32> , [ //~ ERROR: Lifetimes in ghost constraints not allowed
    ensures(result > 0)
])]
fn foo<T>(_x: T) -> i32 {
    42
}

fn main() {
}
