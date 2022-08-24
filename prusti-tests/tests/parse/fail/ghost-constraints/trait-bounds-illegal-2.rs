use prusti_contracts::*;

trait A<X> { }

#[ghost_constraint(T: for<'a> A<&'a i32>, [ //~ ERROR: lifetimes are not allowed in ghost constraint trait bounds
    ensures(result > 0)
])]
//~| ERROR: expected a trait bound and specifications in brackets, e.g.: `ghost_constraint(T: A + B + ..., [requires(...), ...])`
fn foo<T>(_x: T) -> i32 {
    42
}

fn main() {
}
