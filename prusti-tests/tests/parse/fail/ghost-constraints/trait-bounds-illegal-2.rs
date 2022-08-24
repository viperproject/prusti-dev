use prusti_contracts::*;

trait A<X> { }

#[ghost_constraint(T: for<'a> A<&'a i32>, [ //~ ERROR: lifetimes are not allowed in ghost constraint trait bounds
    ensures(result > 0)
])]
//~| ERROR: expected a trait bound `T: A + B` and specifications in brackets `[requires(...), ensures(...), pure, ...]`
fn foo<T>(_x: T) -> i32 {
    42
}

fn main() {
}
