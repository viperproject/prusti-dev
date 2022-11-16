use prusti_contracts::*;

#[ghost_constraint([
    ensures(result > 0) //~ ERROR: expected `,`
])]
//~| ERROR: expected a trait bound and specifications in brackets, e.g.: `ghost_constraint(T: A + B + ..., [requires(...), ...])`
fn foo<T>(_x: T) -> i32 {
    42
}

fn main() {
}
