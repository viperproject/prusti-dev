use prusti_contracts::*;

#[refine_spec([ //~ ERROR: expected `where`
    ensures(result > 0)
])]
//~| ERROR: expected a trait bound and specifications in brackets, e.g.: `ghost_constraint(T: A + B + ..., [requires(...), ...])`
fn foo<T>(_x: T) -> i32 {
    42
}

fn main() {
}
