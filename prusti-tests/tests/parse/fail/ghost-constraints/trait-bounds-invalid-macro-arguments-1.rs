use prusti_contracts::*;

#[ghost_constraint([ //~ ERROR: Invalid use of macro. Two arguments expected (a trait bound `T: A + B` and multiple specifications `[requires(...), ensures(...), ...]`)
    ensures(result > 0)
])]
fn foo<T>(_x: T) -> i32 {
    42
}

fn main() {
}
