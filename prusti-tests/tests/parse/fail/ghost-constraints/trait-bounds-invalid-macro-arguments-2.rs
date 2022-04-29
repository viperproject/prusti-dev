use prusti_contracts::*;

#[ghost_constraint(42, [ //~ ERROR: Could not parse trait bounds
    ensures(result > 0)
])]
fn foo<T>(_x: T) -> i32 {
    42
}

fn main() {
}
