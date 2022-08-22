use prusti_contracts::*;

#[ghost_constraint([ //~ ERROR: expected `,`
    ensures(result > 0)
])]
fn foo<T>(_x: T) -> i32 {
    42
}

fn main() {
}
