use prusti_contracts::*;

trait A { }

#[ghost_constraint(T: 'static + A, [ //~ ERROR: Lifetimes in ghost constraints not allowed
    ensures(result > 0)
])]
fn foo<T>(_x: T) -> i32 {
    42
}

fn main() {
}
