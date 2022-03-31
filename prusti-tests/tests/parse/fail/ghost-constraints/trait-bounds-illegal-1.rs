use prusti_contracts::*;

trait A { type Item; }

#[ghost_constraint(T: A<Item = i32>, [ //~ ERROR: Trait bounds can only have type bindings
    ensures(result > 0)
])]
fn foo<T>(_x: T) -> i32 {
    42
}

fn main() {
}
