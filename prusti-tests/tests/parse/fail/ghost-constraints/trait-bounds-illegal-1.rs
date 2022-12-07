use prusti_contracts::*;

trait A { }

#[refine_spec(where T: 'static + A [ //~ ERROR: lifetimes are not allowed in ghost constraint trait bounds
    ensures(result > 0)
])]
fn foo<T>(_x: T) -> i32 {
    42
}

fn main() {
}
