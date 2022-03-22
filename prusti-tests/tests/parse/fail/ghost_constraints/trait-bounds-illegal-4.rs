// TODO hansenj: Parser error
use prusti_contracts::*;

trait A { }
trait B { }

#[ghost_constraint(T: Fn(A) -> B , [ //~ ERROR: unexpected Prusti syntax
    ensures(result > 0)
])]
fn foo<T>(_x: T) -> i32 {
    42
}

fn main() {
}
