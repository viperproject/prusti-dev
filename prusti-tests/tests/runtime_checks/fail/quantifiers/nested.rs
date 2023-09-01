//@run: 101
use prusti_contracts::*;

#[trusted]
fn main() {
    foo(400);
}

// failing quantifier, because z + x is never 0, comparison
// would have to be z >= -x
#[insert_runtime_check]
#[requires(forall(|y: i32| (y >= 0 && y <= x) ==> exists(
    |z: i32| z > -x && z <= 0 ==> z + y == 0)
))]
fn foo(x: i32) {}
