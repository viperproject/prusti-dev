// compile-flags: -Penable_ghost_constraints=true

use prusti_contracts::*;

#[ghost_constraint(T: Copy, [pure])]
#[trusted]
fn test<T>(_t: T) -> bool { true }

#[derive(Clone, PartialEq, Eq)]
struct Copyrighted; // not Copy

fn main() {
	prusti_assert!(test(Copyrighted) == test(Copyrighted)); //~ ERROR: [Prusti: invalid specification] use of impure function "test" in pure code is not allowed
}
