// compile-flags: -Penable_ghost_constraints=true

use prusti_contracts::*;

#[ghost_constraint(T: Copy, [pure])]
#[trusted]
fn test<T>(_t: T) -> bool { true }

fn main() {
	assert!(test(5) == test(5));
}
