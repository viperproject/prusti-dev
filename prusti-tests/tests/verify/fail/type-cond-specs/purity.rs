use prusti_contracts::*;

#[refine_spec(where T: Copy, [pure])]
#[trusted]
fn test<T>(_t: T) -> bool {
    true
}

#[derive(PartialEq, Eq)]
struct Copyrighted; // not Copy

fn main() {
    prusti_assert!(test(Copyrighted) == test(Copyrighted)); //~ ERROR: [Prusti: invalid specification] use of impure function "test" in pure code is not allowed
}
