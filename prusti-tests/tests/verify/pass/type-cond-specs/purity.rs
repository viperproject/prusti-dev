use prusti_contracts::*;

#[refine_spec(where T: Copy, [pure])]
#[trusted]
fn test<T>(_t: T) -> bool {
    true
}

fn main() {
    assert!(test(5) == test(5));
}
