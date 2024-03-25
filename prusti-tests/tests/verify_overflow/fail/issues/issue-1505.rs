use prusti_contracts::*;

// To inhibit constant-propagation optimizations:
#[pure]
fn id<T: Copy>(x: T) -> T { x }

fn check_division(){
    assert!(id(3i32) / 2 == 1);
    assert!(id(-3i32) / 2 == -1);
    assert!(id(3i32) / -2 == -1);
    assert!(id(-3i32) / -2 == 1);
    prusti_assert!(id(3i32) / 2 == 1);
    prusti_assert!(id(-3i32) / 2 == -1);
    prusti_assert!(id(3i32) / -2 == -1);
    prusti_assert!(id(-3i32) / -2 == 1);

    // Smoke test
    assert!(false); //~ ERROR the asserted expression might not hold
}

fn check_modulo() {
    assert!(id(10) % 3 == 1);
    assert!(id(10) % -3 == 1);
    assert!(id(-10) % 3 == -1);
    assert!(id(-10) % -3 == -1);
    prusti_assert!(id(10) % 3 == 1);
    prusti_assert!(id(10) % -3 == 1);
    prusti_assert!(id(-10) % 3 == -1);
    prusti_assert!(id(-10) % -3 == -1);

    assert!(id(3) % 3 == 0);
    assert!(id(2) % 3 == 2);
    assert!(id(1) % 3 == 1);
    assert!(id(0) % 3 == 0);
    assert!(id(-1) % 3 == -1);
    assert!(id(-2) % 3 == -2);
    assert!(id(-3) % 3 == 0);
    assert!(id(-4) % 3 == -1);
    assert!(id(-5) % 3 == -2);
    prusti_assert!(id(3) % 3 == 0);
    prusti_assert!(id(2) % 3 == 2);
    prusti_assert!(id(1) % 3 == 1);
    prusti_assert!(id(0) % 3 == 0);
    prusti_assert!(id(-1) % 3 == -1);
    prusti_assert!(id(-2) % 3 == -2);
    prusti_assert!(id(-3) % 3 == 0);
    prusti_assert!(id(-4) % 3 == -1);
    prusti_assert!(id(-5) % 3 == -2);

    assert!(id(-4) % 2 == 0);
    prusti_assert!(id(-4) % 2 == 0);

    // Smoke test
    assert!(false); //~ ERROR the asserted expression might not hold
}

fn main(){}
