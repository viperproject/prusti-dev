use prusti_contracts::prusti_assert;

// An enum with *signed* and *explicit* discriminants
enum Ordering {
    Less = -10,
    Equal = 0,
    Greater = 100,
}

fn good() {
    assert!(matches!(Ordering::Less, Ordering::Less));
    assert!(matches!(Ordering::Equal, Ordering::Equal));
    assert!(matches!(Ordering::Greater, Ordering::Greater));
    prusti_assert!(matches!(Ordering::Less, Ordering::Less));
    prusti_assert!(matches!(Ordering::Equal, Ordering::Equal));
    prusti_assert!(matches!(Ordering::Greater, Ordering::Greater));

    // Smoke test
    assert!(false); //~ ERROR: asserted expression might not hold
}

fn bad_1() {
    assert!(!matches!(Ordering::Less, Ordering::Less)); //~ ERROR: asserted expression might not hold
}

fn bad_2() {
    assert!(!matches!(Ordering::Equal, Ordering::Equal)); //~ ERROR: asserted expression might not hold
}

fn bad_3() {
    assert!(!matches!(Ordering::Greater, Ordering::Greater)); //~ ERROR: asserted expression might not hold
}

fn bad_4() {
    prusti_assert!(!matches!(Ordering::Less, Ordering::Less)); //~ ERROR: asserted expression might not hold
}

fn bad_5() {
    prusti_assert!(!matches!(Ordering::Equal, Ordering::Equal)); //~ ERROR: asserted expression might not hold
}

fn bad_6() {
    prusti_assert!(!matches!(Ordering::Greater, Ordering::Greater)); //~ ERROR: asserted expression might not hold
}

fn main() {}
