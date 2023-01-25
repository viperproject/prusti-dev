use prusti_contracts::*;

fn main() {
    let default: (i32, u64) = Default::default();
    assert!(default.0 == 0);
    assert!(default.1 == 0);

    let default: Option<Special> = Default::default();
    assert!(default.is_none());

    let default: Vec<Special> = Default::default();
    assert!(default.is_empty());

    let default = String::default();
    assert!(default.is_empty());
}

// not Copy => Default not pure
#[derive(Default)]
struct Special {
    value: i32,
}
