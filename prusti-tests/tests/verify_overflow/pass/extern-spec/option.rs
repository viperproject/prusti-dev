use prusti_contracts::*;

fn main() {
    let mut x = Some(3);
    assert!(x.is_some());
    x = None;
    assert!(x.is_none());
}
