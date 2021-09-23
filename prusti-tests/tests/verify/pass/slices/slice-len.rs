use prusti_contracts::*;

fn main() {}

#[requires(a.len() > 5)]
fn slice(a: &[i32]) {
    let s = &a[1..4];
    assert!(s.len() == 3);
    let s = &a[..2];
    assert!(s.len() == 2);
    let s = &a[1..];
    assert!(s.len() == a.len()-1);
    let s = &a[..];
    assert!(s.len() == a.len());
    // Unsupported
    //let s = &a[1..=4];
    //assert!(s.len() == 4);
    let s = &a[..=4];
    assert!(s.len() == 5);
}
