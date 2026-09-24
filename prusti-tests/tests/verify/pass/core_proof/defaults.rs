use prusti_contracts::*;

fn integers() {
    let a: i32 = Default::default();
    let b: u64 = Default::default();
    let c: usize = usize::default();
    assert!(a == 0 && b == 0 && c == 0);
}

fn primitives() {
    let b: bool = Default::default();
    let c: char = Default::default();
    let u: () = Default::default();
    let f: f64 = Default::default();
    assert!(!b);
    assert!(c == '\0');
    assert!(u == ());
    assert!(f == 0.0);
}

fn option() {
    let o: Option<i32> = Default::default();
    assert!(matches!(o, None));
}

fn slice() {
    let s: &[u8] = Default::default();
    assert!(s.len() == 0);
}

fn tuples() {
    let t: (i32, bool) = Default::default();
    assert!(t.0 == 0);
    assert!(!t.1);
    let u: (u8, (), char) = Default::default();
    assert!(u.0 == 0);
    assert!(u.2 == '\0');
}
