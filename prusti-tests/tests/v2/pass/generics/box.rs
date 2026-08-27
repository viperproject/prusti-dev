fn main() {
    let x = Box::new(42);
    assert!(*x == 42);

    let y = Some(Box::new(72));
    match y {
        Some(n) => assert!(*n == 72),
        None => assert!(false),
    }
}
