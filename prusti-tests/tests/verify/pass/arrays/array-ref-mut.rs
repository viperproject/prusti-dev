fn main() {}

fn array_mut(mut a: [i32; 3]) {
    let a0 = a[0];
    let b = &mut a[0];
    assert!(*b == a0);
    *b = 42;
    // b expires here
    assert!(a[0] == 42);
}
