fn main() {
    let mut a = [1, 2, 3];
    a[1] = 23;

    assert!(a[0] == 1);
    assert!(a[1] == 23);
    assert!(a[2] == 3);
}
