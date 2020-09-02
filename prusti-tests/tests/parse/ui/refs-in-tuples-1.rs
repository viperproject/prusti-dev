fn main() {
    let mut x = 0;
    let mut y = 1;

    let xy = (&mut x, &mut y);
    assert!(*xy.0 == 0);
    assert!(*xy.1 == 1);

    let a = xy.0;
    let b = xy.1;

    *a = 2;
    assert!(*a == 2);
    assert!(x == 2);

    *b = 3;
    assert!(*b == 3);
    assert!(y == 3);
}
