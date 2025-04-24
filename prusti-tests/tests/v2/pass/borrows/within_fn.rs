fn ints() {
    let x = 42;
    let y = &x;
    assert!(*y == 42);
    assert!(x == 42);
}

fn bools() {
    let x = true;
    let y = &x;
    assert!(*y == true);
    assert!(x == true);
}

fn main() {}
