fn main() {
    assert!(10 % 3 == 1);
    assert!(10 % -3 == 1);
    assert!(-10 % 3 == -1); // 2
    assert!(-10 % -3 == -1); // 2
    let a = 10;
    let b = 3;
    assert!(a % b == 1);

    assert!(-4 % 2 == 0);

    assert!(3 % 3 == 0);
    assert!(2 % 3 == 2);
    assert!(1 % 3 == 1);
    assert!(0 % 3 == 0);
    assert!(-1 % 3 == -1);
    assert!(-2 % 3 == -2);
    assert!(-3 % 3 == 0);
    assert!(-4 % 3 == -1);
    assert!(-5 % 3 == -2);
}
