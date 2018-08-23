extern crate prusti_contracts;

fn main() {
    assert!(10 % 3 == 1);
    assert!(10 % -3 == 1);
    assert!(-10 % 3 == -1); // 2
    assert!(-10 % -3 == -1); // 2
    let a = 10;
    let b = 3;
    assert!(a % b == 1);
}
