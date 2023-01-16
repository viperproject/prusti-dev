use prusti_contracts::*;

fn main() {
    let x = 5;
    let y = 4;
    assert!(x + y == 9);
    prusti_assert!(x + &y == 9);
    assert!(x + &y == 9);
    prusti_assert!(&x + y == 9);
    assert!(&x + y == 9);
    prusti_assert!(&x + &y == 9);
    assert!(&x + &y == 9);

    assert!(x - y == 1);
    prusti_assert!(x - &y == 1);
    assert!(x - &y == 1);
    prusti_assert!(&x - y == 1);
    assert!(&x - y == 1);
    prusti_assert!(&x - &y == 1);
    assert!(&x - &y == 1);

    prusti_assert!(&x - &y + &y == x);
    assert!(&x - &y + &y == x);
}

fn mutation() {
    let mut x = 5;
    let y = 4;
    x += &y;
    assert!(x == 9);
    x += y;
    assert!(x == 13);
}

fn bools() {
    let t = true;
    let f = false;

    assert!(t | f == true);
    prusti_assert!(t | &f == true);
    assert!(t | &f == true);
    prusti_assert!(&t & f == false);
    assert!(&t & f == false);
    prusti_assert!(&t & &f == false);
    assert!(&t & &f == false);
}
