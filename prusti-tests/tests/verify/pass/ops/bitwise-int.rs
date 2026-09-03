use prusti_contracts::*;

fn main() {
    let x = 1;
    let y = 0;
    prusti_assert!(x & y == 0);

    let x = 1;
    let y = 4;
    prusti_assert!(x & y == 0);

    let x = 1;
    let y = 3;
    prusti_assert!(x & y == 1);

    let x = 1;
    let y = 3;
    prusti_assert!(x | y == 3);

    let x = 1;
    let y = 4;
    prusti_assert!(x | y == 5);

    let x = 1;
    let y = 0;
    prusti_assert!(x | y == 1);

    let x = 1;
    let y = 0;
    prusti_assert!(x ^ y == 1);

    let x = 1;
    let y = 1;
    prusti_assert!(x ^ y == 0);

    let x = 3;
    let y = 1;
    prusti_assert!(x ^ y == 2);

    let x = 1;
    let y = 2;
    prusti_assert!(x << y == 4);

    let x = 4;
    let y = 2;
    prusti_assert!(x >> y == 1);

    let x: u8 = 255;
    let y: u8 = 1;
    prusti_assert!(x << y == 254);

    let x: u8 = 128;
    let y: u8 = 1;
    prusti_assert!(x << y == 0);

    let x: u8 = 255;
    let y: u8 = 1;
    prusti_assert!(x >> y == 127);
}
