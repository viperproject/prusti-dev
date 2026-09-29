use prusti_contracts::*;

fn main() {
    let mut x = 6;
    let mut y = 3;
    let a = return_larger(&mut x, &mut y);
    *a = 8;
    assert!(x == 8);
    assert!(y == 3);

    let mut x = 6;
    let mut y = 10;
    let a = return_larger(&mut x, &mut y);
    *a = 8;
    assert!(x == 6);
    assert!(y == 8);
}

#[after_expiry(old(*x) > old(*y) ==> before_expiry(*result) == *x && old(*y) == *y)]
#[after_expiry(old(*x) <= old(*y) ==> before_expiry(*result) == *y && old(*x) == *x)]
fn return_larger<'a>(x: &'a mut i32, y: &'a mut i32) -> &'a mut i32 {
    if *x > *y {
        &mut (*x)
    } else {
        &mut (*y)
    }
}
