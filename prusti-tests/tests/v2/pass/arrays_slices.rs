use prusti_contracts::*;

#[requires(x[1] == 42)]
fn test1(x: [i32; 3]) {
    assert!(x[1] > 10);
}

fn test2(x: [i32; 3]) {
    assert!(x.len() == 3);
}

#[requires(N > 10)]
fn test3<const N: usize>(x: [i32; N]) -> i32 {
    let y: &[i32] = &x;
    y[10]
}

#[requires(x[1] == 42)]
fn test4(x: [i32; 3]) {
    let y: &[i32] = &x;
    assert!(y[1] > 10);
}

fn test5() {
    let mut x = [13, 37, 72];
    let y: &mut [i32] = &mut x;
    y[1] = 3;
    test5_2(x);
}

//#[requires(x[1] == 3)]
fn test5_2(x: [i32; 3]) {}

fn main() {
    // create arrays
    let x = [13, 37, 72];
    let mut y = [5; 42];

    // get length
    assert!(x.len() == 3);
    assert!(y.len() == 42);

    // index read
    assert!(x[1] == 37);
    assert!(x[2] == 72);
    assert!(y[10] == 5);

    // index modify
    y[10] = 72;
    assert!(y[10] == 72);
    assert!(y[11] == 5);
}
