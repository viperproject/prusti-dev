use prusti_contracts::*;

fn main() {}

fn array_mut(mut a: [i32; 3]) {
    let a0 = a[0];
    let b = &mut a[0];
    assert!(*b == a0);
    *b = 42;
    // b expires here
    assert!(a[0] == 42);
}

fn set_if(a: &mut [i32; 4], i: usize) {
    if i < 4 {
        a[i] = 1;
        prusti_assert!(a[i] == 1);
    }
}

fn set_both(a: &mut [i32; 4], i: usize, c: bool) {
    if i < 4 {
        if c {
            a[i] = 1;
        } else {
            a[i] = 2;
        }
        prusti_assert!(a[i] > 0);
    }
}
