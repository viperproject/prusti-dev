use prusti_contracts::*;

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
