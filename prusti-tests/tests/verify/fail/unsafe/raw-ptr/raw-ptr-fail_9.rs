use prusti_contracts::*;

fn foo() {
    let mut x = 5;
    let r_x = &mut x;
    let p_x = r_x as *mut i32;
    bar(r_x);
    unsafe {
        assert!(*p_x == 5);
    }
}

fn bar(x: &mut i32) {
    *x = 6;
}
