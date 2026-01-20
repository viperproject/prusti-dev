use prusti_contracts::*;

fn foo() {
    let mut x = 5;
    let p_x = &raw mut x;
    let r_x_1 = &x;
    let r_x_2 = &x;
    unsafe {
        *p_x = 6;
    }
    assert!(*r_x_1 == 5);
}