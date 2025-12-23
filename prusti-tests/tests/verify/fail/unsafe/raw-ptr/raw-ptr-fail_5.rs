use prusti_contracts::*;

fn foo() {
    let mut x = 5;
    let mut r_x = &mut x;
    let p_r_x = &raw mut r_x;
    let p_r_x_2 = &raw mut r_x;
    bar(p_r_x_2);
    unsafe {
        assert!(**p_r_x == 5); //should fail
    }
}

#[requires(acc!(*x))]
#[ensures(acc!(*x))]
fn bar(x: *mut &mut i32) {}