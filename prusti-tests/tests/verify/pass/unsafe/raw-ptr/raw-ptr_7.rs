use prusti_contracts::*;

fn foo() {
    let mut x = 5;
    let r_x = &x;
    let p_x = (r_x as *const i32) as *mut i32;
    bar(p_x);
    unsafe {
        assert!(*p_x == 5); 
    }
}

#[requires(acc(*x, 1/2))]
#[ensures(acc(*x, 1/2))]
fn bar(x: *mut i32) {}