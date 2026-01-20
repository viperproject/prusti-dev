use prusti_contracts::*;

fn foo() {
    let mut x = 5;
    let r_x = &mut x;
    let p_x = r_x as *mut i32;
    // Upon writing to r_x, p_x should become invalid because the aliasing rules of r_x
    // require r_x to be unique
    *r_x = 6;
    unsafe {
        // UB: p_x should be invalid
        assert!(*p_x == 6); 
    }
}