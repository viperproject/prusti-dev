use prusti_contracts::*;

fn foo() {
    let mut x = 5;
    let r_x = &mut x;
    let p_x = r_x as *mut i32;
    // Upon writing to x, p_x should become invalid because r_x becomes invalid, too
    x = 6;
    unsafe {
        // UB: p_x should be invalid
        assert!(*p_x == 6); 
    }
}