use prusti_contracts::*;

fn main() {
    let mut x = 5;
    let p_x = &raw const x;
    let p_x = p_x as *mut i32;
    unsafe {
        *p_x = 6;
    }
    prusti_assert!(x == 6);
}
