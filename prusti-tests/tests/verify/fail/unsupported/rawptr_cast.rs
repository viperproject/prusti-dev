use prusti_contracts::*;

fn main() {
    let mut x = 5i32;
    let p_x = &raw mut x;
    let p_x = p_x as *mut i8; //~ERROR: unsupported rvalue
    unsafe {
        *p_x = 6;
    }
}
