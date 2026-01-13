use prusti_contracts::*;

fn bar(x: *mut i32) -> i32 {
    unsafe {
        *x
    }
}