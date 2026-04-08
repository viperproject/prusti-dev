use prusti_contracts::*;

fn main() {
    let x = bar();
    unsafe {
        assert!(*x == 5);
    }
}


#[ensures(acc(*result))]
#[ensures(unsafe { *result == 5 })]
fn bar() -> *mut i32 {
    let mut x = 5;
    &raw mut x
}