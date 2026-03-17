use prusti_contracts::*;
use core::mem;

#[pure]
fn from_1_to_0(ptr: *mut i32) -> *mut i32 {
    unsafe {
        if mem::offset_of!((i32, i32), 1) > mem::offset_of!((i32, i32), 0) {
            ptr.sub(mem::offset_of!((i32, i32), 1) - mem::offset_of!((i32, i32), 0))
        } else {
            ptr.add(mem::offset_of!((i32, i32), 0) - mem::offset_of!((i32, i32), 1))
        }
    }
}


fn foo() {
	let mut val = (1, 2);
	let ptr = &raw mut val.1;
	bar(ptr);
	// assert!(val.0 == 1); // would fail
 	assert!(val.1 == 2); // OK
}

#[requires(acc(*(unsafe { from_1_to_0(ptr) })))]
#[ensures(acc(*(unsafe { from_1_to_0(ptr) })))]
fn bar(ptr: *mut i32) {
    unsafe {
	    *(from_1_to_0(ptr)) = 2;
	}
}