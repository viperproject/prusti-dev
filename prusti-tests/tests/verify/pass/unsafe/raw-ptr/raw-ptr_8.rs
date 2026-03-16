use prusti_contracts::*;
//use core::mem;

// fn foo() {
// 	let mut val = (1, 2);
// 	let ptr = &raw mut val.1;
// 	bar(ptr, mem::offset_of!((u32, u32), 1) - mem::offset_of!((u32, u32), 0));
// 	// assert!(val.0 == 1); // would fail
//  	assert!(val.1 == 2); // OK
// }

#[requires(acc(*(unsafe { ptr.sub(offset) })))]
//#[ensures(acc(*(unsafe { ptr.sub(offset) })))]
fn bar(ptr: *mut i32, offset: usize) {
    // unsafe {
	//     *(ptr.sub(offset / size_of::<i32>())) = 2;
	// }
}