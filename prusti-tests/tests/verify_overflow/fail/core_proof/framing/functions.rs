// compile-flags: -Punsafe_core_proof=true -Penable_type_invariants=true

#![deny(unsafe_op_in_unsafe_fn)]

use prusti_contracts::*;

#[structural_invariant(!self.p.is_null() ==> own!(*self.p))]
struct T1 {
    p: *mut i32,
}

#[pure]
fn test1_get_p(x: &T1) -> i32 {
    if self.p.is_null() {
        0
    } else {
        unsafe { *self.p }
    }
}


#[trusted]
#[requires(align > 0)]
#[ensures(!result.is_null() ==> (
    raw!(*result, size) &&
    raw_dealloc!(*result, size, align)
))]
// https://doc.rust-lang.org/alloc/alloc/fn.alloc.html
unsafe fn alloc(size: usize, align: usize) -> *mut u8 {
    unimplemented!();
}

#[trusted]
#[requires(
    raw!(*ptr, size) &&
    raw_dealloc!(*ptr, size, align)
)]
unsafe fn dealloc(ptr: *mut u8, size: usize, align: usize) {
    unimplemented!();
}

struct Pair {
    x: i32,
    y: i32,
}

fn main() {}
