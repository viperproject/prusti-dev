// compile-flags: -Punsafe_core_proof=true -Penable_type_invariants=true

#![deny(unsafe_op_in_unsafe_fn)]

use prusti_contracts::*;

#[ensures(!result.is_null() ==> unsafe { *result } == 5)]   //~ ERROR: the place must be framed by permissions
fn test01_safe() -> *mut i32 {
    let p_alloc = unsafe {
        alloc(std::mem::size_of::<i32>(), std::mem::align_of::<i32>())
    };
    let p = (p_alloc as *mut i32);
    if !p.is_null() {
        unsafe { *p = 5; }
    }
    p
}

#[ensures(!result.is_null() ==> own!(*result) && unsafe { *result } == 5)]   //~ ERROR: only unsafe functions can use permissions in their contracts
fn test02_safe() -> *mut i32 {
    let p_alloc = unsafe {
        alloc(std::mem::size_of::<i32>(), std::mem::align_of::<i32>())
    };
    let p = (p_alloc as *mut i32);
    if !p.is_null() {
        unsafe { *p = 5; }
    }
    p
}

#[ensures(!result.is_null() ==> own!(*result) && unsafe { *result } == 5)]
unsafe fn test03_unsafe() -> *mut i32 {
    let p_alloc = unsafe {
        alloc(std::mem::size_of::<i32>(), std::mem::align_of::<i32>())
    };
    let p = (p_alloc as *mut i32);
    if !p.is_null() {
        unsafe { *p = 5; }
    }
    p
}

#[ensures(!result.is_null() ==> own!(*result) && unsafe { *result } == 6)]  //~ ERROR: postcondition might not hold.
unsafe fn test04_unsafe() -> *mut i32 {
    let p_alloc = unsafe {
        alloc(std::mem::size_of::<i32>(), std::mem::align_of::<i32>())
    };
    let p = (p_alloc as *mut i32);
    if !p.is_null() {
        unsafe { *p = 5; }
    }
    p
}

unsafe fn test05_unsafe() -> *mut i32 {
    let p_alloc = unsafe {
        alloc(std::mem::size_of::<i32>(), std::mem::align_of::<i32>())
    };
    let p = (p_alloc as *mut i32);
    unsafe { *p = 5; }  //~ ERROR: the accessed memory location must be allocated and uninitialized
    p
}

#[ensures(own!(*result))]
unsafe fn test06_unsafe() -> *mut i32 {  //~ ERROR: there might be insufficient permission to dereference a raw pointer
    let p_alloc = unsafe {
        alloc(std::mem::size_of::<i32>(), std::mem::align_of::<i32>())
    };
    let p = (p_alloc as *mut i32);
    if !p.is_null() {
        unsafe { *p = 5; }
    }
    p
}

unsafe fn test07_unsafe() -> *mut i32 {
    let p_alloc = unsafe {
        alloc(std::mem::size_of::<i32>(), std::mem::align_of::<i32>())
    };
    let p = (p_alloc as *mut i32);
    if !p.is_null() {
        unsafe { *p = 5; }
        assert!(unsafe { *p } == 5);
    }
    p
}

fn test07_safe() -> *mut i32 {
    let p_alloc = unsafe {
        alloc(std::mem::size_of::<i32>(), std::mem::align_of::<i32>())
    };
    let p = (p_alloc as *mut i32);
    if !p.is_null() {
        unsafe { *p = 5; }
        assert!(unsafe { *p } == 5);
    }
    p
}

fn callee() {}

unsafe fn test08_unsafe() -> *mut i32 {
    let p_alloc = unsafe {
        alloc(std::mem::size_of::<i32>(), std::mem::align_of::<i32>())
    };
    let p = (p_alloc as *mut i32);
    if !p.is_null() {
        unsafe { *p = 5; }
        callee();
        assert!(unsafe { *p } == 5);
    }
    p
}

fn test08_safe() -> *mut i32 {
    let p_alloc = unsafe {
        alloc(std::mem::size_of::<i32>(), std::mem::align_of::<i32>())
    };
    let p = (p_alloc as *mut i32);
    if !p.is_null() {
        unsafe { *p = 5; }
        callee();
        // Calling non-pure functions havoc the heap when in permissions
        // are disabled:
        assert!(unsafe { *p } == 5);   //~ ERROR: the type invariant of the constructed object might not hold
                                       //^ ERROR: the type invariant of the constructed object might not hold
    }
    p
}

#[pure]
#[terminates]
fn pure_callee() {}

unsafe fn test09_unsafe() -> *mut i32 {
    let p_alloc = unsafe {
        alloc(std::mem::size_of::<i32>(), std::mem::align_of::<i32>())
    };
    let p = (p_alloc as *mut i32);
    if !p.is_null() {
        unsafe { *p = 5; }
        pure_callee();
        assert!(unsafe { *p } == 5);
    }
    p
}

fn test09_safe() -> *mut i32 {
    let p_alloc = unsafe {
        alloc(std::mem::size_of::<i32>(), std::mem::align_of::<i32>())
    };
    let p = (p_alloc as *mut i32);
    if !p.is_null() {
        unsafe { *p = 5; }
        pure_callee();
        assert!(unsafe { *p } == 5);
    }
    p
}

#[ensures(!result.0.is_null() ==> unsafe { *result.0 } == 5)]   //~ ERROR: the place must be framed by permissions
fn test11_safe() -> (*mut i32, *mut i32) {
    let p_alloc = unsafe {
        alloc(std::mem::size_of::<i32>(), std::mem::align_of::<i32>())
    };
    let p = (p_alloc as *mut i32);
    if !p.is_null() {
        unsafe { *p = 5; }
    }
    (p, p)
}

#[ensures(!result.0.is_null() ==> own!(*result.0) && unsafe { *result.0 } == 5)]   //~ ERROR: only unsafe functions can use permissions in their contracts
fn test12_safe() -> (*mut i32, *mut i32) {
    let p_alloc = unsafe {
        alloc(std::mem::size_of::<i32>(), std::mem::align_of::<i32>())
    };
    let p = (p_alloc as *mut i32);
    if !p.is_null() {
        unsafe { *p = 5; }
    }
    (p, p)
}

#[ensures(!result.0.is_null() ==> own!(*result.0) && unsafe { *result.0 } == 5)]
unsafe fn test13_unsafe() -> (*mut i32, *mut i32) {
    let p_alloc = unsafe {
        alloc(std::mem::size_of::<i32>(), std::mem::align_of::<i32>())
    };
    let p = (p_alloc as *mut i32);
    if !p.is_null() {
        unsafe { *p = 5; }
    }
    (p, p)
}

// Note: This works and `test14_unsafe_semantic_aliasing` fails because
// framing of unsafe function postconditions is done by Viper.
#[ensures(result.0 == result.1)]
#[ensures(!result.0.is_null() ==> own!(*result.0) && unsafe { *result.1 } == 5)]
unsafe fn test13_unsafe_semantic_aliasing() -> (*mut i32, *mut i32) {
    let p_alloc = unsafe {
        alloc(std::mem::size_of::<i32>(), std::mem::align_of::<i32>())
    };
    let p = (p_alloc as *mut i32);
    if !p.is_null() {
        unsafe { *p = 5; }
    }
    (p, p)
}

#[ensures(!result.0.is_null() ==> own!(*result.0) && unsafe { *result.1 } == 5)]    //~ ERROR: the postcondition might not be self-framing.
unsafe fn test14_unsafe_semantic_aliasing() -> (*mut i32, *mut i32) {
    let p_alloc = unsafe {
        alloc(std::mem::size_of::<i32>(), std::mem::align_of::<i32>())
    };
    let p = (p_alloc as *mut i32);
    if !p.is_null() {
        unsafe { *p = 5; }
    }
    (p, p)
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

fn main() {}
