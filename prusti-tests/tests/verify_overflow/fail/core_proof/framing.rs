// compile-flags: -Punsafe_core_proof=true -Penable_type_invariants=true

#![deny(unsafe_op_in_unsafe_fn)]

use prusti_contracts::*;

// TODO: Check only on the definition side. Add tests.

//#[ensures(!result.is_null() ==> own!((*result).x) && unsafe { (*result).x } == 5)]
//unsafe fn test01() -> *mut Pair {
    //let p = unsafe {
        //alloc(std::mem::size_of::<Pair>(), std::mem::align_of::<Pair>())
    //};
    //let pair = (p as *mut Pair);
    //if !pair.is_null() {
        //split!(*pair);
        //unsafe { (*pair).x = 5; }
    //}
    //pair
//}

//#[ensures(!result.is_null() ==> unsafe { (*result).x } == 5)]   //~ ERROR: the place must be framed by permissions
//unsafe fn test01_non_framed() -> *mut Pair {
    //let p = unsafe {
        //alloc(std::mem::size_of::<Pair>(), std::mem::align_of::<Pair>())
    //};
    //let pair = (p as *mut Pair);
    //if !pair.is_null() {
        //split!(*pair);
        //unsafe { (*pair).x = 5; }
    //}
    //pair
//}

//#[ensures(!result.is_null() ==> own!(*result) && unsafe { (*result).x } == 5)]
//unsafe fn test02() -> *mut Pair {
    //let p = unsafe {
        //alloc(std::mem::size_of::<Pair>(), std::mem::align_of::<Pair>())
    //};
    //let pair = (p as *mut Pair);
    //if !pair.is_null() {
        //split!(*pair);
        //unsafe { (*pair).y = 4; }
        //unsafe { (*pair).x = 5; }
        //pack!(*pair);
    //}
    //pair
//}

//#[ensures(!result.is_null() ==> own!(*result) && unsafe { (*result).x } == 5)]
//unsafe fn test02_missing_pack() -> *mut Pair {  //~ ERROR: there might be insufficient permission to dereference a raw pointer
    //let p = unsafe {
        //alloc(std::mem::size_of::<Pair>(), std::mem::align_of::<Pair>())
    //};
    //let pair = (p as *mut Pair);
    //if !pair.is_null() {
        //split!(*pair);
        //unsafe { (*pair).y = 4; }
        //unsafe { (*pair).x = 5; }
    //}
    //pair
//}

//#[ensures(!result.is_null() ==> unsafe { (*result).x } == 5)]   //~ ERROR: there might be insufficient permission to dereference a raw pointer
                    ////^ ERROR: the postcondition might not be self-framing
//unsafe fn test02_non_framed() -> *mut Pair {
    //let p = unsafe {
        //alloc(std::mem::size_of::<Pair>(), std::mem::align_of::<Pair>())
    //};
    //let pair = (p as *mut Pair);
    //if !pair.is_null() {
        //split!(*pair);
        //unsafe { (*pair).y = 4; }
        //unsafe { (*pair).x = 5; }
        //pack!(*pair);
    //}
    //pair
//}

//#[ensures(!result.is_null() ==> own!(*result) && unsafe { (*result).x } == 5)]  //~ ERROR: only unsafe functions can use permissions in their contracts
//fn test02_safe() -> *mut Pair {
    //let p = unsafe {
        //alloc(std::mem::size_of::<Pair>(), std::mem::align_of::<Pair>())
    //};
    //let pair = (p as *mut Pair);
    //if !pair.is_null() {
        //split!(*pair);
        //unsafe { (*pair).y = 4; }
        //unsafe { (*pair).x = 5; }
        //pack!(*pair);
    //}
    //pair
//}

//#[ensures(!result.is_null() ==>     //~ ERROR: permission predicates can be only in positive positions
      //own!(*result) && unsafe { !(*result).is_null() } ==>
      //own!(**result) && unsafe { (**result).x } == 5)]
//unsafe fn test03() -> *mut *mut Pair {
    //let pp = unsafe {
        //alloc(std::mem::size_of::<*mut Pair>(), std::mem::align_of::<*mut Pair>())
    //};
    //let ppair = (pp as *mut *mut Pair);
    //ppair
//}

//#[ensures(!result.is_null() ==>
      //own!(*result) && (
          //unsafe { !(*result).is_null() } ==>
          //own!(**result) && unsafe { (**result).x } == 5))]
//unsafe fn test04() -> *mut *mut Pair {
    //let p = unsafe {
        //alloc(std::mem::size_of::<Pair>(), std::mem::align_of::<Pair>())
    //};
    //let pp = unsafe {
        //alloc(std::mem::size_of::<*mut Pair>(), std::mem::align_of::<*mut Pair>())
    //};
    //let pair = (p as *mut Pair);
    //let ppair = (pp as *mut *mut Pair);
    //let mut v = 0;
    //if !ppair.is_null() {
        //if !pair.is_null() {
            //split!(*pair);
            //unsafe { (*pair).y = 4; }
            //unsafe { (*pair).x = 5; }
            //pack!(*pair);
        //}
        //unsafe { *ppair = pair; }
        //if !pair.is_null() {
            //unpack!(**ppair);
            //unsafe { v = (**ppair).x; }
            //pack!(**ppair);
        //}
    //}
    //ppair
//}

//#[ensures(!result.is_null() ==>     //~ ERROR: postcondition might not hold
      //own!(*result) && (
          //unsafe { !(*result).is_null() } ==>
          //own!(**result) && unsafe { (**result).x } == 6))]
//unsafe fn test04_wrong_value() -> *mut *mut Pair {
    //let p = unsafe {
        //alloc(std::mem::size_of::<Pair>(), std::mem::align_of::<Pair>())
    //};
    //let pp = unsafe {
        //alloc(std::mem::size_of::<*mut Pair>(), std::mem::align_of::<*mut Pair>())
    //};
    //let pair = (p as *mut Pair);
    //let ppair = (pp as *mut *mut Pair);
    //let mut v = 0;
    //if !ppair.is_null() {
        //if !pair.is_null() {
            //split!(*pair);
            //unsafe { (*pair).y = 4; }
            //unsafe { (*pair).x = 5; }
            //pack!(*pair);
        //}
        //unsafe { *ppair = pair; }
        //if !pair.is_null() {
            //unpack!(**ppair);
            //unsafe { v = (**ppair).x; }
            //pack!(**ppair);
        //}
    //}
    //ppair
//}

//#[ensures(!result.1.is_null() ==>
      //own!(*result.1) && (
          //unsafe { !(*result.1).is_null() } ==>
          //own!(**result.1) && unsafe { (**result.1).x } == 5 &&
          //result.0 == 5))]
//unsafe fn test05() -> (i32, *mut *mut Pair) {
    //let p = unsafe {
        //alloc(std::mem::size_of::<Pair>(), std::mem::align_of::<Pair>())
    //};
    //let pp = unsafe {
        //alloc(std::mem::size_of::<*mut Pair>(), std::mem::align_of::<*mut Pair>())
    //};
    //let pair = (p as *mut Pair);
    //let ppair = (pp as *mut *mut Pair);
    //let mut v = 0;
    //if !ppair.is_null() {
        //if !pair.is_null() {
            //split!(*pair);
            //unsafe { (*pair).y = 4; }
            //unsafe { (*pair).x = 5; }
            //pack!(*pair);
        //}
        //unsafe { *ppair = pair; }
        //if !pair.is_null() {
            //unpack!(**ppair);
            //unsafe { v = (**ppair).x; }
            //pack!(**ppair);
        //}
    //}
    //(v, ppair)
//}

//#[ensures(!result.1.is_null() ==>   //~ ERROR: postcondition might not hold
      //own!(*result.1) && (
          //unsafe { !(*result.1).is_null() } ==>
          //own!(**result.1) && unsafe { (**result.1).x } == 6 &&
          //result.0 == 5))]
//unsafe fn test05_wrong_value_1() -> (i32, *mut *mut Pair) {
    //let p = unsafe {
        //alloc(std::mem::size_of::<Pair>(), std::mem::align_of::<Pair>())
    //};
    //let pp = unsafe {
        //alloc(std::mem::size_of::<*mut Pair>(), std::mem::align_of::<*mut Pair>())
    //};
    //let pair = (p as *mut Pair);
    //let ppair = (pp as *mut *mut Pair);
    //let mut v = 0;
    //if !ppair.is_null() {
        //if !pair.is_null() {
            //split!(*pair);
            //unsafe { (*pair).y = 4; }
            //unsafe { (*pair).x = 5; }
            //pack!(*pair);
        //}
        //unsafe { *ppair = pair; }
        //if !pair.is_null() {
            //unpack!(**ppair);
            //unsafe { v = (**ppair).x; }
            //pack!(**ppair);
        //}
    //}
    //(v, ppair)
//}

//#[ensures(!result.1.is_null() ==>   //~ ERROR: postcondition might not hold
      //own!(*result.1) && (
          //unsafe { !(*result.1).is_null() } ==>
          //own!(**result.1) && unsafe { (**result.1).x } == 5 &&
          //result.0 == 6))]
//unsafe fn test05_wrong_value_2() -> (i32, *mut *mut Pair) {
    //let p = unsafe {
        //alloc(std::mem::size_of::<Pair>(), std::mem::align_of::<Pair>())
    //};
    //let pp = unsafe {
        //alloc(std::mem::size_of::<*mut Pair>(), std::mem::align_of::<*mut Pair>())
    //};
    //let pair = (p as *mut Pair);
    //let ppair = (pp as *mut *mut Pair);
    //let mut v = 0;
    //if !ppair.is_null() {
        //if !pair.is_null() {
            //split!(*pair);
            //unsafe { (*pair).y = 4; }
            //unsafe { (*pair).x = 5; }
            //pack!(*pair);
        //}
        //unsafe { *ppair = pair; }
        //if !pair.is_null() {
            //unpack!(**ppair);
            //unsafe { v = (**ppair).x; }
            //pack!(**ppair);
        //}
    //}
    //(v, ppair)
//}

//#[structural_invariant(!self.p.is_null() ==> own!(*self.p) && unsafe { (*self.p).x } == 5)]
//struct T6 {
    //p: *mut Pair,
//}

//fn test06(_: T6) {}

//#[structural_invariant(!self.p.is_null() ==> unsafe { (*self.p).x } == 5)]
//struct T6MissingOwn {  //~ ERROR: there might be insufficient permission to dereference a raw pointer
    //p: *mut Pair,
//}

//fn test06_missing_own(_: T6MissingOwn) {}

//#[structural_invariant(!self.p.is_null() ==> own!(*self.p))]
#[structural_invariant(!self.p.is_null() ==> own!(*self.p) && unsafe {(*self.p).x} == 5)]
struct T4 {
    p: *mut Pair,
}

//#[ensures(!result.p.is_null() ==> unsafe { (*result.p).x } == 5)]
//unsafe fn test04() -> T4 {
    //let p = unsafe {
        //alloc(std::mem::size_of::<Pair>(), std::mem::align_of::<Pair>())
    //};
    //let pair = (p as *mut Pair);
    //if !pair.is_null() {
        //split!(*pair);
        //unsafe { (*pair).y = 4; }
        //unsafe { (*pair).x = 5; }
        //pack!(*pair);
    //}
    //T4 { p: pair }
//}

//#[ensures(unsafe { (*result.p).x } == 5)]
//unsafe fn test04_not_framed() -> T4 {   //~ ERROR: there might be insufficient permission to dereference a raw pointer
                                        ////^ ERROR: the postcondition might not be self-framing.
    //let p = unsafe {
        //alloc(std::mem::size_of::<Pair>(), std::mem::align_of::<Pair>())
    //};
    //let pair = (p as *mut Pair);
    //if !pair.is_null() {
        //split!(*pair);
        //unsafe { (*pair).y = 4; }
        //unsafe { (*pair).x = 5; }
        //pack!(*pair);
    //}
    //T4 { p: pair }
//}

#[structural_invariant(!self.p.is_null() ==> own!((*self.p).x))]
struct T5 {
    p: *mut Pair,
}

#[ensures(!result.p.is_null() ==> unsafe { (*result.p).x } == 5)]
fn test05_safe() -> T5 {
    let p = unsafe {
        alloc(std::mem::size_of::<Pair>(), std::mem::align_of::<Pair>())
    };
    let pair = (p as *mut Pair);
    if !pair.is_null() {
        split!(*pair);
        //unsafe { (*pair).y = 4; }
        unsafe { (*pair).x = 5; }
        //pack!(*pair);
    }
    T5 { p: pair }
}

//#[ensures(unsafe { (*result.p).x } == 5)]   //~ ERROR: postcondition might not hold
//fn test04_safe_not_framed() -> T4 {   //~ ERROR: there might be insufficient permission to dereference a raw pointer
    //let p = unsafe {
        //alloc(std::mem::size_of::<Pair>(), std::mem::align_of::<Pair>())
    //};
    //let pair = (p as *mut Pair);
    //if !pair.is_null() {
        //split!(*pair);
        //unsafe { (*pair).y = 4; }
        //unsafe { (*pair).x = 5; }
        //pack!(*pair);
    //}
    //T4 { p: pair }
//}

//#[structural_invariant(!self.p.is_null() ==> own!((*self.p).x))]
//struct T2 {
    //p: *mut Pair,
//}

//#[ensures(!result.p.is_null() ==> framed!((*result.p).x, unsafe { (*result.p).x }) == 5)]
//fn test03() -> T1 {
    //let p = unsafe {
        //alloc(std::mem::size_of::<Pair>(), std::mem::align_of::<Pair>())
    //};
    //let pair = (p as *mut Pair);
    //if !pair.is_null() {
        //split!(*pair);
        //unsafe { (*pair).y = 4; }
        //unsafe { (*pair).x = 5; }
        //pack!(*pair);
    //}
    //T1 { p: pair }
//}

//#[ensures(!result.p.is_null() ==> unsafe { (*result.p).x } == 5)]   //~ ERROR: Permissions
//fn test03_non_framed() -> T1 {
    //let p = unsafe {
        //alloc(std::mem::size_of::<Pair>(), std::mem::align_of::<Pair>())
    //};
    //let pair = (p as *mut Pair);
    //if !pair.is_null() {
        //split!(*pair);
        //unsafe { (*pair).x = 5; }
    //}
    //T1 { p: pair }
//}

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
