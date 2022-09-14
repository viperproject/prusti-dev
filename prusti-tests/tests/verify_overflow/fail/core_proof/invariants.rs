// compile-flags: -Punsafe_core_proof=true -Penable_type_invariants=true
// -Pverify_specifications_with_core_proof=true
// -Puse_snapshot_parameters_in_predicates=true

use prusti_contracts::*;

// struct T1 {
//     f: i32,
// }

// fn test1(mut a: T1) -> T1 {
//     let b = std::ptr::addr_of_mut!(a);
//     unpack!(*b);
//     unpack!((*b).f);
//     unsafe { (*b).f = 4; }
//     pack!(*b);
//     restore!(*b, a);
//     assert!(a.f == 4);
//     a
// }

// fn test2(mut a: T1) -> T1 {
//     let b = std::ptr::addr_of_mut!(a);
//     unpack!(*b);
//     forget_initialization!((*b).f);
//     unsafe { (*b).f = 4; }
//     pack!(*b);
//     restore!(*b, a);
//     assert!(a.f == 4);
//     a
// }

// fn test3(mut a: T1) -> T1 {
//     let b = std::ptr::addr_of_mut!(a);
//     unpack!(*b);
//     unpack!((*b).f);
//     unsafe { (*b).f = 4; }
//     pack!(*b);
//     restore!(*b, a);
//     assert!(a.f == 5);  //~ ERROR: the asserted expression might not hold
//     a
// }

// fn test4(mut a: T1) -> T1 {
//     let b = std::ptr::addr_of_mut!(a);
//     unpack!(*b);
//     forget_initialization!((*b).f);
//     unsafe { (*b).f = 4; }
//     pack!(*b);
//     restore!(*b, a);
//     assert!(a.f == 5);  //~ ERROR: the asserted expression might not hold
//     a
// }

// fn test5(mut a: T1) -> T1 {
//     let b = std::ptr::addr_of_mut!(a);
//     unpack!(*b);
//     forget_initialization!((*b).f);
//     unsafe { (*b).f = 4; }
//     assert!( unsafe { (*b).f }  == 4);
//     pack!(*b);
//     restore!(*b, a);
//     a
// }

// fn test6(mut a: T1) -> T1 {
//     let b = std::ptr::addr_of_mut!(a);
//     unpack!(*b);
//     forget_initialization!((*b).f);
//     assert!( unsafe { (*b).f }  == 4);  //~ ERROR: the asserted expression might not hold
//                             //^ ERROR: the accessed place may not be allocated or initialized
//     unsafe { (*b).f = 4; }
//     pack!(*b);
//     restore!(*b, a);
//     a
// }

// fn test7(mut a: T1) -> T1 {
//     let b = std::ptr::addr_of_mut!(a);
//     unpack!(*b);
//     assert!( unsafe { (*b).f }  == 4);  //~ ERROR: the asserted expression might not hold
//     forget_initialization!((*b).f);
//     unsafe { (*b).f = 4; }
//     pack!(*b);
//     restore!(*b, a);
//     a
// }

// #[requires(b ==> own!(*p))]
// #[ensures(b ==> ((own!(*p)) && unsafe { *p } == 4))]
// unsafe fn test8(p: *mut i32, b: bool) {
//     if b {
//         forget_initialization!(*p);
//         unsafe { *p = 4 };
//     }
// }

// #[ensures(result.f == 4)]
// fn test9(mut a: T1) -> T1 {
//     let b = std::ptr::addr_of_mut!(a.f);
//     unsafe { test8(b, true); }
//     restore!(*b, a.f);
//     a
// }

// #[requires(b ==> own!(*p))]
// #[ensures(b ==> ((own!(*p)) && unsafe { *p } == 5))]   //~ ERROR: postcondition might not hold.
// unsafe fn test10(p: *mut i32, b: bool) {
//     if b {
//         forget_initialization!(*p);
//         unsafe { *p = 4 };
//     }
// }

// #[ensures(result.f == 5)]   //~ ERROR: postcondition might not hold.
// fn test11(mut a: T1) -> T1 {
//     let b = std::ptr::addr_of_mut!(a.f);
//     unsafe { test8(b, true); }
//     restore!(*b, a.f);
//     a
// }

// struct T2 {
//     f: i32,
//     g: i32,
// }

// #[ensures(result.f == 4 && result.g == a.g)]
// fn test12(mut a: T2) -> T2 {
//     let b = std::ptr::addr_of_mut!(a);
//     unpack!(*b);
//     unpack!((*b).f);
//     unsafe { (*b).f = 4; }
//     pack!(*b);
//     restore!(*b, a);
//     assert!(a.f == 4);
//     a
// }

// #[ensures(result.f == 5 && result.g == a.g)]
// fn test13(mut a: T2) -> T2 {    //~ ERROR: postcondition might not hold.
//     let b = std::ptr::addr_of_mut!(a);
//     unpack!(*b);
//     unpack!((*b).f);
//     unsafe { (*b).f = 4; }
//     pack!(*b);
//     restore!(*b, a);
//     assert!(a.f == 4);
//     a
// }

// #[requires(b ==> (own!(*p) && unsafe { *p } < 20))]
// #[ensures(b ==> (own!(*p) && unsafe { *p } == old(unsafe { *p }) + 1))]
// unsafe fn test14(p: *mut i32, b: bool) {
//     if b {
//         // FIXME: unsafe { *p += 1 };
//         let tmp = unsafe { *p };
//         forget_initialization!(*p);
//         unsafe { *p = tmp + 1 };
//     }
// }

// #[ensures(result.f == 7)]
// fn test15(mut a: T1) -> T1 {
//     a.f = 6;
//     let b = std::ptr::addr_of_mut!(a.f);
//     unsafe { test14(b, true); }
//     restore!(*b, a.f);
//     a
// }

// #[ensures(result.f == 8)]
// fn test16(mut a: T1) -> T1 {
//     a.f = 6;
//     let b = std::ptr::addr_of_mut!(a.f);
//     unsafe { test14(b, true); }
//     restore!(*b, a.f);
//     a
// }

// fn alloc_client() {
//     let size = std::mem::size_of::<u16>();
//     let align = std::mem::align_of::<u16>();
//     let ptr = unsafe { alloc(size, align) };
//     if !ptr.is_null() {
//         unsafe { *(ptr as *mut u16) = 42; }
//         assert!(unsafe { *(ptr as *mut u16) } == 42);
//         let ptr_u16 = (ptr as *mut u16);
//         forget_initialization!(*ptr_u16);    // FIXME: We should support (ptr as *mut u16).
//         unsafe { dealloc(ptr, size, align) };
//     }
// }

// fn alloc_client2() {
//     let size = std::mem::size_of::<u16>();
//     let align = std::mem::align_of::<u16>();
//     let ptr = unsafe { alloc(size, align) };
//     if !ptr.is_null() {
//         unsafe { *(ptr as *mut u16) = 42; }
//         assert!(unsafe { *(ptr as *mut u16) } == 43);   //~ ERROR: the asserted expression might not hold
//         let ptr_u16 = (ptr as *mut u16);
//         forget_initialization!(*ptr_u16);    // FIXME: We should support (ptr as *mut u16).
//         unsafe { dealloc(ptr, size, align) };
//     }
// }

// fn alloc_client3() {
//     let size = std::mem::size_of::<u16>();
//     let align = std::mem::align_of::<u16>();
//     let ptr = unsafe { alloc(size, align) };
//     unsafe { *(ptr as *mut u16) = 42; }     //~ ERROR: the accessed memory location must be allocated and uninitialized
// }

// #[requires(x < 5)]
// unsafe fn check_x(x: u32) {}

// #[structural_invariant(self.x < 5)]
// struct T3 {
//     x: u32,
// }

// fn test17(a: T3) {
//     unpack!(a);
//     unsafe { check_x(a.x) }
//     pack!(a);
//     forget_initialization!(a);
// }

// #[structural_invariant(
//     !self.p1.is_null() ==> (
//         raw!(*self.p1, std::mem::size_of::<i32>()) &&
//         raw_dealloc!(*self.p1, std::mem::size_of::<i32>(), std::mem::align_of::<i32>())
//     )
// )]
// #[structural_invariant(
//     !self.p2.is_null() ==> (
//         own!(*self.p2) &&
//         raw_dealloc!(*self.p2, std::mem::size_of::<i32>(), std::mem::align_of::<i32>())
//     )
// )]
// struct T4 {
//     p1: *mut i32,
//     p2: *mut i32,
// }

// impl T4 {
//     fn new() -> Self {
//         let p1 = unsafe {
//             alloc(std::mem::size_of::<i32>(), std::mem::align_of::<i32>())
//         };
//         let p2 = unsafe {
//             alloc(std::mem::size_of::<i32>(), std::mem::align_of::<i32>())
//         };
//         if !p2.is_null() {
//             unsafe { *(p2 as *mut i32) = 42; }
//         }
//         Self { p1: (p1 as *mut i32), p2: (p2 as *mut i32) }
//     }
// }

// #[structural_invariant(
//     !self.p2.is_null() ==> (
//         own!(*self.p2) &&
//         raw_dealloc!(*self.p2, std::mem::size_of::<i32>(), std::mem::align_of::<i32>()) &&
//         unsafe { *self.p2 == 42 } &&
//         1 == 1 &&
//         2 == 2 &&
//         3 == 3 &&
//         4 == 4 &&
//         5 == 5 &&
//         6 == 6
//     )
// )]
// struct T5 {
//     p2: *mut i32,
// }

// impl T5 {
//     fn new() -> Self {
//         let p2 = unsafe {
//             alloc(std::mem::size_of::<i32>(), std::mem::align_of::<i32>())
//         };
//         if !p2.is_null() {
//             unsafe { *(p2 as *mut i32) = 42; }
//         }
//         Self { p2: (p2 as *mut i32) }
//     }
//     fn new_fail() -> Self {
//         let p2 = unsafe {
//             alloc(std::mem::size_of::<i32>(), std::mem::align_of::<i32>())
//         };
//         if !p2.is_null() {
//             unsafe { *(p2 as *mut i32) = 43; }
//         }
//         Self { p2: (p2 as *mut i32) }   //~ ERROR: The type invariant of the constructed object might not hold
//     }
// }

#[structural_invariant(
    !self.p.is_null() ==> (
        raw_dealloc!(*self.p, std::mem::size_of::<Pair>(), std::mem::align_of::<Pair>()) &&
        raw!((*self.p).x, std::mem::size_of::<i32>()) &&
        own!((*self.p).y) &&
        unsafe { (*self.p).y } == self.v
    )
)]
struct T6 {
    v: i32,
    p: *mut Pair,
}

impl T6 {
    #[ensures(result.v == 42)]
    #[ensures(
        unpacking!(
            result,
            !result.p.is_null() ==>
            (unpacking!((*result.p).y, unsafe { (*result.p).y }) == 42)
        )
    )]
    fn new() -> Self {
        let p2 = unsafe {
            alloc(std::mem::size_of::<Pair>(), std::mem::align_of::<Pair>())
        };
        let p = (p2 as *mut Pair);
        if !p2.is_null() {
            split!(*p);
            unsafe { (*p).y = 42; }
        }
        Self { p, v: 42 }
    }
//  #[ensures(result.v == 42)]
//  #[ensures(
//      unpacking!(         //~ ERROR: postcondition might not hold.
//          result,
//          !result.p.is_null() ==>
//          (unpacking!((*result.p).y, unsafe { (*result.p).y }) == 43)
//      )
//  )]
//  fn new_fail_wrong_value() -> Self {
//      let p2 = unsafe {
//          alloc(std::mem::size_of::<Pair>(), std::mem::align_of::<Pair>())
//      };
//      let p = (p2 as *mut Pair);
//      if !p2.is_null() {
//          split!(*p);
//          unsafe { (*p).y = 42; }
//      }
//      Self { p, v: 42 }
//  }
//  #[ensures(result.v == 42)]
//  #[ensures(
//      !result.p.is_null() ==>
//      (unpacking!((*result.p).y, unsafe { (*result.p).y }) == 42)
//  )]
//  fn new_fail_missing_outer_unpacking() -> Self {     //~ ERROR: there might be insufficient permission to dereference a raw pointer
//      let p2 = unsafe {
//          alloc(std::mem::size_of::<Pair>(), std::mem::align_of::<Pair>())
//      };
//      let p = (p2 as *mut Pair);
//      if !p2.is_null() {
//          split!(*p);
//          unsafe { (*p).y = 42; }
//      }
//      Self { p, v: 42 }
//  }
    #[ensures(result.v == 42)]
    #[ensures(
        unpacking!(
            result,
            !result.p.is_null() ==>
            (unsafe { (*result.p).y } == 42)
        )
    )]
    fn new_fail_missing_inner_unpacking() -> Self {
        let p2 = unsafe {
            alloc(std::mem::size_of::<Pair>(), std::mem::align_of::<Pair>())
        };
        let p = (p2 as *mut Pair);
        if !p2.is_null() {
            split!(*p);
            unsafe { (*p).y = 42; }
        }
        Self { p, v: 42 }
    }
//  #[ensures(result.v == 42)]
//  #[ensures(
//      unpacking!(
//          result,
//          !result.p.is_null() ==>
//          (unpacking!(*result.p, unsafe { (*result.p).y }) == 42)
//      )
//  )]
//  fn new_fail_wrong_inner_unpacking() -> Self {   //~ ERROR: there might be insufficient permission to dereference a raw pointer
//      let p2 = unsafe {
//          alloc(std::mem::size_of::<Pair>(), std::mem::align_of::<Pair>())
//      };
//      let p = (p2 as *mut Pair);
//      if !p2.is_null() {
//          split!(*p);
//          unsafe { (*p).y = 42; }
//      }
//      Self { p, v: 42 }
//  }

    //#[ensures(result.v == 42)]
    //#[ensures(!result.p.is_null() ==> (unsafe { (*result.p).y } == 42))]  //~ ERROR: there might be insufficient permission to dereference a raw pointer
    //fn new_fail1() -> Self {
        //let p2 = unsafe {
            //alloc(std::mem::size_of::<Pair>(), std::mem::align_of::<Pair>())
        //};
        //let p = (p2 as *mut Pair);
        //if !p2.is_null() {
            //split!(*p);
            //unsafe { (*p).y = 42; }
        //}
        //Self { p, v: 42 }
    //}
    //fn new_fail() -> Self {
        //let p2 = unsafe {
            //alloc(std::mem::size_of::<Pair>(), std::mem::align_of::<Pair>())
        //};
        //let p = (p2 as *mut Pair);
        //if !p2.is_null() {
            //split!(*p);
            //unsafe { (*p).y = 43; }
        //}
        //Self { p, v: 42 }   //~ ERROR: The type invariant of the constructed object might not hold
    //}
    //#[ensures(result.v == 42)]
    //#[ensures((unsafe { (*result.p).y } == 42))]    //~ ERROR: there might be insufficient permission to dereference a raw pointer
                                                    ////^ ERROR: postcondition might not hold
    //fn new_fail2() -> Self {
        //let p2 = unsafe {
            //alloc(std::mem::size_of::<Pair>(), std::mem::align_of::<Pair>())
        //};
        //let p = (p2 as *mut Pair);
        //if !p2.is_null() {
            //split!(*p);
            //unsafe { (*p).y = 42; }
        //}
        //Self { p, v: 42 }
    //}

    //#[ensures(result.v == 42)]
    //// TODO: Make sure to distinguish unpacking!((*result.p), ...) from
    //// unpacking!((*result.p).y, ...)
    //#[ensures((unpacking!(result.p, unsafe { (*result.p).y }) == 42))]
    //fn new_fail3() -> Self {
        //let p2 = unsafe {
            //alloc(std::mem::size_of::<Pair>(), std::mem::align_of::<Pair>())
        //};
        //let p = (p2 as *mut Pair);
        //if !p2.is_null() {
            //split!(*p);
            //unsafe { (*p).y = 42; }
        //}
        //Self { p, v: 42 }
    //}

    //#[ensures(result.v == 42)]
    //// TODO: Make sure to distinguish unpacking!((*result.p), ...) from
    //// unpacking!((*result.p).y, ...)
    //#[ensures((unpacking!((*result.p).y, unsafe { (*result.p).y }) == 42))]
    //fn new_fail4() -> Self {
        //let p2 = unsafe {
            //alloc(std::mem::size_of::<Pair>(), std::mem::align_of::<Pair>())
        //};
        //let p = (p2 as *mut Pair);
        //if !p2.is_null() {
            //split!(*p);
            //unsafe { (*p).y = 42; }
        //}
        //Self { p, v: 42 }
    //}
    // #[pure]
    // fn value(&self) -> i32 {
    //     if self.p2.is_null() {
    //         0
    //     } else {
    //         unsafe { *self.p2 }
    //     }
    // }
}

// #[structural_invariant(
//     !self.p2.is_null() ==> (
//         own!(*self.p2) &&
//         raw_dealloc!(*self.p2, std::mem::size_of::<i32>(), std::mem::align_of::<i32>()) &&
//         unsafe { *self.p2 } == self.v
//     )
// )]
// struct T6 {
//     v: i32,
//     p2: *mut i32,
// }

// impl T6 {
//     // #[ensures(result.v == 42)]
//     // #[ensures(!result.p2.is_null() ==> (unsafe { *result.p2 } == 42))]
//     // fn new() -> Self {
//     //     let p2 = unsafe {
//     //         alloc(std::mem::size_of::<i32>(), std::mem::align_of::<i32>())
//     //     };
//     //     if !p2.is_null() {
//     //         unsafe { *(p2 as *mut i32) = 42; }
//     //     }
//     //     Self { p2: (p2 as *mut i32), v: 42 }
//     // }
//     #[ensures(result.v == 42)]
//     #[ensures(unsafe { *result.p2 } == 42)] //~ ERROR: Permissions
//     fn new_fail() -> Self {
//         let p2 = unsafe {
//             alloc(std::mem::size_of::<i32>(), std::mem::align_of::<i32>())
//         };
//         if !p2.is_null() {
//             unsafe { *(p2 as *mut i32) = 42; }
//         }
//         Self { p2: (p2 as *mut i32), v: 42 }
//     }
//     // #[pure]
//     // fn value(&self) -> i32 {
//     //     if self.p2.is_null() {
//     //         0
//     //     } else {
//     //         unsafe { *self.p2 }
//     //     }
//     // }
// }

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
