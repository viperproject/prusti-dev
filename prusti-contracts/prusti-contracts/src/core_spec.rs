use crate::*;

#[extern_spec]
impl<T, E> ::core::result::Result<T, E> {
    #[pure]
    #[ensures(result == matches!(self, Ok(_)))]
    #[no_panic]
    #[no_panic_ensures_postcondition]
    fn is_ok(&self) -> bool;

    #[pure]
    #[ensures(result == matches!(self, Err(_)))]
    #[no_panic]
    #[no_panic_ensures_postcondition]
    fn is_err(&self) -> bool;
}

#[extern_spec]
impl<T, E: ::core::fmt::Debug> ::core::result::Result<T, E> {
    #[requires(matches!(self, Ok(_)))]
    #[ensures(match self {
        Ok(value) => result === value,
        Err(_) => false,
    })]
    #[no_panic_ensures_postcondition]
    fn unwrap(self) -> T;
}

#[extern_spec]
impl<T> ::core::option::Option<T> {
    #[requires(matches!(self, Some(_)))]
    #[ensures(match self {
        Some(value) => result === value,
        None => false,
    })]
    #[no_panic_ensures_postcondition]
    fn unwrap(self) -> T;
}

// Crashes ☹
type Pointer<T> = *const T;
#[extern_spec]
impl<T> Pointer<T> {
    #[trusted]
    #[terminates]
    #[pure]
    // FIXME: This is needed because this function is special cased only in the
    // pure encoder and not in the impure one.
    #[ensures(result == self.is_null())]
    #[no_panic]
    #[no_panic_ensures_postcondition]
    fn is_null(self) -> bool;

    #[trusted]
    #[terminates]
    #[pure]
    // FIXME: Check provenance.
    #[structural_requires(Int::new_isize(count) * Int::new_usize(std::mem::size_of::<T>()) <= Int::new_isize(isize::MAX))]
    #[ensures(result == address_offset(self, Int::new_isize(count)))]
    #[no_panic]
    #[no_panic_ensures_postcondition]
    unsafe fn offset(self, count: isize) -> *const T;

    #[trusted]
    #[terminates]
    #[pure]
    // FIXME: Properly specify the wrapping arithmetic.
    #[ensures(result == address_offset(self, Int::new_isize(count)))]
    #[no_panic]
    #[no_panic_ensures_postcondition]
    fn wrapping_offset(self, count: isize) -> *const T;

    #[trusted]
    #[terminates]
    #[pure]
    // FIXME: Check provenance.
    #[structural_requires(address_from(self, origin) * Int::new_usize(std::mem::size_of::<T>()) <= Int::new_isize(isize::MAX))]
    #[structural_requires(address_from(self, origin) >= Int::new_isize(0))]
    #[ensures(Int::new_isize(result) == address_from(self, origin))]
    #[no_panic]
    #[no_panic_ensures_postcondition]
    unsafe fn offset_from(self, origin: *const T) -> isize;

    #[trusted]
    #[terminates]
    #[pure]
    // FIXME: Check provenance.
    #[structural_requires(Int::new_usize(count) * Int::new_usize(std::mem::size_of::<T>()) <= Int::new_isize(isize::MAX))]
    #[ensures(result == address_offset(self, Int::new_usize(count)))]
    #[no_panic]
    #[no_panic_ensures_postcondition]
    unsafe fn add(self, count: usize) -> *const T;
}

type MutPointer<T> = *mut T;
#[extern_spec]
impl<T> MutPointer<T> {
    #[trusted]
    #[terminates]
    #[pure]
    // FIXME: This is needed because this function is special cased only in the
    // pure encoder and not in the impure one.
    #[ensures(result == self.is_null())]
    #[no_panic]
    #[no_panic_ensures_postcondition]
    fn is_null(self) -> bool;

    #[trusted]
    #[terminates]
    #[pure]
    // FIXME: Check provenance.
    #[structural_requires(Int::new_isize(count) * Int::new_usize(std::mem::size_of::<T>()) <= Int::new_isize(isize::MAX))]
    #[ensures(result == address_offset_mut(self, Int::new_isize(count)))]
    #[no_panic]
    #[no_panic_ensures_postcondition]
    unsafe fn offset(self, count: isize) -> *mut T;

    #[trusted]
    #[terminates]
    #[pure]
    // FIXME: Properly specify the wrapping arithmetic.
    #[ensures(result == address_offset_mut(self, Int::new_isize(count)))]
    #[no_panic]
    #[no_panic_ensures_postcondition]
    fn wrapping_offset(self, count: isize) -> *mut T;

    #[trusted]
    #[terminates]
    #[pure]
    // FIXME: Check provenance.
    #[structural_requires(Int::new_usize(count) * Int::new_usize(std::mem::size_of::<T>()) <= Int::new_isize(isize::MAX))]
    #[ensures(result == address_offset_mut(self, Int::new_usize(count)))]
    #[no_panic]
    #[no_panic_ensures_postcondition]
    unsafe fn add(self, count: usize) -> *mut T;

    #[trusted]
    #[terminates]
    #[pure]
    // FIXME: Check provenance.
    #[structural_requires(address_from(self, origin) * Int::new_usize(std::mem::size_of::<T>()) <= Int::new_isize(isize::MAX))]
    #[structural_requires(address_from(self, origin) >= Int::new_isize(0))]
    #[ensures(Int::new_isize(result) == address_from(self, origin))]
    #[no_panic]
    #[no_panic_ensures_postcondition]
    unsafe fn offset_from(self, origin: *const T) -> isize;

    #[no_panic]
    #[no_panic_ensures_postcondition]
    #[structural_requires(raw!(*self, std::mem::size_of::<T>()))]
    #[structural_ensures(own!(*self))]
    #[structural_ensures(unsafe { eval_in!(own!(*self), &*self) } === &val)]
    pub unsafe fn write(self, val: T);
}

#[extern_spec]
impl usize {
    #[terminates]
    #[pure]
    #[no_panic]
    #[no_panic_ensures_postcondition]
    fn is_power_of_two(self) -> bool;

    #[terminates]
    #[pure]
    #[no_panic]
    #[no_panic_ensures_postcondition]
    #[ensures(if Int::new_usize(self) * Int::new_usize(rhs) <= Int::new_usize(usize::MAX) {
        result == Some(self * rhs)
    } else {
        let none = None;
        result == none
    })]
    fn checked_mul(self, rhs: usize) -> Option<usize>;

    #[terminates]
    #[pure]
    #[no_panic]
    #[no_panic_ensures_postcondition]
    #[ensures(if Int::new_usize(self) + Int::new_usize(rhs) <= Int::new_usize(usize::MAX) {
    result == Some(self + rhs)
    } else {
        let none = None;
        result == none
    })]
    fn checked_add(self, rhs: usize) -> Option<usize>;

    #[terminates]
    #[pure]
    #[no_panic]
    #[no_panic_ensures_postcondition]
    #[ensures(self >= rhs ==> result == self - rhs)]
    fn wrapping_sub(self, rhs: usize) -> usize;
}

#[extern_spec]
impl<T> ::core::ptr::NonNull<T> {
    #[trusted]
    #[terminates]
    #[pure]
    #[no_panic]
    #[no_panic_ensures_postcondition]
    pub fn dangling() -> Self;

    #[trusted]
    #[terminates]
    #[pure]
    #[no_panic]
    #[no_panic_ensures_postcondition]
    pub fn as_ptr(self) -> *mut T;
}

#[extern_spec]
mod core {
    mod mem {
        #[pure]
        #[no_panic]
        #[no_panic_ensures_postcondition]
        // FIXME: This is needed because this function is special cased only in the
        // pure encoder and not in the impure one.
        #[ensures(result == core::mem::size_of::<T>())]
        pub fn size_of<T>() -> usize;

        #[pure]
        #[no_panic]
        #[no_panic_ensures_postcondition]
        // FIXME: What are the guarantees?
        // https://doc.rust-lang.org/std/mem/fn.align_of.html says nothing…
        #[ensures(result > 0)]
        // FIXME: This is needed because this function is special cased only in the
        // pure encoder and not in the impure one.
        #[ensures(result == core::mem::align_of::<T>())]
        #[ensures(result.is_power_of_two())]
        pub fn align_of<T>() -> usize;
    }
    mod ptr {
        #[pure]
        #[no_panic]
        #[no_panic_ensures_postcondition]
        #[ensures(result.is_null())]
        pub fn null<T>() -> *const T;

        #[no_panic]
        #[no_panic_ensures_postcondition]
        #[structural_requires(own!(*src))]
        #[structural_ensures(raw!(*src, std::mem::size_of::<T>()))]
        #[ensures(unsafe { old(eval_in!(own!(*src), &*src)) } === &result)]
        pub unsafe fn read<T>(src: *const T) -> T;

        #[no_panic]
        #[no_panic_ensures_postcondition]
        #[structural_requires(raw!(*dst, std::mem::size_of::<T>()))]
        #[structural_ensures(own!(*dst))]
        #[structural_ensures(unsafe { eval_in!(own!(*dst), &*dst) } === &src)]
        pub unsafe fn write<T>(dst: *mut T, src: T);

        #[structural_requires(own!(*to_drop))]
        #[structural_ensures(raw!(*to_drop, std::mem::size_of::<T>()))]
        pub unsafe fn drop_in_place<T>(to_drop: *mut T);
    }
}

#[extern_spec]
impl std::alloc::Layout {
    #[ensures(result.size() == core::mem::size_of::<T>())]
    #[ensures(result.align() == core::mem::align_of::<T>())]
    #[no_panic]
    #[no_panic_ensures_postcondition]
    fn new<T>() -> std::alloc::Layout;

    // #[requires(core::mem::size_of::<T>() == 4 && core::mem::align_of::<T>() == 4)] // FIXME: We currently support only i32.
    // Documentation: https://doc.rust-lang.org/reference/type-layout.html#array-layout
    #[requires(n * core::mem::size_of::<T>() <= (isize::MAX as usize))]
    #[ensures(
        (n * core::mem::size_of::<T>() <= (isize::MAX as usize)) == result.is_ok()
    )]
    #[ensures(match result {
        Ok(layout) => {
            layout.size() == n * core::mem::size_of::<T>() &&
            layout.align() == core::mem::align_of::<T>()
        },
        Err(_) => true,
    })]
    #[no_panic]
    #[no_panic_ensures_postcondition]
    fn array<T>(n: usize) -> Result<std::alloc::Layout, std::alloc::LayoutError>;

    #[pure]
    #[no_panic]
    #[no_panic_ensures_postcondition]
    fn size(&self) -> usize;

    #[pure]
    #[no_panic]
    #[no_panic_ensures_postcondition]
    fn align(&self) -> usize;
}

#[extern_spec]
mod std {
    mod alloc {
        // “It’s undefined behavior if global allocators unwind.”
        // https://doc.rust-lang.org/std/alloc/trait.GlobalAlloc.html
        #[no_panic]
        #[structural_requires(
            raw!(*ptr, layout.size()) &&
            raw_dealloc!(*ptr, layout.size(), layout.align())
        )]
        pub unsafe fn dealloc(ptr: *mut u8, layout: std::alloc::Layout);

        // “It’s undefined behavior if global allocators unwind.”
        // https://doc.rust-lang.org/std/alloc/trait.GlobalAlloc.html
        #[no_panic]
        #[no_panic_ensures_postcondition]
        #[structural_requires(
            layout.size() > 0
        )]
        #[ensures(
            !result.is_null() ==> (
                raw!(*result, layout.size()) &&
                raw_dealloc!(*result, layout.size(), layout.align())
            )
        )]
        pub unsafe fn alloc(layout: std::alloc::Layout) -> *mut u8;
    }
}
