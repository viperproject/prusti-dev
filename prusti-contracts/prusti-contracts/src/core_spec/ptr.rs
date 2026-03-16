use crate::*;

#[extern_spec]
impl<T> *mut T {
    #[pure]
    #[ensures(result === mut_ptr_add::<T>(self, count))]
    pub const unsafe fn add(self, count: usize) -> *mut T;

    #[pure]
    #[ensures(result === mut_ptr_sub::<T>(self, count))]
    pub const unsafe fn sub(self, count: usize) -> *mut T;
}