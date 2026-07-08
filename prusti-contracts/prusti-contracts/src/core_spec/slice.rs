use crate::*;

#[extern_spec]
impl<T> [T] {
    #[pure]
    #[ensures(result == core::intrinsics::ptr_metadata(self))]
    fn len(&self) -> usize;
}
