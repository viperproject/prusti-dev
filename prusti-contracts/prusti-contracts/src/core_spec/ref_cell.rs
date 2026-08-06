use crate::*;

use core::cell::RefCell;

#[extern_spec]
impl<T> RefCell<T> {
    #[pure_unstable(true)]
    #[interior_mut(match refcell_count(self) {
        0 => Real::WRITE,
        n if n > 0 => Real::WRITE / Real::from(n),
        _ => Real::NONE,
    })]
    pub fn as_ptr(&self) -> *mut T;
}

#[trusted]
#[pure_unstable(true)]
pub fn refcell_count<T>(_r: &RefCell<T>) -> isize {
    unimplemented!()
}
