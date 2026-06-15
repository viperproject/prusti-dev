use crate::*;

use core::cell::RefCell;

#[extern_spec]
impl<T> RefCell<T> {
    #[interior_mut(match refcell_count(self) {
        0 => Real::FULL,
        n if n > 0 => Real::FULL / Real::from(n as f64),
        _ => Real::NONE,
    })]
    pub fn as_ptr(&self) -> *mut T;
}

#[trusted]
#[pure_unstable(true)]
pub fn refcell_count<T>(r: &RefCell<T>) -> isize {
    todo!()
}
