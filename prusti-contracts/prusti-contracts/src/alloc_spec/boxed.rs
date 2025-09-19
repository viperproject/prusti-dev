use crate::*;

use alloc::boxed::Box;

#[extern_spec]
impl<T> Box<T> {
    #[ensures(*result === x)]
    fn new(x: T) -> Self;
}
