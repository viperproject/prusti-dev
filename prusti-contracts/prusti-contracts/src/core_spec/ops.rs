use crate::*;

use core::ops::Index;

#[extern_spec]
pub trait Index<Idx> {
    #[trusted]
    #[pure]
    fn index(&self, index: Idx) -> &Self::Output;
}
