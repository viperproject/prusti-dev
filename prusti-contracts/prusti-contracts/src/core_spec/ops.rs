use crate::*;

use core::ops::{Index, IndexMut};

#[extern_spec]
pub trait Index<Idx> {
    #[trusted]
    #[pure]
    #[requires(false)]
    fn index(&self, index: Idx) -> &Self::Output;
}

#[extern_spec]
pub trait IndexMut<Idx>: Index<Idx> {
    #[trusted]
    #[requires(false)]
    fn index_mut(&mut self, index: Idx) -> &mut <Self as Index<Idx>>::Output;
}
