use crate::*;

use core::ops::Index;

// FUTURE(#1221): This spec is currently not usable due to issue #1221.
#[extern_spec]
trait Index<Idx> {
    #[pure]
    fn index(&self, idx: Idx) -> &Self::Output;
}
