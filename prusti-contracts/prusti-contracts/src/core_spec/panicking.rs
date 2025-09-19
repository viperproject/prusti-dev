use crate::*;

use core::panicking;

#[extern_spec]
mod panicking {
    #[pure]
    #[requires(false)]
    fn panic(msg: &'static str) -> !;
}
