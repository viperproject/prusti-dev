use crate::*;

#[extern_spec]
impl<T> Option<T> {
    #[trusted]
    #[pure]
    fn is_some(&self) -> bool;

    #[trusted]
    #[pure]
    fn is_none(&self) -> bool;
}
