use crate::*;

#[extern_spec]
impl<T> ::core::option::Option<T> {
    #[pure]
    #[ensures(result == matches!(self, Some(_)))]
    fn is_some(&self) -> bool;
}

