use crate::*;

#[extern_spec]
impl<T, E> ::core::result::Result<T, E> {
    #[pure]
    #[ensures(result == matches!(self, Ok(_)))]
    fn is_ok(&self) -> bool;

    #[pure]
    #[ensures(result == matches!(self, Err(_)))]
    fn is_err(&self) -> bool;
}

#[extern_spec]
impl<T, E: ::core::fmt::Debug> ::core::result::Result<T, E> {
    #[requires(matches!(self, Ok(_)))]
    fn unwrap(self) -> T;
}
