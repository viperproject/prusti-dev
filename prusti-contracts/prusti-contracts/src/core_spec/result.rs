use crate::*;

#[extern_spec]
impl<T, E> Result<T, E> {
    #[trusted]
    #[pure]
    #[ensures(result == matches!(self, Ok(_)))]
    pub fn is_ok(&self) -> bool;

    #[trusted]
    #[pure]
    #[ensures(result == matches!(self, Err(_)))]
    pub fn is_err(&self) -> bool;
}
