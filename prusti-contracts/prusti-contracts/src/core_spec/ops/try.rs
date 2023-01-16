use crate::*;

#[allow(unused_imports)]
use core::convert::Infallible;
#[allow(unused_imports)]
use core::ops::*;

#[extern_spec]
impl<T, E> Try for Result<T, E> {
    #[ensures(result === Ok(output))]
    fn from_output(output: T) -> Self;

    #[ensures(match old(self) {
        Ok(output) => result === ControlFlow::Continue(output),
        Err(error) => result === ControlFlow::Break(Err(error)),
    })]
    fn branch(self) -> ControlFlow<Result<Infallible, E>, T>;
}

#[extern_spec]
impl<T> Try for Option<T> {
    #[ensures(result === Some(output))]
    fn from_output(output: T) -> Self;

    #[ensures(match old(self) {
        Some(output) => result === ControlFlow::Continue(output),
        //None => result === ControlFlow::Break(None),
        None => match result {
            ControlFlow::Break(residual) => residual.is_none(),
            _ => false,
        },
    })]
    fn branch(self) -> ControlFlow<Option<Infallible>, T>;
}
