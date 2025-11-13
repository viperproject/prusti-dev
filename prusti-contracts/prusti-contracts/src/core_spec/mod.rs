use crate::*;
pub mod eq;
pub mod float;

pub use eq::PureEq;

pub(super) mod type_eq {
    /// A trait which can be used as a bound to say that two types are the same. For
    /// example `Self: TypeEq<Rhs>` can be used as a condition in `PartialEq`.
    pub trait TypeEq<T>: SealedTypeEq<T> {}
    impl<T> TypeEq<T> for T {}

    /// Makes the above trait sealed: it cannot be implemented outside this module.
    trait SealedTypeEq<T> {}
    impl<T> SealedTypeEq<T> for T {}
}

#[extern_spec(core::panicking)]
#[requires(false)]
fn panic(expr: &'static str) -> !;
