use crate::*;

pub mod cell;
pub mod default;
pub mod eq;
pub mod float;
pub mod result;
pub mod slice;
pub mod ref_cell;

pub use eq::PureEq;

/// The current value of the interior-mutable object `ptr` points to (the
/// pointer returned by an `#[interior_mut]` accessor). This is the one
/// primitive read of interior-mutable state: Prusti defines it as the lookup
/// of the object in the interior-mutability snapshot of the enclosing
/// `#[pure_unstable]` function, so accessors that alias the same object read
/// the same value. Only meaningful inside `#[pure_unstable]` functions whose
/// arguments reach the object.
#[trusted]
#[pure_unstable]
#[cfg_attr(feature = "prusti", prusti::im_deref)]
pub fn im_deref<'a, T: ?Sized>(_ptr: *const T) -> &'a T {
    unimplemented!()
}

pub(super) mod type_eq {
    /// A trait which can be used as a bound to say that two types are the same. For
    /// example `Self: TypeEq<Rhs>` can be used as a condition in `PartialEq`.
    #[allow(private_bounds)]
    pub trait TypeEq<T>: SealedTypeEq<T> {}
    impl<T> TypeEq<T> for T {}

    /// Makes the above trait sealed: it cannot be implemented outside this module.
    trait SealedTypeEq<T> {}
    impl<T> SealedTypeEq<T> for T {}
}

#[extern_spec(core::panicking)]
#[trusted]
#[requires(false)]
#[pure]
fn panic(expr: &'static str) -> !;

#[extern_spec(core::panicking)]
#[trusted]
#[requires(false)]
pub fn assert_failed<T, U>(
    kind: core::panicking::AssertKind,
    left: &T,
    right: &U,
    args: Option<core::fmt::Arguments<'_>>,
) -> !
where
    T: core::fmt::Debug + ?Sized,
    U: core::fmt::Debug + ?Sized;
