pub mod pure;
pub mod indirect;
pub mod impure;
pub mod kinds;
pub mod use_impure;
pub mod use_pure;
pub mod viper_tuple;

pub mod lifted;
pub mod generics;
mod data;
mod rust_ty;
pub mod interpretation;
pub mod interior_mut;

pub use data::TySpecifics;
pub use rust_ty::*;

/// Defines the collection of datas which are output by the Viper type encoders.
/// For `P = Pure`, this is e.g. the domain/adt FunctionIdn etc.
/// For `P = Impure`, this is e.g. the PredicateIdn etc.
#[derive(Debug, Clone, Copy)]
pub struct ViperTyDatas<P: super::Purity>(std::marker::PhantomData<P>);

/// Defines the collection of datas which are output by the "use" type encoders.
/// For `P = Pure`, this is e.g. the cast functions for all generic fields.
/// For `P = Impure`, this is e.g. the cast methods for all generic fields.
#[derive(Debug, Clone, Copy)]
pub struct UseTyDatas<P: super::Purity>(std::marker::PhantomData<P>);

pub struct TyEnc<P: super::Purity>(std::marker::PhantomData<P>);

pub struct TyUseEnc<P: super::Purity>(std::marker::PhantomData<P>);
