#![feature(rustc_private)]
#![feature(never_type)]
#![feature(iter_intersperse)]
#![feature(unboxed_closures, fn_traits, tuple_trait)]
#![feature(macro_metavar_expr)]
#![allow(clippy::needless_lifetimes)]

mod context;
mod data;
mod debug;
mod debug_info;
mod gendata;
mod genrefs; // TODO: explain gen...
pub mod macros;
mod make;
mod refs;
mod reify;
mod serde;
mod spans;
// mod callable_idents;
mod callable;
mod viper_ident;
mod r#type;

// pub use callable_idents::*;
pub use callable::*;
pub use context::*;
pub use data::*;
pub use gendata::*;
pub use genrefs::*;
pub use r#type::*;
pub use refs::*;
pub use reify::*;
pub use spans::VirSpan;
pub use viper_ident::*;

// for all arena-allocated types, there are two type definitions: one with
// a `Data` suffix, containing the actual data; and one without the suffix,
// being shorthand for a VIR-lifetime reference to the data.
