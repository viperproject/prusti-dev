#![feature(box_patterns)]
#![feature(box_syntax)]
#![feature(decl_macro)]
#![allow(unused_imports)]
#![deny(unused_must_use)]
#![deny(unreachable_patterns)]
#![deny(unused_mut)]
#![deny(unused_variables)]
#![deny(unused_doc_comments)]

#[rustfmt::skip]
#[path = "../gen/mod.rs"]
mod gen;

pub mod common;
pub mod converter;
/// VIR that is as close to MIR as possible.
pub mod high;
/// Effectively Viper.
pub mod low;
/// Fold-unfold operations are inferred.
pub mod middle;
/// Reduce the number of types. For example, tuples and structs are unified.
pub mod typed;

/// Monomorphized legacy.
pub mod legacy;
/// Polymorphic legacy.
pub mod polymorphic;
