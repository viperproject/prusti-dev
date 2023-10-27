#![feature(try_blocks)]
#![feature(let_chains)]

pub mod verifier;
mod smt_lib;
mod theory_provider;
mod optimization;
mod fol;

pub use crate::verifier::*;
