//! This is a Prusti wrapper around Rustc's interface until
//! https://github.com/rust-lang/project-stable-mir/tree/smir is completely
//! ready.

#![feature(rustc_private)]

extern crate rustc_smir;

pub extern crate polonius_engine as polonius_engine;
pub extern crate rustc_ast as ast;
pub extern crate rustc_attr as attr;
pub extern crate rustc_data_structures as data_structures;
pub extern crate rustc_driver as driver;
pub extern crate rustc_errors as errors;
pub extern crate rustc_index as index;
pub extern crate rustc_infer as infer;
pub extern crate rustc_interface as interface;
pub extern crate rustc_session as session;
pub extern crate rustc_span as span;
pub extern crate rustc_target as target;

pub use rustc_smir::very_unstable::{borrowck, dataflow, hir, middle, trait_selection};
