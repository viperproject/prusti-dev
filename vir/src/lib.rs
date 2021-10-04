#![feature(box_patterns)]
#![feature(box_syntax)]
#![allow(unused_imports)]
#![deny(unused_must_use)]
#![deny(unreachable_patterns)]
#![deny(unused_mut)]
#![deny(unused_variables)]
#![deny(unused_doc_comments)]

#[macro_use]
extern crate log;
#[macro_use]
extern crate lazy_static;
#[macro_use]
extern crate serde;

#[rustfmt::skip]
#[path = "../gen/vir_gen.rs"]
mod gen;
pub use gen::*;

pub mod converter;
pub mod legacy;
