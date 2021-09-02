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

// https://github.com/rust-analyzer/rust-analyzer/issues/1964
//
// To enable autocompletion of the generated code, please add
// `"rust-analyzer.cargo.loadOutDirsFromCheck": true` to your VS Code settings.
include!(concat!(env!("OUT_DIR"), "/vir_gen.rs"));

pub mod converter;
pub mod legacy;
