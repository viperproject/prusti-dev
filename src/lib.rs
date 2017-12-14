#[macro_use]
extern crate log;
extern crate jni;

#[macro_use]
extern crate error_chain;

#[macro_use]
mod macros;

pub mod errors;
mod utils;
mod module_tree;
mod unordered_set_eq;
mod gen_object_getter;
mod gen_constructors;
mod gen_methods;
mod gen_class;
mod gen_mod;
mod wrapper_generator;

pub use wrapper_generator::*;
