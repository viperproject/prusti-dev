#[macro_use]
extern crate log;
extern crate jni;

#[macro_use]
mod macros;

pub mod java;
pub mod scala;
pub mod viper_ast;
pub mod verifier;
pub mod jvm;

#[path = "../gen/mod.rs"]
mod wrappers;
