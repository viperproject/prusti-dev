#![recursion_limit = "1024"]

#[macro_use]
extern crate error_chain;
extern crate jni;
#[macro_use]
extern crate log;
extern crate uuid;
extern crate viper_sys;

mod viper;
mod verification_context;
mod ast_factory;
mod verification_result;
mod verifier;
mod jni_utils;
mod ast_utils;
mod cfg_method;
pub mod errors;

pub use viper::*;
pub use verification_context::*;
pub use ast_factory::*;
pub use verification_result::*;
pub use ast_utils::*;
pub use cfg_method::*;
