#![feature(rustc_private)]
#![feature(box_syntax)]
#![feature(box_patterns)]

extern crate env_logger;
#[macro_use]
extern crate log;
extern crate rustc;
extern crate rustc_plugin;
extern crate syntax;

extern crate serde;
extern crate serde_json;
#[macro_use]
extern crate serde_derive;

pub mod validators;
