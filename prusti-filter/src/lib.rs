#![feature(rustc_private)]
#![feature(box_syntax)]
#![feature(box_patterns)]

extern crate env_logger;
extern crate log;
extern crate rustc;
extern crate rustc_plugin;
extern crate syntax;

pub mod validators;
