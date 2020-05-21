#![feature(rustc_private)]

extern crate rustc_driver;

pub struct PrustiCompilerCalls {}

impl rustc_driver::Callbacks for PrustiCompilerCalls {}
