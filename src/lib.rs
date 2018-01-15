#![doc(html_root_url = "https://viperproject.github.io/prusti/")]

//! # Prusti: Viper Front-End For Rust.
//!
//! More information about the Viper project can be found
//! [here](viper.ethz.ch).
//!
//! Prusti is a Rust compiler plugin that provides an intermediate layer
//! between the compiler and verification tool. Its main responsibility
//! is to provide a convenient access to program's CFG with contracts.
//!
//! ## Prusti Design
//!
//! Prusti registers attributes for specifying programs:
//! `#[requires="<precondition>"]`, `#[ensures="<postcondition>"]`, and
//! `#[invariant="<loop invariant>"]`. The registration and control of
//! the entire workflow is done by the rustc driver implemented in the
//! `lib/driver.rs`.
//!
//! The Rust compiler exposes procedures for parsing strings into Rust
//! AST, but it does not expose procedures for type-checking AST.
//! Therefore, Prusti rewrites ASTs of annotated procedures in the
//! callback ``after_expand`` to include specifications so that they are
//! type-checked during the regular rustc type-checker's pass. The
//! rewriting logic is defined in the module `parser` and the data
//! structures for storing information about specifications are defined
//! in the module `specifications`.
//!
//! The main Prusti logic is invoked as `after_analysis` callback.
//! During this pass, Prusti reconstructs specifications with types and
//! invokes a verification tool and gives it a facade trait that can be
//! used by the verification tool to query Prusti for all needed
//! information. This trait is defined in the crate `prusti_interface`.

#![warn(missing_docs)]

#![feature(plugin_registrar)]
#![feature(quote)]
#![feature(box_syntax)]
#![feature(rustc_private)]
#![feature(macro_vis_matcher)]
#![feature(try_from)]
#![feature(i128_type)]

#[macro_use]
extern crate log;
extern crate prusti_contracts;
extern crate regex;
#[macro_use]
extern crate rustc;
extern crate rustc_driver;
extern crate syntax;
extern crate syntax_pos;

pub mod specifications;
pub mod parser;
pub mod ast_builder;
