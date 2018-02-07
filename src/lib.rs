// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![doc(html_root_url = "https://viperproject.github.io/prusti/")]

//! Prusti is a Rust compiler driver that provides an intermediate layer
//! between the compiler and verification tool. Its main responsibility
//! is to provide a convenient access to program's CFG with contracts.
//!
//! # Prusti Design
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
//! callback ``after_parse`` to include specifications so that they are
//! type-checked during the regular rustc type-checker's pass. The
//! rewriting logic is defined in the modules `parser` and `typeck` and
//! the data structures for storing information about specifications are
//! defined in the module `specifications`. Please see the documentation
//! of the module `parser` for more information.
//!
//! The main Prusti logic is invoked as `after_analysis` callback.
//! During this pass, Prusti reconstructs specifications with types and
//! invokes a verification tool and gives it a facade trait that can be
//! used by the verification tool to query Prusti for all needed
//! information. This trait is defined in the crate `prusti_interface`.
//!
//! TODO: Implement `prusti_interface`.

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
extern crate prusti_interface;
extern crate prusti_viper;
extern crate regex;
#[macro_use]
extern crate rustc;
extern crate rustc_driver;
extern crate syntax;
extern crate syntax_pos;

pub mod ast_builder;
pub mod specifications;
pub mod parser;
pub mod typeck;
pub mod verifier;
pub mod environment;
pub mod hir_visitor;
