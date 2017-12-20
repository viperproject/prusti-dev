#![doc(html_root_url = "https://viperproject.github.io/prusti/")]

//! # Prusti: Viper Front-End For Rust.
//!
//! More information about the Viper project can be found
//! [here](viper.ethz.ch).
//!
//! Prusti is a Rust compiler plugin that provides an intermediate layer
//! between the compiler and verification tool. Its main responsibility is
//! to provide a convenient access to program's CFG with contracts.
//!
//! ## Prusti Design
//!
//! Prusti registers attributes for specifying programs:
//! `#[requires="<precondition>"]`, `#[ensures="<postcondition>"]`, and
//! `#[invariant="<loop invariant>"]`. `requires` and `ensures` attributes
//! are registered as `syntax::ext::base::SyntaxExtension::MultiModifier` by
//! using `register_syntax_extension`. The `invariant` attribute is
//! registered with `register_attribute` because only the top level
//! items can annotated with syntax extensions. As a result, rewriting
//! invariants (see below) works only if a procedure is annotated with
//! `requires` or `ensures` attribute.
//!
//! The Rust compiler exposes procedures for parsing strings into Rust AST,
//! but it does not expose procedures for type-checking AST. Therefore, Prusti
//! rewrites ASTs of annotated procedures (by using registered `MultiModifier`)
//! to include specifications so that they are type-checked during the regular
//! rustc type-checker's pass. The rewriting logic is defined in the module
//! `parser` and the data structures for storing information about
//! specifications are defined in the module `specifications`.
//!
//! The main Prusti logic is invoked as a late lint pass. During this pass,
//! Prusti invokes a verification tool and gives it a facade trait that can
//! be used by the verification tool to query Prusti for all needed
//! information. This trait is defined in the crate `prusti_interface`.

#![feature(plugin_registrar)]
#![feature(quote)]
#![feature(box_syntax)]
#![feature(rustc_private)]
#![feature(macro_vis_matcher)]
#![feature(try_from)]

#[macro_use]
extern crate log;
extern crate env_logger;

extern crate syntax;

#[macro_use]
extern crate rustc;
extern crate rustc_plugin;

extern crate prusti_contracts;

use std::sync::{Arc, Mutex};

use syntax::ast;
use syntax::feature_gate::AttributeType;
use syntax::ext::base::{ExtCtxt, MultiModifier, Annotatable};
use syntax::codemap::Span;
use rustc::hir;
use rustc::lint::{LateContext, LintPass, LateLintPass,
                  LateLintPassObject, LintArray};
use rustc_plugin::Registry;

pub mod specifications;
pub mod parser;

declare_lint!(PRUSTI_LINT, Warn, "Warn about verification errors.");

type MSpecParser = Arc<Mutex<parser::SpecParser>>;

struct Pass {
    spec_parser: Option<MSpecParser>,
}

impl Pass {

    pub fn new() -> Pass {
        Pass {
            spec_parser: Some(Arc::new(Mutex::new(parser::SpecParser::new()))),
        }
    }

}

impl LintPass for Pass {
    fn get_lints(&self) -> LintArray {
        lint_array!(PRUSTI_LINT)
    }
}

impl<'a, 'tcx> LateLintPass<'a, 'tcx> for Pass {

    fn check_crate_post(&mut self,
                        _cx: &LateContext<'a, 'tcx>,
                        _krate: &'tcx hir::Crate) {
        trace!("[check_crate_post] enter");
        trace!("[check_crate_post] exit");
    }
}

#[plugin_registrar]
pub fn plugin_registrar(reg: &mut Registry) {
    env_logger::init().unwrap();
    let pass = box Pass::new();
    let parser = pass.spec_parser.clone().unwrap();
    reg.register_late_lint_pass(pass as LateLintPassObject);
    register_syntax_extension(reg, "requires", parser.clone());
    register_syntax_extension(reg, "ensures", parser.clone());
    reg.register_attribute(String::from("invariant"), AttributeType::Whitelisted);
    reg.register_attribute(String::from("__PRUSTI_SPEC"), AttributeType::Whitelisted);
}

fn register_syntax_extension(reg: &mut Registry, name: &str, spec_parser: MSpecParser) {
    reg.register_syntax_extension(
        ast::Name::intern(name),
        MultiModifier(Box::new(
            move |
                cx: &mut ExtCtxt,
                span: Span,
                attr: &ast::MetaItem,
                item: Annotatable| -> Vec<Annotatable> {

                let mut spec_parser = spec_parser.lock().unwrap();
                let items = spec_parser.expand_specifications(cx, span, attr, item);
                for item in items.iter() {
                    match item {
                        &Annotatable::Item(ref item) => {
                            println!("------------\n{}",
                                     syntax::print::pprust::item_to_string(item));
                        },
                        _ => {unreachable!();},
                    }
                }
                items
            }
        )));
}
