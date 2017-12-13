#![feature(plugin_registrar)]
#![feature(box_syntax, rustc_private)]
#![feature(macro_vis_matcher)]

#[macro_use]
extern crate log;
extern crate env_logger;

extern crate syntax;

#[macro_use]
extern crate rustc;
extern crate rustc_plugin;

use std::sync::{Arc, Mutex};

use syntax::ast;
use syntax::ext::base::{ExtCtxt, MultiModifier, Annotatable};
use syntax::ext::quote::rt::ExtParseUtils;
use syntax::codemap::Span;
use rustc::hir;
use rustc::lint::{LateContext, LintPass, LateLintPass,
                  LateLintPassObject, LintArray};
use rustc_plugin::Registry;

pub mod specifications;

declare_lint!(PRUSTI_LINT, Warn, "Warn about verification errors.");

struct Pass {
    specs: Arc<Mutex<specifications::SpecificationManager>>,
}

impl Pass {

    pub fn new() -> Pass {
        Pass {
            specs: Arc::new(Mutex::new(specifications::SpecificationManager::new())),
        }
    }

}

impl LintPass for Pass {
    fn get_lints(&self) -> LintArray {
        lint_array!(PRUSTI_LINT)
    }
}

impl<'a, 'tcx> LateLintPass<'a, 'tcx> for Pass {

    fn check_crate_post(&mut self, _cx: &LateContext<'a, 'tcx>,
                        _: &'tcx hir::Crate) {
        trace!("[check_crate_post] enter");
        trace!("[check_crate_post] exit");
    }
}

#[plugin_registrar]
pub fn plugin_registrar(reg: &mut Registry) {
    env_logger::init();
    error!("this is printed by default");
    let pass = box Pass::new();
    let specs = pass.specs.clone();
    reg.register_late_lint_pass(pass as LateLintPassObject);
    register_syntax_extension(reg, "requires", specs.clone());
    register_syntax_extension(reg, "ensures", specs.clone());
    register_syntax_extension(reg, "invariant", specs.clone());
}

fn register_syntax_extension(reg: &mut Registry, name: &str,
                             specs: Arc<Mutex<specifications::SpecificationManager>>) {
    reg.register_syntax_extension(
        ast::Name::intern(name),
        MultiModifier(Box::new(move |cx: &mut ExtCtxt,
                               span: Span,
                               attr: &ast::MetaItem,
                               item: Annotatable| -> Annotatable {
        match &attr.node {
            &ast::MetaItemKind::NameValue(ref lit) => {
                match lit.node {
                    ast::LitKind::Str(ref lit, _) => {
                        let mut specs = specs.lock().unwrap();
                        let expr = cx.parse_expr(lit.to_string().clone());
                        specs.add_specification(
                            attr.name,
                            item.clone().expect_item().ident,
                            span,
                            lit.to_string(),
                            expr,
                        );
                    },
                    _ => {panic!("Unrecognized attribute literal: {:?}", lit.node)},
                }
            },
            _ => {panic!("Unrecognized attribute: {:?}", attr.node)},
        }
        item
    })));
}
