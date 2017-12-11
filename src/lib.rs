#![feature(plugin_registrar)]
#![feature(box_syntax, rustc_private)]
#![feature(macro_vis_matcher)]

extern crate syntax;

#[macro_use]
extern crate rustc;
extern crate rustc_plugin;

use syntax::ast;
use syntax::ext::base::{ExtCtxt, MultiModifier, Annotatable};
use syntax::ext::quote::rt::ExtParseUtils;
use syntax::codemap::Span;
use rustc::hir;
use rustc::lint::{LateContext, LintPass, LateLintPass,
                  LateLintPassObject, LintArray};
use rustc_plugin::Registry;

declare_lint!(PRUSTI_LINT, Warn, "Warn about verification errors.");

struct Pass;

impl LintPass for Pass {
    fn get_lints(&self) -> LintArray {
        lint_array!(PRUSTI_LINT)
    }
}

impl<'a, 'tcx> LateLintPass<'a, 'tcx> for Pass {

    fn check_crate_post(&mut self, _cx: &LateContext<'a, 'tcx>,
                        _: &'tcx hir::Crate) {
        println!("It works!");
    }
}

#[plugin_registrar]
pub fn plugin_registrar(reg: &mut Registry) {
    reg.register_late_lint_pass(box Pass as LateLintPassObject);
    reg.register_syntax_extension(
        ast::Name::intern("requires"),
        MultiModifier(Box::new(requires)));
}

fn requires(cx: &mut ExtCtxt,
           _sp: Span,
           attr: &ast::MetaItem,
           item: Annotatable)
    -> Annotatable
{
    match &attr.node {
        &ast::MetaItemKind::NameValue(ref lit) => {
            match lit.node {
                ast::LitKind::Str(ref lit, _) => {
                    let spec = lit.to_string();
                    let expr = cx.parse_expr(spec.clone());
                    println!("{}({:?}) on {:?}",
                        attr.name, expr, item.clone().expect_item().ident);
                },
                _ => {},
            }
        },
        _ => {},
    }
    item
}
