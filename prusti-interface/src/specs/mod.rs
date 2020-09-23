use prusti_specs::specifications::{json::Assertion as JsonAssertion, SpecType};
use rustc_ast::ast;
use rustc_hir::{intravisit, ItemKind};
use rustc_middle::hir::map::Map;
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;
use rustc_span::symbol::Symbol;
use rustc_hir::def_id::LocalDefId;
use std::collections::HashMap;
use std::convert::TryInto;
use crate::utils::{has_spec_only_attr, has_extern_spec_attr};
use crate::environment::Environment;

pub mod external;
pub mod typed;

use typed::StructuralToTyped;
use std::fmt;
use crate::specs::external::ExternSpecResolver;

struct SpecItem {
    spec_id: typed::SpecificationId,
    spec_type: SpecType,
    specification: JsonAssertion,
}

impl fmt::Debug for SpecItem {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SpecItem")
         .field("spec_id", &self.spec_id)
         .finish()
    }
}

struct Item<'tcx> {
    name: Symbol,
    attrs: &'tcx [ast::Attribute],
}

pub struct SpecCollector<'tcx> {
    tcx: TyCtxt<'tcx>,
    spec_items: Vec<SpecItem>,
    current_spec_item: Option<SpecItem>,
    typed_expressions: HashMap<String, LocalDefId>,
    resolver: ExternSpecResolver<'tcx>,
}

impl<'tcx> SpecCollector<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx: tcx,
            spec_items: Vec::new(),
            current_spec_item: None,
            typed_expressions: HashMap::new(),
            resolver: ExternSpecResolver::new(tcx),
        }
    }
    pub fn determine_typed_procedure_specs(self) -> typed::SpecificationMap<'tcx> {
        let typed_expressions = self.typed_expressions;
        let tcx = self.tcx;
        self.spec_items
            .into_iter()
            .map(|spec_item| {
                let assertion = typed::SpecificationMapElement::Assertion(reconstruct_typed_assertion(
                    spec_item.specification,
                    &typed_expressions,
                    tcx
                ));
                (spec_item.spec_id, assertion)
            })
            .collect()
    }
    
    fn process_item(&mut self, item: Item) {
        if has_spec_only_attr(item.attrs) {
            assert!(
                self.current_spec_item.is_none(),
                "nested specification item?"
            );
            let fn_name = item.name.to_ident_string();
            let spec_type = if fn_name.starts_with("prusti_pre_item_") {
                SpecType::Precondition
            } else if fn_name.starts_with("prusti_post_item_") {
                SpecType::Postcondition
            } else {
                unreachable!();
            };
            let spec_item = SpecItem {
                spec_id: read_prusti_attr("spec_id", item.attrs)
                    .expect("missing spec_id on spec item")
                    .try_into()
                    .unwrap(),
                spec_type: spec_type,
                specification: deserialize_spec_from_attrs(item.attrs),
            };
            assert!(self.current_spec_item.is_none());
            self.current_spec_item = Some(spec_item);
        }
    }

    pub fn determine_extern_procedure_specs(&self, env: &Environment<'tcx>) -> typed::ExternSpecificationMap<'tcx> {
        self.resolver.check_duplicates(env);
        self.resolver.get_extern_fn_map()
    }
}

fn reconstruct_typed_assertion<'tcx>(
    assertion: JsonAssertion,
    typed_expressions: &HashMap<String, LocalDefId>,
    tcx: TyCtxt<'tcx>
) -> typed::Assertion<'tcx> {
    assertion.to_typed(typed_expressions, tcx)
}

/// Read the value stored in a Prusti attribute (e.g. `prusti::<attr_name>="...")`.
fn read_prusti_attr(attr_name: &str, attrs: &[ast::Attribute]) -> Option<String> {
    let mut string = None;
    for attr in attrs {
        if let ast::AttrKind::Normal(ast::AttrItem {
            path: ast::Path { span: _, segments, tokens: _ },
            args: ast::MacArgs::Eq(_, tokens),
            tokens: _,
        }) = &attr.kind {
            // Skip attributes whose path don't match with "prusti::<attr_name>"
            if !(
                segments.len() == 2 &&
                segments[0].ident.name.with(|name| name == "prusti") &&
                segments[1].ident.name.with(|name| name == attr_name)
            ) {
                continue;
            }
            use rustc_ast::token::Lit;
            use rustc_ast::token::Token;
            use rustc_ast::token::TokenKind;
            use rustc_ast::tokenstream::TokenTree;
            match &tokens.0[0].0 {
                TokenTree::Token(Token {
                    kind: TokenKind::Literal(Lit { symbol, .. }),
                    ..
                }) => {
                    assert!(string.is_none(), "string={:?} attr={:?}", string, attr);
                    string = Some(symbol.as_str());
                }
                x => unreachable!("{:?}", x),
            }
        };
    }
    string.map(|s| s.replace("\\\"", "\""))
}

fn deserialize_spec_from_attrs(attrs: &[ast::Attribute]) -> JsonAssertion {
    let json_string = read_prusti_attr("assertion", attrs).expect("could not find prusti::assertion");
    JsonAssertion::from_json_string(&json_string)
}

impl<'tcx> intravisit::Visitor<'tcx> for SpecCollector<'tcx> {
    type Map = Map<'tcx>;
    fn nested_visit_map(&mut self) -> intravisit::NestedVisitorMap<Self::Map> {
        let map = self.tcx.hir();
        intravisit::NestedVisitorMap::All(map)
    }

    fn visit_item(&mut self, item: &'tcx rustc_hir::Item<'tcx>) {
        if let ItemKind::Impl {items, ..} = &item.kind {
            for impl_item_ref in items.iter() {
                let impl_item = self.tcx.hir().impl_item(impl_item_ref.id);
                self.process_item(
                    Item {attrs: impl_item.attrs, name: impl_item.ident.name}
                );
                intravisit::walk_impl_item(self, impl_item);
                if let Some(spec_item) = self.current_spec_item.take() {
                    self.spec_items.push(spec_item);
                }
            }
            return;
        }
        self.process_item(Item {attrs: item.attrs, name: item.ident.name});
        intravisit::walk_item(self, item);
        if let Some(spec_item) = self.current_spec_item.take() {
            self.spec_items.push(spec_item);
        }
    }

    fn visit_fn(
        &mut self,
        fn_kind: intravisit::FnKind<'tcx>,
        fn_decl: &'tcx rustc_hir::FnDecl,
        body_id: rustc_hir::BodyId,
        span: Span,
        id: rustc_hir::hir_id::HirId,
    ) {
        if self.current_spec_item.is_some() {
            if read_prusti_attr("spec_id", fn_kind.attrs()).is_none() {
                let expr_id = read_prusti_attr("expr_id", fn_kind.attrs()).unwrap();
                let local_id = self.tcx.hir().local_def_id(id);
                self.typed_expressions.insert(expr_id, local_id);
            }
        } else if has_extern_spec_attr(fn_kind.attrs()) {
            self.resolver.add_extern_fn(fn_kind, fn_decl, body_id, span, id);
        }
        intravisit::walk_fn(self, fn_kind, fn_decl, body_id, span, id);
    }

    fn visit_local(&mut self, local: &'tcx rustc_hir::Local<'tcx>) {
        let mut clean_spec_item = false;
        if has_spec_only_attr(&local.attrs) {
            let spec_item = SpecItem {
                spec_id: read_prusti_attr("spec_id", &local.attrs)
                    .expect("missing spec_id on invariant")
                    .try_into()
                    .unwrap(),
                spec_type: SpecType::Invariant,
                specification: deserialize_spec_from_attrs(&local.attrs),
            };
            assert!(self.current_spec_item.is_none());
            self.current_spec_item = Some(spec_item);
            clean_spec_item = true;
        }
        intravisit::walk_local(self, local);
        if clean_spec_item {
            let spec_item = self.current_spec_item.take().unwrap();
            self.spec_items.push(spec_item);
        }
    }
}
