use prusti_specs::specifications::{json::Assertion as JsonAssertion, SpecType};
use rustc_ast::ast;
use rustc_hir::def_id::DefId;
use rustc_hir::definitions::{DefPath, DefPathData};
use rustc_hir::intravisit;
use rustc_middle::hir::map::Map;
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;
use std::collections::HashMap;
use std::fmt::Write;

mod typed;

use typed::StructuralToTyped;

struct SpecItem {
    spec_type: SpecType,
    def_path: DefPath,
    specification: JsonAssertion,
}

struct Item {
    def_id: DefId,
    def_path: DefPath,
}

pub(crate) struct SpecCollector<'tcx> {
    tcx: TyCtxt<'tcx>,
    spec_items: Vec<SpecItem>,
    current_spec_item: Option<SpecItem>,
    items: Vec<Item>,
    typed_expressions: HashMap<String, rustc_hir::BodyId>,
}

impl<'tcx> SpecCollector<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx: tcx,
            spec_items: Vec::new(),
            current_spec_item: None,
            items: Vec::new(),
            typed_expressions: HashMap::new(),
        }
    }
    pub fn determine_typed_procedure_specs(self) -> HashMap<DefId, typed::ProcedureSpecification> {
        fn def_path_to_string_split(mut def_path: DefPath) -> (String, String) {
            let krate = def_path.krate;
            let mut path = String::with_capacity(def_path.data.len() * 16);
            let fn_name = match def_path.data.pop().unwrap().data {
                DefPathData::ValueNs(symbol) => symbol.as_str().to_string(),
                _ => unreachable!(),
            };
            write!(path, "{}", krate).unwrap();
            for component in def_path.data {
                write!(
                    path,
                    "::{}[{}]",
                    component.data.as_symbol(),
                    component.disambiguator
                )
                .unwrap();
            }
            (path, fn_name)
        }
        let mut item_map: HashMap<_, _> = self
            .items
            .into_iter()
            .map(|Item { def_id, def_path }| {
                let (path, fn_name) = def_path_to_string_split(def_path);
                (
                    (path, fn_name),
                    (def_id, typed::ProcedureSpecification::empty()),
                )
            })
            .collect();

        for spec_item in self.spec_items.into_iter() {
            let (path, spec_fn_name) = def_path_to_string_split(spec_item.def_path);
            match spec_item.spec_type {
                SpecType::Precondition => {
                    // Drop the prefix and the hash.
                    let fn_name = spec_fn_name[16..spec_fn_name.len() - 33].to_string();
                    let (_, spec) = item_map.get_mut(&(path, fn_name)).unwrap();
                    spec.pres.push(reconstruct_typed_assertion(
                        spec_item.specification,
                        &self.typed_expressions,
                    ));
                }
                SpecType::Postcondition => {
                    // Drop the prefix and the hash.
                    let fn_name = spec_fn_name[17..spec_fn_name.len() - 33].to_string();
                    let (_, spec) = item_map.get_mut(&(path, fn_name)).unwrap();
                    spec.posts.push(reconstruct_typed_assertion(
                        spec_item.specification,
                        &self.typed_expressions,
                    ));
                }
                _ => {
                    unreachable!();
                }
            };
        }
        item_map
            .into_iter()
            .map(|(_, (def_id, spec))| (def_id, spec))
            .collect()
    }
}

fn reconstruct_typed_assertion<'tcx>(
    assertion: JsonAssertion,
    typed_expressions: &HashMap<String, rustc_hir::BodyId>,
) -> typed::Assertion {
    assertion.to_typed(typed_expressions)
}

fn read_doc_attr(attrs: &[ast::Attribute]) -> String {
    let mut string = None;
    for attr in attrs {
        match &attr.kind {
            ast::AttrKind::DocComment(symbol) => {
                assert!(string.is_none());
                string = Some(symbol.as_str());
            },
            ast::AttrKind::Normal(ast::AttrItem {
                path: ast::Path { span:_, segments },
                args: ast::MacArgs::Eq(_, tokens),
            }) => {
                if segments.len() != 1 || segments[0].ident.name.with(|attr_name| attr_name != "doc") {
                    unreachable!();
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
                        assert!(string.is_none());
                        string = Some(symbol.as_str());
                    },
                    x => unreachable!("{:?}", x),
                }
            }
            ast::AttrKind::Normal(ast::AttrItem {
                path: ast::Path { span:_, segments },
                args: _,
            }) if segments.len() == 1 || segments[0].ident.name.with(|attr_name| attr_name != "allow") => {
                continue;
            }
            x => unreachable!("{:?}", x),
        };
    }
    string.expect("no specification structure attribute?").replace("\\\"", "\"")
}

fn deserialize_spec_from_attrs(attrs: &[ast::Attribute]) -> JsonAssertion {
    let json_string = read_doc_attr(attrs);
    JsonAssertion::from_json_string(&json_string)
}

impl<'tcx> intravisit::Visitor<'tcx> for SpecCollector<'tcx> {
    type Map = Map<'tcx>;
    fn nested_visit_map<'this>(&'this mut self) -> intravisit::NestedVisitorMap<Self::Map> {
        let map = self.tcx.hir();
        intravisit::NestedVisitorMap::All(map)
    }
    fn visit_item(&mut self, item: &'tcx rustc_hir::Item<'tcx>) {
        let local_def_id = self.tcx.hir().opt_local_def_id(item.hir_id).unwrap();
        let def_id = local_def_id.to_def_id();
        let def_path = self.tcx.def_path(def_id);
        match &item.kind {
            rustc_hir::ItemKind::Fn(_sig, _generics, _body_id) => {
                let fn_name = item.ident.name.to_ident_string();
                let spec_type = if fn_name.starts_with("prusti_pre_item_") {
                    Some(SpecType::Precondition)
                } else if fn_name.starts_with("prusti_post_item_") {
                    Some(SpecType::Postcondition)
                } else {
                    None
                };
                if let Some(spec_type) = spec_type {
                    let spec_item = SpecItem {
                        spec_type: spec_type,
                        def_path: def_path,
                        specification: deserialize_spec_from_attrs(item.attrs),
                    };
                    assert!(self.current_spec_item.is_none());
                    self.current_spec_item = Some(spec_item);
                } else {
                    self.items.push(Item { def_id, def_path });
                }
            }
            _ => {}
        }
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
        if let Some(_spec_item) = self.current_spec_item.as_mut() {
            let expr_id = read_doc_attr(fn_kind.attrs());
            self.typed_expressions.insert(expr_id, body_id);
        }
        intravisit::walk_fn(self, fn_kind, fn_decl, body_id, span, id);
    }
}
