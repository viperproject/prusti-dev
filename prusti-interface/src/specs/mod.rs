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
use crate::environment::Environment;
use crate::utils::{has_spec_only_attr, has_extern_spec_attr, read_prusti_attr, has_prusti_attr};

pub mod external;
pub mod typed;

use typed::StructuralToTyped;
use std::fmt;
use crate::specs::external::ExternSpecResolver;
use prusti_specs::specifications::common::SpecificationId;

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
    typed_expressions: HashMap<String, LocalDefId>,
    extern_resolver: ExternSpecResolver<'tcx>,
}

impl<'tcx> SpecCollector<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx: tcx,
            spec_items: Vec::new(),
            typed_expressions: HashMap::new(),
            extern_resolver: ExternSpecResolver::new(tcx),
        }
    }

    pub fn determine_typed_procedure_specs(self) -> typed::SpecificationMap<'tcx> {
        let typed_expressions = self.typed_expressions;
        let tcx = self.tcx;
        self.spec_items
            .into_iter()
            .map(|spec_item| {
                let assertion = reconstruct_typed_assertion(
                    spec_item.specification,
                    &typed_expressions,
                    tcx
                );
                (spec_item.spec_id, assertion)
            })
            .collect()
    }

    pub fn determine_extern_procedure_specs(&self, env: &Environment<'tcx>) -> typed::ExternSpecificationMap<'tcx> {
        self.extern_resolver.check_duplicates(env);
        self.extern_resolver.get_extern_fn_map()
    }
}

fn reconstruct_typed_assertion<'tcx>(
    assertion: JsonAssertion,
    typed_expressions: &HashMap<String, LocalDefId>,
    tcx: TyCtxt<'tcx>
) -> typed::Assertion<'tcx> {
    assertion.to_typed(typed_expressions, tcx)
}

fn deserialize_spec_from_attrs(attrs: &[ast::Attribute]) -> JsonAssertion {
    let json_string = read_prusti_attr("assertion", attrs)
        .expect("could not find prusti::assertion");
    JsonAssertion::from_json_string(&json_string)
}

impl<'tcx> intravisit::Visitor<'tcx> for SpecCollector<'tcx> {
    type Map = Map<'tcx>;

    fn nested_visit_map(&mut self) -> intravisit::NestedVisitorMap<Self::Map> {
        let map = self.tcx.hir();
        intravisit::NestedVisitorMap::All(map)
    }

    fn visit_fn(
        &mut self,
        fn_kind: intravisit::FnKind<'tcx>,
        fn_decl: &'tcx rustc_hir::FnDecl,
        body_id: rustc_hir::BodyId,
        span: Span,
        id: rustc_hir::hir_id::HirId,
    ) {
        intravisit::walk_fn(self, fn_kind, fn_decl, body_id, span, id);

        // Collect external function specifications
        if has_extern_spec_attr(fn_kind.attrs()) {
            self.extern_resolver.add_extern_fn(fn_kind, fn_decl, body_id, span, id);
        }

        // Collect a typed expression
        if let Some(expr_id) = read_prusti_attr("expr_id", fn_kind.attrs()) {
            let local_id = self.tcx.hir().local_def_id(id);
            self.typed_expressions.insert(expr_id, local_id);
        }

        // Collect a specification id and its assertion
        if let Some(raw_spec_id) = read_prusti_attr("spec_id", fn_kind.attrs()) {
            let spec_id: SpecificationId = raw_spec_id.try_into()
                .expect("failed conversion to SpecificationId");
            let specification = deserialize_spec_from_attrs(fn_kind.attrs());

            // Detect the kind of specification
            let spec_type = if has_prusti_attr(fn_kind.attrs(), "loop_body_invariant_spec") {
                SpecType::Invariant
            } else {
                let fn_name = match fn_kind {
                    intravisit::FnKind::ItemFn(ref ident, ..) |
                    intravisit::FnKind::Method(ref ident, ..) => ident.name.to_ident_string(),
                    intravisit::FnKind::Closure(..) => unreachable!(
                        "a closure is annotated with prusti::spec_id but not with \
                        prusti::loop_body_invariant_spec"
                    ),
                };
                if fn_name.starts_with("prusti_pre_item_") {
                    SpecType::Precondition
                } else if fn_name.starts_with("prusti_post_item_") {
                    SpecType::Postcondition
                } else {
                    unreachable!()
                }
            };

            let spec_item = SpecItem {spec_id, spec_type, specification};
            self.spec_items.push(spec_item);
        }
    }
}
