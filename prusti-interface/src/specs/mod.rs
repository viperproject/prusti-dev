use prusti_specs::specifications::{json::Assertion as JsonAssertion, SpecType};
use rustc_ast::ast;
use rustc_hir::{intravisit, ItemKind};
use rustc_middle::hir::map::Map;
use rustc_middle::ty::TyCtxt;
use rustc_span::{Span, MultiSpan};
use rustc_span::symbol::Symbol;
use rustc_hir::def_id::{DefId, LocalDefId};
use std::collections::HashMap;
use std::convert::TryInto;
use crate::environment::Environment;
use crate::PrustiError;
use crate::utils::{
    has_spec_only_attr, has_extern_spec_attr, read_prusti_attr, read_prusti_attrs, has_prusti_attr
};
use log::debug;

pub mod external;
pub mod typed;
pub mod checker;

use typed::StructuralToTyped;
use typed::SpecIdRef;
use std::fmt;
use crate::specs::external::ExternSpecResolver;
use prusti_specs::specifications::common::SpecificationId;

struct SpecItem {
    spec_id: typed::SpecificationId,
    #[allow(dead_code)]
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

struct ProcedureSpecRef {
    spec_id_refs: Vec<prusti_specs::specifications::common::SpecIdRef>,
    pure: bool,
    trusted: bool,
}

/// Specification collector, intended to be applied as a visitor over the crate
/// HIR. After the visit, [determine_def_specs] can be used to get back
/// a mapping of DefIds (which may not be local due to extern specs) to their
/// [SpecificationSet], i.e. procedures, loop invariants, and structs.
pub struct SpecCollector<'tcx> {
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> SpecCollector<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx: tcx,
        }
    }

    pub fn build_def_specs(mut self, env: &Environment<'tcx>) -> typed::DefSpecificationMap<'tcx> {
        typed::DefSpecificationMap::new()
    }
}

impl<'tcx> intravisit::Visitor<'tcx> for SpecCollector<'tcx> {
    type Map = Map<'tcx>;

    fn nested_visit_map(&mut self) -> intravisit::NestedVisitorMap<Self::Map> {
        let map = self.tcx.hir();
        intravisit::NestedVisitorMap::All(map)
    }

    fn visit_trait_item(
        &mut self,
        ti: &'tcx rustc_hir::TraitItem,
    ) {
        intravisit::walk_trait_item(self, ti);
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
    }

    fn visit_stmt(
        &mut self,
        stmt: &'tcx rustc_hir::Stmt,
    ) {
        intravisit::walk_stmt(self, stmt);
    }
}
