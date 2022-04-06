use rustc_ast::ast;
use rustc_hir::{intravisit};
use rustc_middle::hir::map::Map;
use rustc_middle::ty::TyCtxt;
use rustc_span::{Span, MultiSpan};

use rustc_hir::def_id::{DefId, LocalDefId};
use std::collections::HashMap;
use std::convert::TryInto;
use crate::environment::Environment;
use crate::PrustiError;
use crate::utils::{has_extern_spec_attr, read_prusti_attr, read_prusti_attrs, has_prusti_attr};
use log::debug;

pub mod external;
pub mod typed;
pub mod checker;

use typed::SpecIdRef;

use crate::specs::external::ExternSpecResolver;
use prusti_specs::specifications::common::SpecificationId;
use crate::specs::typed::{ProcedureSpecificationKind, SpecificationItem};

#[derive(Debug)]
struct ProcedureSpecRefs {
    spec_id_refs: Vec<SpecIdRef>,
    pure: bool,
    trusted: bool,
}

/// Specification collector, intended to be applied as a visitor over the crate
/// HIR. After the visit, [SpecCollector::build_def_specs] can be used to get back
/// a mapping of DefIds (which may not be local due to extern specs) to their
/// [typed::SpecificationSet], i.e. procedures, loop invariants, and structs.
pub struct SpecCollector<'a, 'tcx: 'a> {
    tcx: TyCtxt<'tcx>,
    env: &'a Environment<'tcx>,
    extern_resolver: ExternSpecResolver<'a, 'tcx>,

    /// Map from specification IDs to their typed expressions.
    spec_functions: HashMap<SpecificationId, LocalDefId>,

    /// Map from functions/loops and their specifications.
    procedure_specs: HashMap<LocalDefId, ProcedureSpecRefs>,
    loop_specs: Vec<LocalDefId>, // HashMap<LocalDefId, Vec<SpecificationId>>,
}

impl<'a, 'tcx> SpecCollector<'a, 'tcx> {
    pub fn new(env: &'a Environment<'tcx>) -> Self {
        let tcx = env.tcx();
        Self {
            tcx,
            env,
            extern_resolver: ExternSpecResolver::new(env),
            spec_functions: HashMap::new(),
            procedure_specs: HashMap::new(),
            loop_specs: vec![],
        }
    }

    pub fn build_def_specs(&self) -> typed::DefSpecificationMap {
        let mut def_spec = typed::DefSpecificationMap::new();
        self.determine_procedure_specs(&mut def_spec);
        self.determine_extern_specs(&mut def_spec);
        self.determine_loop_specs(&mut def_spec);
        self.determine_struct_specs(&mut def_spec);
        // TODO: remove spec functions (make sure none are duplicated or left over)

        def_spec
    }

    fn determine_procedure_specs(&self, def_spec: &mut typed::DefSpecificationMap) {
        // First: Build specs as they are typed by the user
        for (local_id, refs) in self.procedure_specs.iter() {
            let mut pres = vec![];
            let mut posts = vec![];
            let mut pledges = vec![];

            let mut kind = if refs.pure {
                ProcedureSpecificationKind::Pure
            } else {
                ProcedureSpecificationKind::Impure
            };

            for spec_id_ref in &refs.spec_id_refs {
                match spec_id_ref {
                    SpecIdRef::Precondition(spec_id) => {
                        pres.push(*self.spec_functions.get(spec_id).unwrap());
                    }
                    SpecIdRef::Postcondition(spec_id) => {
                        posts.push(*self.spec_functions.get(spec_id).unwrap());
                    }
                    SpecIdRef::Pledge { lhs, rhs } => {
                        pledges.push(typed::Pledge {
                            reference: None, // FIXME: Currently only `result` is supported.
                            lhs: lhs.as_ref().map(|spec_id| *self.spec_functions.get(spec_id).unwrap()),
                            rhs: *self.spec_functions.get(rhs).unwrap(),
                        });
                    }
                    SpecIdRef::Predicate(spec_id) => {
                        kind = ProcedureSpecificationKind::Predicate(*self.spec_functions.get(spec_id).unwrap());
                    }
                }
            }

            // Wrap everything into a specification item
            let pres = SpecificationItem::new(pres);
            let posts = SpecificationItem::new(posts);
            let pledges = SpecificationItem::new(pledges);
            let trusted = SpecificationItem::Inherent(refs.trusted);

            // We never create an empty kind. This would lead to refinement inheritance
            // if there is a trait involved.
            // Instead, we require the user to explicitly make annotations
            let kind = SpecificationItem::Inherent(kind);

            def_spec.specs.insert(
                *local_id,
                typed::SpecificationSet::Procedure(typed::ProcedureSpecification {
                    pres,
                    posts,
                    pledges,
                    kind,
                    trusted,
                })
            );
        }
    }

    fn determine_extern_specs(&self, def_spec: &mut typed::DefSpecificationMap) {
        self.extern_resolver.check_errors(self.env);
        for (extern_spec_decl, spec_id) in self.extern_resolver.extern_fn_map.iter() {
            let target_def_id = extern_spec_decl.get_target_def_id();

            if let Some(local_id) = target_def_id.as_local() {
                if def_spec.specs.contains_key(&local_id) {
                    PrustiError::incorrect(
                        format!("external specification provided for {}, which already has a specification",
                                self.env.get_item_name(target_def_id)),
                        MultiSpan::from_span(self.env.get_def_span(*spec_id)),
                    ).emit(self.env);
                }
            }

            if def_spec.specs.get(&spec_id.expect_local()).is_some() {
                def_spec.extern_specs.insert(target_def_id, spec_id.expect_local());
            }
        }
    }

    fn determine_loop_specs(&self, def_spec: &mut typed::DefSpecificationMap) {
        for local_id in self.loop_specs.iter() {
            def_spec.specs.insert(*local_id, typed::SpecificationSet::Loop(typed::LoopSpecification {
                invariant: *local_id,
            }));
        }
    }

    // TODO: struct specs
    fn determine_struct_specs(&self, _def_spec: &mut typed::DefSpecificationMap) {}
}

fn parse_spec_id(spec_id: String, def_id: DefId) -> SpecificationId {
    spec_id.try_into().unwrap_or_else(|_|
        panic!("cannot parse the spec_id attached to {:?}", def_id)
    )
}

fn get_procedure_spec_ids(def_id: DefId, attrs: &[ast::Attribute]) -> Option<ProcedureSpecRefs> {
    let mut spec_id_refs = vec![];

    spec_id_refs.extend(
        read_prusti_attrs("pre_spec_id_ref", attrs).into_iter().map(
            |raw_spec_id| SpecIdRef::Precondition(parse_spec_id(raw_spec_id, def_id))
        )
    );
    spec_id_refs.extend(
        read_prusti_attrs("post_spec_id_ref", attrs).into_iter().map(
            |raw_spec_id| SpecIdRef::Postcondition(parse_spec_id(raw_spec_id, def_id))
        )
    );
    spec_id_refs.extend(
        // TODO: pledges with LHS that is not "result" would need to carry the
        // LHS expression through typing
        read_prusti_attrs("pledge_spec_id_ref", attrs).into_iter().map(
            |raw_spec_id| SpecIdRef::Pledge { lhs: None, rhs: parse_spec_id(raw_spec_id, def_id) }
        )
    );
    match (
        read_prusti_attr("assert_pledge_spec_id_ref_lhs", attrs),
        read_prusti_attr("assert_pledge_spec_id_ref_rhs", attrs)
    ) {
        (Some(lhs_id), Some(rhs_id)) => {
            spec_id_refs.push(SpecIdRef::Pledge { lhs: Some(parse_spec_id(lhs_id, def_id)), rhs: parse_spec_id(rhs_id, def_id) });
        }
        (None, None) => {},
        _ => unreachable!(),
    }
    spec_id_refs.extend(
        read_prusti_attr("pred_spec_id_ref", attrs).map(
            |raw_spec_id| SpecIdRef::Predicate(parse_spec_id(raw_spec_id, def_id))
        )
    );
    debug!("Function {:?} has specification ids {:?}", def_id, spec_id_refs);

    let pure = has_prusti_attr(attrs, "pure");
    let trusted = has_prusti_attr(attrs, "trusted");

    if pure || trusted || !spec_id_refs.is_empty() {
        Some(ProcedureSpecRefs {
            spec_id_refs,
            pure,
            trusted,
        })
    } else {
        None
    }
}

impl<'a, 'tcx> intravisit::Visitor<'tcx> for SpecCollector<'a, 'tcx> {
    type Map = Map<'tcx>;
    type NestedFilter = rustc_middle::hir::nested_filter::All;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.tcx.hir()
    }

    fn visit_trait_item(
        &mut self,
        ti: &'tcx rustc_hir::TraitItem,
    ) {
        intravisit::walk_trait_item(self, ti);

        let id = ti.hir_id();
        let local_id = self.tcx.hir().local_def_id(id);
        let def_id = local_id.to_def_id();
        let attrs = self.tcx.get_attrs(ti.def_id.to_def_id());

        // Collect procedure specifications
        if let Some(procedure_spec_ref) = get_procedure_spec_ids(def_id, attrs) {
            self.procedure_specs.insert(local_id, procedure_spec_ref);
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
        intravisit::walk_fn(self, fn_kind, fn_decl, body_id, span, id);

        let local_id = self.tcx.hir().local_def_id(id);
        let def_id = local_id.to_def_id();
        let attrs = self.tcx.hir().attrs(id);

        // Collect spec functions
        if let Some(raw_spec_id) = read_prusti_attr("spec_id", attrs) {
            let spec_id: SpecificationId = parse_spec_id(raw_spec_id, def_id);
            self.spec_functions.insert(spec_id, local_id);

            // Collect loop specifications
            if has_prusti_attr(attrs, "loop_body_invariant_spec") {
                self.loop_specs.push(local_id);
            }
        } else {
            // Don't collect specs "for" spec items

            // Collect external function specifications
            if has_extern_spec_attr(attrs) {
                let attr = read_prusti_attr("extern_spec", attrs).unwrap_or_default();
                let kind = prusti_specs::ExternSpecKind::try_from(attr).unwrap();
                self.extern_resolver.add_extern_fn(fn_kind, fn_decl, body_id, span, id, kind);
            }

            // Collect procedure specifications
            if let Some(procedure_spec_ref) = get_procedure_spec_ids(def_id, attrs) {
                self.procedure_specs.insert(local_id, procedure_spec_ref);
            }
        }
    }

    fn visit_stmt(
        &mut self,
        stmt: &'tcx rustc_hir::Stmt,
    ) {
        intravisit::walk_stmt(self, stmt);

        // Collect closure specifications
        if let rustc_hir::StmtKind::Local(local) = stmt.kind {
            let attrs = self.tcx.hir().attrs(local.hir_id);
            if has_prusti_attr(attrs, "closure") {
                let init_expr = local.init
                    .expect("closure on Local without assignment");
                let local_id = self.tcx.hir().local_def_id(init_expr.hir_id);
                let def_id = local_id.to_def_id();
                // Collect procedure specifications
                if let Some(procedure_spec_ref) = get_procedure_spec_ids(def_id, attrs) {
                    self.procedure_specs.insert(local_id, procedure_spec_ref);
                }
            }
        }
    }
}
