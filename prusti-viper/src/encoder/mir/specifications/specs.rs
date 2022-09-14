use crate::encoder::{
    errors::MultiSpan,
    mir::specifications::{
        constraints::ConstraintResolver,
        interface::{FunctionCallEncodingQuery, SpecQuery},
    },
};
use log::debug;
use prusti_interface::{
    environment::Environment,
    specs::typed::{
        DefSpecificationMap, GhostBegin, GhostEnd, LoopSpecification, ProcedureSpecification,
        ProcedureSpecificationKind, ProcedureSpecificationKindError, PrustiAssertion,
        PrustiAssumption, PrustiRefutation, Refinable, SpecificationExpression, SpecificationItem,
        SpecificationRegionBegin, SpecificationRegionEnd, TypeSpecification,
    },
    PrustiError,
};
use prusti_rustc_interface::hir::def_id::DefId;
use rustc_hash::FxHashMap;

/// Defines the context for which we perform refinement.
/// It can be thought of as the variants of [SpecQuery] for which we can perform refinement.
#[derive(Debug)]
struct RefinementContext<'qry, 'tcx> {
    impl_query: &'qry SpecQuery<'tcx>,
    trait_query: SpecQuery<'tcx>,
}

impl<'qry, 'tcx> RefinementContext<'qry, 'tcx> {
    /// Tries to create a refinement context.
    /// Returns None if refinement is not needed
    fn try_from(env: &Environment<'tcx>, query: &'qry SpecQuery<'tcx>) -> Option<Self> {
        match query {
            SpecQuery::FunctionCallEncoding(FunctionCallEncodingQuery {
                called_def_id: def_id,
                call_substs: substs,
                ..
            })
            | SpecQuery::FunctionDefEncoding(def_id, substs)
            | SpecQuery::GetProcKind(def_id, substs) => {
                let (trait_def_id, trait_substs) =
                    env.query.find_trait_method_substs(*def_id, substs)?;
                let trait_query = query.adapt_to(trait_def_id, trait_substs);
                Some(RefinementContext {
                    impl_query: query,
                    trait_query,
                })
            }
            // All other queries do not need refinement
            _ => None,
        }
    }
}

/// Provides access to specifications, handling refinement if needed
pub(super) struct Specifications<'tcx> {
    user_typed_specs: DefSpecificationMap,

    /// A refinement can be different based on the query.
    /// The query can resolve to different [ProcedureSpecification]s due to type-conditional spec refinements.
    /// Since Prusti does currently not support refinements of type-conditional spec refinements, we
    /// store different refined versions for different queries.
    refined_specs: FxHashMap<SpecQuery<'tcx>, ProcedureSpecification>,
}

impl<'tcx> Specifications<'tcx> {
    pub(super) fn new(user_typed_specs: DefSpecificationMap) -> Self {
        Self {
            user_typed_specs,
            refined_specs: FxHashMap::default(),
        }
    }

    #[tracing::instrument(level = "trace", skip(self))]
    pub(super) fn get_loop_spec(&self, def_id: &DefId) -> Option<&LoopSpecification> {
        self.user_typed_specs.get_loop_spec(def_id)
    }

    #[tracing::instrument(level = "trace", skip(self))]
    pub(super) fn get_type_spec(&self, def_id: &DefId) -> Option<&TypeSpecification> {
        self.user_typed_specs.get_type_spec(def_id)
    }

    #[tracing::instrument(level = "trace", skip(self))]
    pub(super) fn get_assertion(&self, def_id: &DefId) -> Option<&PrustiAssertion> {
        self.user_typed_specs.get_assertion(def_id)
    }

    #[tracing::instrument(level = "trace", skip(self))]
    pub(super) fn get_assumption(&self, def_id: &DefId) -> Option<&PrustiAssumption> {
        self.user_typed_specs.get_assumption(def_id)
    }

    #[tracing::instrument(level = "trace", skip(self))]
    pub(super) fn get_refutation(&self, def_id: &DefId) -> Option<&PrustiRefutation> {
        self.user_typed_specs.get_refutation(def_id)
    }

    #[tracing::instrument(level = "trace", skip(self))]
    pub(super) fn get_ghost_begin(&self, def_id: &DefId) -> Option<&GhostBegin> {
        self.user_typed_specs.get_ghost_begin(def_id)
    }

    #[tracing::instrument(level = "trace", skip(self))]
    pub(super) fn get_ghost_end(&self, def_id: &DefId) -> Option<&GhostEnd> {
        self.user_typed_specs.get_ghost_end(def_id)
    }

    #[tracing::instrument(level = "trace", skip(self))]
    pub(super) fn get_specification_region_begin(
        &self,
        def_id: &DefId,
    ) -> Option<&SpecificationRegionBegin> {
        self.user_typed_specs.get_specification_region_begin(def_id)
    }

    #[tracing::instrument(level = "trace", skip(self))]
    pub(super) fn get_specification_region_end(
        &self,
        def_id: &DefId,
    ) -> Option<&SpecificationRegionEnd> {
        self.user_typed_specs.get_specification_region_end(def_id)
    }

    #[tracing::instrument(level = "trace", skip(self))]
    pub(super) fn get_specification_expression(
        &self,
        def_id: &DefId,
    ) -> Option<&SpecificationExpression> {
        self.user_typed_specs.get_specification_expression(def_id)
    }

    #[tracing::instrument(level = "trace", skip(self, env))]
    pub(super) fn get_and_refine_proc_spec<'a, 'env: 'a>(
        &'a mut self,
        env: &'env Environment<'tcx>,
        query: SpecQuery<'tcx>,
    ) -> Option<&'a ProcedureSpecification> {
        if self.is_refined(&query) {
            return self.get_proc_spec(env, &query);
        }

        match RefinementContext::try_from(env, &query) {
            Some(context) => {
                let refined = self.perform_proc_spec_refinement(
                    env,
                    context.impl_query,
                    &context.trait_query,
                );
                assert!(
                    refined.is_some(),
                    "Could not perform refinement for {query:?}"
                );
                refined
            }
            _ => self.get_proc_spec(env, &query),
        }
    }

    #[tracing::instrument(level = "debug", skip(self, env))]
    fn perform_proc_spec_refinement<'a, 'env: 'a>(
        &'a mut self,
        env: &'env Environment<'tcx>,
        impl_query: &SpecQuery<'tcx>,
        trait_query: &SpecQuery<'tcx>,
    ) -> Option<&'a ProcedureSpecification> {
        let impl_spec = self
            .get_proc_spec(env, impl_query)
            .cloned()
            .unwrap_or_else(|| ProcedureSpecification::empty(impl_query.referred_def_id()));

        let trait_spec = self
            .get_proc_spec(env, trait_query)
            .cloned()
            .unwrap_or_else(|| ProcedureSpecification::empty(trait_query.referred_def_id()));
        let refined = impl_spec.refine(&trait_spec);

        self.validate_refined_kind(
            env,
            impl_query.referred_def_id(),
            trait_query.referred_def_id(),
            &refined.kind,
        );

        debug!("Refined: {:?}", refined);
        self.refined_specs.insert(*impl_query, refined);
        self.get_proc_spec(env, impl_query)
    }

    fn get_proc_spec<'a, 'env: 'a>(
        &'a self,
        env: &'env Environment<'tcx>,
        query: &SpecQuery<'tcx>,
    ) -> Option<&'a ProcedureSpecification> {
        self.refined_specs.get(query).or_else(|| {
            self.user_typed_specs
                .get_proc_spec(&query.referred_def_id())
                .and_then(|spec| spec.resolve_emit_err(env, query))
        })
    }

    fn is_refined(&self, query: &SpecQuery<'tcx>) -> bool {
        self.refined_specs.contains_key(query)
    }

    /// Validates refinement and reports proper errors
    fn validate_refined_kind(
        &self,
        env: &Environment<'tcx>,
        impl_proc_def_id: DefId,
        trait_proc_def_id: DefId,
        kind: &SpecificationItem<ProcedureSpecificationKind>,
    ) {
        match kind.validate() {
            Ok(()) => (),
            Err(ProcedureSpecificationKindError::InvalidSpecKindRefinement(
                base_kind,
                refined_kind,
            )) => {
                let impl_method_span = env.query.get_def_span(impl_proc_def_id);

                let trait_def_id = env.query.get_trait_of_item(trait_proc_def_id).unwrap();
                let trait_span = env.query.get_def_span(trait_def_id);
                let trait_name = env.name.get_absolute_item_name(trait_def_id);
                let trait_method_name = env.name.get_absolute_item_name(trait_proc_def_id);
                let impl_method_name = env.name.get_absolute_item_name(impl_proc_def_id);

                PrustiError::incorrect(
                    format!("Invalid specification kind for procedure '{impl_method_name}'"),
                    MultiSpan::from_span(impl_method_span),
                )
                .add_note("Procedures can be predicates, pure or impure", None)
                .add_note(
                    format!("This procedure is of kind '{refined_kind}'").as_str(),
                    None,
                )
                .add_note(
                    format!("This procedure refines a function declared on '{trait_name}'")
                        .as_str(),
                    Some(trait_span),
                )
                .add_note(
                    format!("However, '{trait_method_name}' is of kind '{base_kind}'").as_str(),
                    None,
                )
                .add_note(
                    format!(
                        "Try to convert '{impl_method_name}' into a procedure of kind '{base_kind}'"
                    ),
                    Some(impl_method_span),
                )
                .emit(&env.diagnostic);
            }
        }
    }
}
