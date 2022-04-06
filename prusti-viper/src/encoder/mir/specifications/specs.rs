use crate::encoder::errors::MultiSpan;
use log::{debug, trace};
use prusti_interface::{
    environment::Environment,
    specs::typed::{
        DefSpecificationMap, LoopSpecification, ProcedureSpecification, ProcedureSpecificationKind,
        ProcedureSpecificationKindError, Refinable, SpecificationItem,
    },
    PrustiError,
};
use rustc_hash::FxHashMap;
use rustc_hir::def_id::{DefId, LocalDefId};
use std::collections::HashMap;

/// Provides access to specifications, handling refinement if needed
pub(super) struct Specifications {
    user_typed_specs: DefSpecificationMap,
    refined_specs: FxHashMap<DefId, ProcedureSpecification>,
}

impl Specifications {
    pub(super) fn new(user_typed_specs: DefSpecificationMap) -> Self {
        Self {
            user_typed_specs,
            refined_specs: FxHashMap::default(),
        }
    }

    pub(super) fn get_user_typed_specs(&self) -> &DefSpecificationMap {
        &self.user_typed_specs
    }

    pub(super) fn get_extern_spec_map(&self) -> &HashMap<DefId, LocalDefId> {
        &self.get_user_typed_specs().extern_specs
    }

    pub(super) fn get_loop_spec(&self, def_id: DefId) -> Option<&LoopSpecification> {
        trace!("Get loop specs of {:?}", def_id);
        let spec = self.get_user_typed_specs().get(&def_id)?;
        spec.as_loop()
    }

    pub(super) fn get_and_refine_proc_spec<'tcx>(
        &mut self,
        env: &Environment<'tcx>,
        def_id: DefId,
    ) -> Option<&ProcedureSpecification> {
        trace!("Get procedure specs of {:?}", def_id);

        // Refinement (if needed)
        if !self.is_refined(def_id) {
            if let Some(trait_def_id) = env.find_trait_method(def_id) {
                let refined = self.perform_proc_spec_refinement(def_id, trait_def_id, env);
                assert!(
                    refined.is_some(),
                    "Could not perform refinement for {:?}",
                    def_id
                );
                return refined;
            }
        }

        self.get_proc_spec(def_id)
    }

    fn perform_proc_spec_refinement<'tcx>(
        &mut self,
        of_def_id: DefId,
        with_trait_def_id: DefId,
        env: &Environment<'tcx>,
    ) -> Option<&ProcedureSpecification> {
        debug!(
            "Refining specs of {:?} with specs of {:?}",
            of_def_id, with_trait_def_id
        );

        let impl_spec = self
            .get_proc_spec(of_def_id)
            .cloned()
            .unwrap_or_else(ProcedureSpecification::empty);

        let trait_spec = self.get_proc_spec(with_trait_def_id);

        let refined = if let Some(trait_spec_set) = trait_spec {
            impl_spec.refine(trait_spec_set)
        } else {
            impl_spec
        };

        self.validate_refined_kind(of_def_id, with_trait_def_id, &refined.kind, env);

        debug!("Refined: {:?}", refined);
        self.refined_specs.insert(of_def_id, refined);
        self.get_proc_spec(of_def_id)
    }

    fn get_proc_spec(&self, def_id: DefId) -> Option<&ProcedureSpecification> {
        self.refined_specs.get(&def_id).or_else(|| {
            self.user_typed_specs
                .get(&def_id)
                .and_then(|spec_set| spec_set.as_procedure())
        })
    }

    fn is_refined(&self, def_id: DefId) -> bool {
        self.refined_specs.contains_key(&def_id)
    }

    /// Validates refinement and reports proper errors
    fn validate_refined_kind<'tcx>(
        &self,
        impl_proc_def_id: DefId,
        trait_proc_def_id: DefId,
        kind: &SpecificationItem<ProcedureSpecificationKind>,
        env: &Environment<'tcx>,
    ) {
        match kind.validate() {
            Ok(()) => (),
            Err(ProcedureSpecificationKindError::InvalidSpecKindRefinement(
                base_kind,
                refined_kind,
            )) => {
                let impl_method_span = env.tcx().def_span(impl_proc_def_id);

                let trait_def_id = env.tcx().trait_of_item(trait_proc_def_id).unwrap();
                let trait_span = env.tcx().def_span(trait_def_id);
                let trait_name = env.tcx().def_path_str(trait_def_id);
                let trait_method_name = env.tcx().def_path_str(trait_proc_def_id);
                let impl_method_name = env.tcx().def_path_str(impl_proc_def_id);

                PrustiError::incorrect(
                    format!(
                        "Invalid specification kind for procedure '{}'",
                        impl_method_name
                    ),
                    MultiSpan::from_span(impl_method_span),
                )
                .add_note("Procedures can be predicates, pure or impure", None)
                .add_note(
                    format!("This procedure is of kind '{}'", refined_kind).as_str(),
                    None,
                )
                .add_note(
                    format!(
                        "This procedure refines a function declared on '{}'",
                        trait_name
                    )
                    .as_str(),
                    Some(trait_span),
                )
                .add_note(
                    format!(
                        "However, '{}' is of kind '{}'",
                        trait_method_name, base_kind
                    )
                    .as_str(),
                    None,
                )
                .add_note(
                    format!(
                        "Try to convert '{}' into a procedure of kind '{}'",
                        impl_method_name, base_kind
                    ),
                    Some(impl_method_span),
                )
                .emit(env);
            }
        }
    }
}
