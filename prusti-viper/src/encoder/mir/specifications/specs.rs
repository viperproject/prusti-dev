use log::{debug, trace};
use prusti_interface::{
    environment::Environment,
    specs::typed::{DefSpecificationMap, LoopSpecification, ProcedureSpecification, Refinable},
};
use rustc_hash::FxHashMap;
use rustc_hir::def_id::{DefId, LocalDefId};
use std::collections::HashMap;

/// Provides access to specifications, handling refinement if needed
pub(super) struct Specifications {
    spec_map: SpecMap,
}

impl Specifications {
    pub fn new(user_typed_specs: DefSpecificationMap) -> Self {
        Self {
            spec_map: SpecMap::new(user_typed_specs),
        }
    }

    pub fn get_loop_spec(&self, def_id: DefId) -> Option<&LoopSpecification> {
        trace!("Get loop specs of {:?}", def_id);
        self.spec_map.get_loop_spec(def_id)
    }

    pub fn get_proc_spec<'tcx>(
        &mut self,
        env: &Environment<'tcx>,
        def_id: DefId,
    ) -> Option<&ProcedureSpecification> {
        trace!("Get procedure specs of {:?}", def_id);

        // Refinement (if needed)
        if let Some(trait_def_id) = env.find_trait_method(def_id) {
            if !self.is_refined(def_id) {
                let refined = self.perform_proc_spec_refinement(def_id, trait_def_id);
                assert!(
                    refined.is_some(),
                    "Could not perform refinement for {:?}",
                    def_id
                );
                return refined;
            }
        }

        self.spec_map.get_proc_spec(def_id)
    }

    fn perform_proc_spec_refinement(
        &mut self,
        of_def_id: DefId,
        with_trait_def_id: DefId,
    ) -> Option<&ProcedureSpecification> {
        debug!(
            "Refining specs of {:?} with specs of {:?}",
            of_def_id, with_trait_def_id
        );

        let impl_spec = self
            .spec_map
            .get_proc_spec(of_def_id)
            .cloned()
            .unwrap_or_else(ProcedureSpecification::empty);

        let trait_spec = self.spec_map.get_proc_spec(with_trait_def_id);

        let refined = if let Some(trait_spec_set) = trait_spec {
            impl_spec.refine(trait_spec_set)
        } else {
            impl_spec
        };

        self.spec_map.insert_refined_spec(of_def_id, refined);
        self.spec_map.get_proc_spec(of_def_id)
    }

    fn is_refined(&self, def_id: DefId) -> bool {
        self.spec_map.is_refined(def_id)
    }

    pub fn compute_is_pure<'tcx>(&mut self, env: &Environment<'tcx>, def_id: DefId) -> bool {
        self.get_proc_spec(env, def_id)
            .and_then(|spec| spec.pure.get())
            .map(|(_, val)| *val)
            .unwrap_or(false)
    }

    pub fn compute_is_trusted<'tcx>(&mut self, env: &Environment<'tcx>, def_id: DefId) -> bool {
        self.get_proc_spec(env, def_id)
            .and_then(|spec| spec.trusted.get())
            .map(|(_, val)| *val)
            .unwrap_or(false)
    }

    pub fn get_user_typed_specs(&self) -> &DefSpecificationMap {
        &self.spec_map.user_typed_specs
    }

    pub fn get_extern_spec_map(&self) -> &HashMap<DefId, LocalDefId> {
        &self.get_user_typed_specs().extern_specs
    }
}

/// A wrapper around `DefSpecificationMap` to account for refined specifications
struct SpecMap {
    user_typed_specs: DefSpecificationMap,
    refined_specs: FxHashMap<DefId, ProcedureSpecification>,
}

impl SpecMap {
    fn new(user_typed_specs: DefSpecificationMap) -> Self {
        Self {
            user_typed_specs,
            refined_specs: FxHashMap::default(),
        }
    }

    fn get_proc_spec(&self, def_id: DefId) -> Option<&ProcedureSpecification> {
        self.refined_specs.get(&def_id).or_else(|| {
            self.user_typed_specs
                .get(&def_id)
                .and_then(|spec_set| spec_set.as_procedure())
        })
    }

    fn get_loop_spec(&self, def_id: DefId) -> Option<&LoopSpecification> {
        let spec = self.user_typed_specs.get(&def_id)?;
        spec.as_loop()
    }

    fn insert_refined_spec(&mut self, def_id: DefId, proc_spec: ProcedureSpecification) {
        self.refined_specs.insert(def_id, proc_spec);
    }

    fn is_refined(&self, def_id: DefId) -> bool {
        self.refined_specs.contains_key(&def_id)
    }
}
