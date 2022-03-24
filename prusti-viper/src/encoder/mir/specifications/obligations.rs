use crate::{encoder::mir::specifications::SpecQuery, rustc_middle::ty::subst::Subst};
use log::{debug, trace};
use prusti_interface::{
    environment::Environment,
    specs::typed::{ProcedureSpecification, SpecificationObligationKind},
};
use rustc_hir::def_id::LocalDefId;
use rustc_middle::ty;
use rustc_span::{MultiSpan, Span};

/// Given a [ProcedureSpecification] with possible sub-contracts under obligation,
/// returns the actual [ProcedureSpecification] that should hold for the given [SpecQuery]
pub(super) struct ObligationResolver<'spec, 'env: 'spec, 'tcx: 'env> {
    pub env: &'env Environment<'tcx>,
    pub spec: &'spec ProcedureSpecification,
    pub query: SpecQuery<'tcx>,
}

impl<'spec, 'env: 'spec, 'tcx: 'env> ObligationResolver<'spec, 'env, 'tcx> {
    pub fn resolve(self) -> &'spec ProcedureSpecification {
        if self.spec.obligations.is_empty() {
            return self.spec;
        }

        if self.spec.obligations.len() != 1 {
            unreachable!("Multiple obligations are not yet supported");
        }

        let (obligation, spec_under_obligation) = self.spec.obligations.iter().next().unwrap();

        if self.obligation_fulfilled(obligation, spec_under_obligation) {
            spec_under_obligation
        } else {
            self.spec
        }
    }

    fn obligation_fulfilled(
        &self,
        obligation: &SpecificationObligationKind,
        item: &'spec ProcedureSpecification,
    ) -> bool {
        match obligation {
            SpecificationObligationKind::None => true,
            SpecificationObligationKind::ResolveGenericParamTraitBounds => {
                resolvers::trait_bounds::resolve(self.env, &self.query, item)
            }
        }
    }
}

mod resolvers {
    use super::*;

    pub mod trait_bounds {
        use super::*;
        use prusti_interface::{utils::has_trait_bounds_ghost_constraint, PrustiError};
        use rustc_hash::FxHashMap;

        pub fn resolve<'spec, 'env: 'spec, 'tcx: 'env>(
            env: &'env Environment<'tcx>,
            query: &SpecQuery<'tcx>,
            item: &'spec ProcedureSpecification,
        ) -> bool {
            debug!("Trait bound obligation resolving for {:?}", query);
            let param_env_obligation = extract_param_env(env, item);
            let param_env_called_method = env.tcx().param_env(query.def_id);

            let mut all_bounds_satisfied = true;

            if !query.substs.is_empty() {
                // We substitute the generics that appear in the param env of the obligation
                // with the substitutions. This should "erase" the generic params of the function
                // with the actual generic arguments used on callsite
                let param_env_substituted = param_env_obligation.subst(env.tcx(), query.substs);
                let trait_predicates = extract_trait_predicates(param_env_substituted);
                for trait_pred in trait_predicates {
                    let substituted_ty = trait_pred.self_ty();
                    let trait_def_id = trait_pred.trait_ref.def_id;
                    // TODO hansenj: Why param_env_called_method?
                    let does_implement_trait = env.type_implements_trait_with_trait_substs(
                        substituted_ty,
                        trait_def_id,
                        trait_pred.trait_ref.substs,
                        param_env_called_method,
                    );
                    trace!("\t{:?}: {}", trait_pred.trait_ref, does_implement_trait);
                    if !does_implement_trait {
                        all_bounds_satisfied = false;
                        break;
                    }
                }
            }

            if all_bounds_satisfied {
                trace!("\tObligation fulfilled");
                true
            } else {
                trace!("\tObligation not fulfilled");
                false
            }
        }

        fn extract_trait_predicates(param_env: ty::ParamEnv) -> Vec<ty::TraitPredicate> {
            let mut result = vec![];
            let caller_bounds = param_env.caller_bounds();
            for bound in caller_bounds {
                let predicate_kind = bound.kind().skip_binder();
                if let rustc_middle::ty::PredicateKind::Trait(trait_pred) = predicate_kind {
                    result.push(trait_pred);
                }
            }
            result
        }

        fn extract_param_env<'a, 'tcx>(
            env: &'a Environment<'tcx>,
            item: &ProcedureSpecification,
        ) -> ty::ParamEnv<'tcx> {
            let mut param_envs: FxHashMap<ty::ParamEnv<'tcx>, Vec<Span>> = FxHashMap::default();

            let pres: Vec<LocalDefId> = item
                .pres
                .expect_empty_or_inherent()
                .cloned()
                .unwrap_or_default();
            let posts: Vec<LocalDefId> = item
                .posts
                .expect_empty_or_inherent()
                .cloned()
                .unwrap_or_default();
            for spec_id in pres.iter().chain(posts.iter()) {
                let param_env = env.tcx().param_env(spec_id.to_def_id());
                let spec_span = env.tcx().def_span(spec_id.to_def_id());
                let attrs = env.tcx().get_attrs(spec_id.to_def_id());
                if has_trait_bounds_ghost_constraint(attrs) {
                    param_envs
                        .entry(param_env)
                        .or_insert(vec![])
                        .push(spec_span);
                }
            }

            assert_ne!(
                param_envs.len(),
                0,
                "Could not extract trait bound obligations from contract"
            );
            if param_envs.len() > 1 {
                let spans = param_envs.values().flatten().cloned().collect();
                PrustiError::unsupported(
                    "Multiple ghost constraints with different bounds defined",
                    MultiSpan::from_spans(spans),
                )
                .add_note("This is currently not supported.", None)
                .emit(env);
            }

            param_envs.into_iter().map(|(k, _)| k).next().unwrap()
        }
    }
}
