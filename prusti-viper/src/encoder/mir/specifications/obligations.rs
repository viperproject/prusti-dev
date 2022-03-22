use crate::{encoder::mir::specifications::SpecQuery, rustc_middle::ty::subst::Subst};
use log::{debug, trace};
use prusti_interface::{
    environment::Environment,
    specs::typed::{ProcedureSpecification, SpecificationObligationKind, WithPossibleObligation},
};
use rustc_middle::ty;
use rustc_span::{MultiSpan, Span};

pub(super) struct ObligationResolver<'spec, 'env: 'spec, 'tcx: 'env> {
    pub env: &'env Environment<'tcx>,
    pub with_obligation: &'spec WithPossibleObligation<ProcedureSpecification>,
    pub query: SpecQuery<'tcx>,
}

impl<'spec, 'env: 'spec, 'tcx: 'env> ObligationResolver<'spec, 'env, 'tcx> {
    pub fn resolve(self) -> &'spec ProcedureSpecification {
        match self.with_obligation {
            WithPossibleObligation::WithoutObligation(item) => item,
            WithPossibleObligation::WithObligation(
                obligation,
                spec_under_obligation,
                base_spec,
            ) => {
                if let Some(item) = self.resolve_with_obligation(obligation, spec_under_obligation)
                {
                    item
                } else {
                    base_spec
                }
            }
        }
    }

    fn resolve_with_obligation(
        &self,
        obligation: &SpecificationObligationKind,
        item: &'env ProcedureSpecification,
    ) -> Option<&'spec ProcedureSpecification> {
        match obligation {
            SpecificationObligationKind::None => Some(item),
            SpecificationObligationKind::ResolveGenericParamTraitBounds => {
                resolvers::trait_bounds::resolve(self.env, &self.query, item)
            }
            SpecificationObligationKind::Combined(_, _) => None,
        }
    }
}

mod resolvers {
    use super::*;

    pub mod trait_bounds {
        use super::*;
        use prusti_interface::PrustiError;
        use rustc_hash::FxHashMap;

        pub fn resolve<'spec, 'env: 'spec, 'tcx: 'env>(
            env: &'env Environment<'tcx>,
            query: &SpecQuery<'tcx>,
            item: &'spec ProcedureSpecification,
        ) -> Option<&'spec ProcedureSpecification> {
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
                Some(item)
            } else {
                trace!("\tObligation not fulfilled");
                None
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

            // TODO hansenj: Not sure about this
            let pres_iter = item.pres.extract_with_selective_replacement_iter();
            let posts_iter = item.posts.extract_with_selective_replacement_iter();
            let specs_iter = pres_iter.chain(posts_iter);

            for spec_id in specs_iter {
                let param_env = env.tcx().param_env(spec_id.to_def_id());
                let spec_span = env.tcx().def_span(spec_id.to_def_id());
                param_envs
                    .entry(param_env)
                    .or_insert(vec![])
                    .push(spec_span);
            }

            // TODO hansenj: Add case param_envs.len() == 0
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
