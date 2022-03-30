use crate::{
    encoder::mir::specifications::{interface::SpecQueryCause, SpecQuery},
    rustc_middle::ty::subst::Subst,
};
use log::{debug, trace};
use prusti_interface::{
    environment::Environment,
    specs::typed::{ProcedureSpecification, SpecConstraintKind, SpecsWithConstraints},
    PrustiError,
};
use rustc_hir::def_id::LocalDefId;
use rustc_middle::ty;
use rustc_span::{MultiSpan, Span};

pub(crate) trait ConstraintResolver<'spec, 'env: 'spec, 'tcx: 'env> {
    fn resolve(
        &'spec self,
        env: &'env Environment<'tcx>,
        query: &SpecQuery<'tcx>,
    ) -> Result<&'spec ProcedureSpecification, PrustiError>;

    fn resolve_emit_err(
        &'spec self,
        env: &'env Environment<'tcx>,
        query: &SpecQuery<'tcx>,
    ) -> Option<&'spec ProcedureSpecification> {
        match self.resolve(env, query) {
            Ok(resolved_spec) => {
                debug!("Resolved spec: {resolved_spec:?}");
                Some(resolved_spec)
            }
            Err(e) => {
                e.emit(env);
                None
            }
        }
    }
}

impl<'spec, 'env: 'spec, 'tcx: 'env> ConstraintResolver<'spec, 'env, 'tcx>
    for SpecsWithConstraints<ProcedureSpecification>
{
    fn resolve(
        &'spec self,
        env: &'env Environment<'tcx>,
        query: &SpecQuery<'tcx>,
    ) -> Result<&'spec ProcedureSpecification, PrustiError> {
        debug!("Resolving spec constraints for {query:?}");
        if self.specs_with_constraints.is_empty() {
            trace!("Spec has no constraints, using base spec");
            return Ok(&self.base_spec);
        }

        if let SpecQueryCause::PureOrTrustedCheck = query.cause {
            trace!(
                "No need to resolve obligations for checking whether function is pure or trusted"
            );
            return Ok(&self.base_spec);
        }

        let mut applicable_specs =
            self.specs_with_constraints
                .iter()
                .filter(|(constraint_kind, spec)| {
                    constraint_fulfilled(env, query, constraint_kind, spec)
                });

        if let Some((constraint_kind, spec_with_constraints)) = applicable_specs.next() {
            if applicable_specs.next().is_some() {
                let span = env.tcx().def_span(query.called_def_id);
                return Err(PrustiError::unsupported("Multiple different applicable specification obligations found, which is currently not supported in Prusti", MultiSpan::from_span(span)).add_note(
                    "This error is triggered because of a call to this function",
                    query.caller_def_id.map(|caller| env.tcx().def_span(caller)),
                ));
            }

            if let Some(false) = self.base_spec.trusted.extract_inherit() {
                let span = env.tcx().def_span(query.called_def_id);
                return Err(PrustiError::unsupported(
                    "Ghost constraints can only be used on trusted functions",
                    MultiSpan::from(span),
                )
                .add_note(
                    "This error is triggered because of a call to this function",
                    query.caller_def_id.map(|caller| env.tcx().def_span(caller)),
                ));
            }

            trace!("Resolved to constrained spec with constraint {constraint_kind:?}");
            Ok(spec_with_constraints)
        } else {
            trace!("No constrained spec applicable, using base spec");
            Ok(&self.base_spec)
        }
    }
}

fn constraint_fulfilled<'spec, 'env: 'spec, 'tcx: 'env>(
    env: &'env Environment<'tcx>,
    query: &SpecQuery<'tcx>,
    obligation: &SpecConstraintKind,
    proc_spec: &'spec ProcedureSpecification,
) -> bool {
    match obligation {
        SpecConstraintKind::ResolveGenericParamTraitBounds => {
            resolvers::trait_bounds::resolve(env, query, proc_spec)
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
            proc_spec: &'spec ProcedureSpecification,
        ) -> bool {
            assert!(
                matches!(query.cause, SpecQueryCause::FunctionCallEncoding)
                    || matches!(query.cause, SpecQueryCause::FunctionDefEncoding)
            );
            debug!("Trait bound constraint resolving for {:?}", query);

            let param_env_constraint = extract_param_env(env, proc_spec);
            let param_env_constraint =
                perform_param_env_substitutions(env, query, param_env_constraint);

            let param_env_lookup = if let Some(caller_def_id) = query.caller_def_id {
                env.tcx().param_env(caller_def_id)
            } else {
                // TODO hansenj: Is this correct?
                env.tcx().param_env(query.called_def_id)
            };

            let trait_predicates = extract_trait_predicates(param_env_constraint);
            let all_bounds_satisfied = trait_predicates.iter().all(|trait_pred| {
                let substituted_ty = trait_pred.self_ty();
                let trait_def_id = trait_pred.trait_ref.def_id;
                env.type_implements_trait_with_trait_substs(
                    substituted_ty,
                    trait_def_id,
                    trait_pred.trait_ref.substs,
                    param_env_lookup,
                )
            });

            if all_bounds_satisfied {
                trace!("Constraint fulfilled");
                true
            } else {
                trace!("Constraint not fulfilled");
                false
            }
        }

        /// Substitutes the param
        fn perform_param_env_substitutions<'env, 'tcx: 'env>(
            env: &'env Environment<'tcx>,
            query: &SpecQuery<'tcx>,
            param_env: ty::ParamEnv<'tcx>,
        ) -> ty::ParamEnv<'tcx> {
            trace!("Unsubstituted constraints: {:#?}", param_env);

            let maybe_trait_method =
                env.find_trait_method_substs(query.called_def_id, query.call_substs);
            let param_env = if let Some((_, trait_substs)) = maybe_trait_method {
                param_env.subst(env.tcx(), trait_substs)
            } else {
                param_env
            };

            trace!(
                "Constraints after substituting trait substs: {:#?}",
                param_env
            );

            let param_env = if query.call_substs.is_empty() {
                param_env
            } else {
                param_env.subst(env.tcx(), query.call_substs)
            };

            trace!(
                "Constraints after substituting call substs: {:#?}",
                param_env
            );

            param_env
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
            spec: &ProcedureSpecification,
        ) -> ty::ParamEnv<'tcx> {
            let mut param_envs: FxHashMap<ty::ParamEnv<'tcx>, Vec<Span>> = FxHashMap::default();

            let pres: Vec<LocalDefId> = spec
                .pres
                .expect_empty_or_inherent()
                .cloned()
                .unwrap_or_default();
            let posts: Vec<LocalDefId> = spec
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
