use crate::encoder::mir::specifications::{interface::FunctionCallEncodingQuery, SpecQuery};
use log::{debug, trace};
use prusti_interface::{
    environment::Environment,
    specs::typed::{ProcedureSpecification, SpecConstraintKind, SpecGraph},
    PrustiError,
};
use prusti_rustc_interface::{
    errors::MultiSpan,
    hir::def_id::{DefId, LocalDefId},
    middle::{
        ty,
        ty::subst::{Subst, SubstsRef},
    },
    span::Span,
};

pub(super) trait ConstraintResolver<'spec, 'env: 'spec, 'tcx: 'env> {
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
    for SpecGraph<ProcedureSpecification>
{
    fn resolve(
        &'spec self,
        env: &'env Environment<'tcx>,
        query: &SpecQuery<'tcx>,
    ) -> Result<&'spec ProcedureSpecification, PrustiError> {
        debug!("Resolving spec constraints for {query:?}");

        if !prusti_common::config::enable_ghost_constraints() {
            trace!("Ghost constraints are disabled, using base spec");
            return Ok(&self.base_spec);
        }

        if self.specs_with_constraints.is_empty() {
            trace!("Spec has no constraints, using base spec");
            return Ok(&self.base_spec);
        }

        let context = match query {
            SpecQuery::GetProcKind(_, _) | SpecQuery::FetchSpan(_) => {
                trace!("No need to resolve obligations for cause {:?}", query);
                return Ok(&self.base_spec);
            }
            SpecQuery::FunctionCallEncoding(FunctionCallEncodingQuery {
                called_def_id,
                caller_def_id,
                call_substs,
            }) => ConstraintSolvingContext {
                proc_def_id: *called_def_id,
                caller_proc_def_id: Some(*caller_def_id),
                substs: call_substs,
            },
            // Obligations are resolved for function definition encodings to account
            // for ghost constraints on traits (behavioral subtyping rules will be checked
            // against the resolved spec).
            SpecQuery::FunctionDefEncoding(proc_def_id, substs) => ConstraintSolvingContext {
                proc_def_id: *proc_def_id,
                substs,
                caller_proc_def_id: None,
            },
        };

        let mut applicable_specs =
            self.specs_with_constraints
                .iter()
                .filter(|(constraint_kind, spec)| {
                    constraint_fulfilled(env, &context, constraint_kind, spec)
                });

        if let Some((constraint_kind, spec_with_constraints)) = applicable_specs.next() {
            if applicable_specs.next().is_some() {
                let span = env.tcx().def_span(context.proc_def_id);
                return Err(PrustiError::unsupported("Multiple different applicable specification obligations found, which is currently not supported in Prusti", MultiSpan::from_span(span)).add_note(
                    "This error is triggered because of a call to this function",
                    context.caller_proc_def_id.map(|caller| env.tcx().def_span(caller)),
                ));
            }

            // Sanity check: The base spec and spec with constraints is trusted
            // This should be ensured when collecting the specs
            assert_eq!(Some(true), self.base_spec.trusted.extract_inherit());
            assert_eq!(Some(true), spec_with_constraints.trusted.extract_inherit());

            trace!("Resolved to constrained spec with constraint {constraint_kind:?}");
            Ok(spec_with_constraints)
        } else {
            trace!("No constrained spec applicable, using base spec");
            Ok(&self.base_spec)
        }
    }
}

#[derive(Debug)]
struct ConstraintSolvingContext<'tcx> {
    proc_def_id: DefId,
    substs: SubstsRef<'tcx>,
    caller_proc_def_id: Option<DefId>,
}

fn constraint_fulfilled<'spec, 'env: 'spec, 'tcx: 'env>(
    env: &'env Environment<'tcx>,
    context: &ConstraintSolvingContext<'tcx>,
    obligation: &SpecConstraintKind,
    proc_spec: &'spec ProcedureSpecification,
) -> bool {
    match obligation {
        SpecConstraintKind::ResolveGenericParamTraitBounds => {
            trait_bounds::resolve(env, context, proc_spec)
        }
    }
}

pub mod trait_bounds {
    use super::*;
    use prusti_interface::{utils::has_trait_bounds_ghost_constraint, PrustiError};
    use rustc_hash::FxHashMap;

    pub(super) fn resolve<'spec, 'env: 'spec, 'tcx: 'env>(
        env: &'env Environment<'tcx>,
        context: &ConstraintSolvingContext<'tcx>,
        proc_spec: &'spec ProcedureSpecification,
    ) -> bool {
        debug!("Trait bound constraint resolving for {:?}", context);

        let param_env_constraint = extract_param_env(env, proc_spec);
        let param_env_constraint =
            perform_param_env_substitutions(env, context, param_env_constraint);

        // There is no caller when encoding a function.
        // We still resolve obligations to account for constrained specs on a trait
        // for which we encode its implementation. The corresponding encoding will
        // contain a behavioral subtyping check which will be performed on the
        // resolved spec.
        let param_env_lookup = if let Some(caller_def_id) = context.caller_proc_def_id {
            env.tcx().param_env(caller_def_id)
        } else {
            env.tcx().param_env(context.proc_def_id)
        };

        let all_bounds_satisfied = param_env_constraint
            .caller_bounds()
            .iter()
            .all(|predicate| {
                // Normalize any associated type projections.
                // This needs to be done because ghost constraints might contain "deeply nested"
                // associated types, e.g. `T: A<SomeAssocType = <Self as B>::OtherAssocType`
                // where `<Self as B>::OtherAssocType` can be normalized to some concrete type.
                let normalized_predicate = env.resolve_assoc_types(predicate, param_env_lookup);

                env.evaluate_predicate(normalized_predicate, param_env_lookup)
            });

        trace!("Constraint fulfilled: {all_bounds_satisfied}");
        all_bounds_satisfied
    }

    /// Substitutes the param environment
    fn perform_param_env_substitutions<'env, 'tcx: 'env>(
        env: &'env Environment<'tcx>,
        context: &ConstraintSolvingContext<'tcx>,
        param_env: ty::ParamEnv<'tcx>,
    ) -> ty::ParamEnv<'tcx> {
        trace!("Unsubstituted constraints: {:#?}", param_env);

        let maybe_trait_method = env.find_trait_method_substs(context.proc_def_id, context.substs);
        let param_env = if let Some((_, trait_substs)) = maybe_trait_method {
            trace!("Applying trait substs {:?}", trait_substs);
            ty::EarlyBinder(param_env).subst(env.tcx(), trait_substs)
        } else {
            param_env
        };

        trace!(
            "Constraints after substituting trait substs: {:#?}",
            param_env
        );

        let param_env = if context.substs.is_empty() {
            param_env
        } else {
            trace!("Applying call substs {:?}", context.substs);
            ty::EarlyBinder(param_env).subst(env.tcx(), context.substs)
        };

        trace!(
            "Constraints after substituting call substs: {:#?}",
            param_env
        );

        param_env
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
            let attrs = env.get_local_attributes(*spec_id);
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
