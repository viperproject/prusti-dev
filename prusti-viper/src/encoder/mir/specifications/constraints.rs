use crate::encoder::mir::specifications::{interface::FunctionCallEncodingQuery, SpecQuery};
use log::{debug, trace};
use prusti_interface::{
    environment::Environment,
    specs::typed::{ProcedureSpecification, SpecConstraintKind, SpecGraph},
    PrustiError,
};
use prusti_rustc_interface::{
    errors::MultiSpan,
    hir::def_id::DefId,
    middle::{ty, ty::GenericArgsRef},
    span::Span,
};

pub(super) trait ConstraintResolver<'spec, 'env: 'spec, 'tcx: 'env> {
    fn resolve(
        &'spec self,
        env: &'env Environment<'tcx>,
        query: &SpecQuery<'tcx>,
    ) -> Result<&'spec ProcedureSpecification, PrustiError>;

    #[tracing::instrument(level = "debug", skip(self, env))]
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
                e.emit(&env.diagnostic);
                None
            }
        }
    }
}

impl<'spec, 'env: 'spec, 'tcx: 'env> ConstraintResolver<'spec, 'env, 'tcx>
    for SpecGraph<ProcedureSpecification>
{
    #[tracing::instrument(level = "debug", skip(self, env))]
    fn resolve(
        &'spec self,
        env: &'env Environment<'tcx>,
        query: &SpecQuery<'tcx>,
    ) -> Result<&'spec ProcedureSpecification, PrustiError> {
        if self.specs_with_constraints.is_empty() {
            trace!("Spec has no constraints, using base spec");
            return Ok(&self.base_spec);
        }

        let context = match query {
            SpecQuery::FetchSpan(_) => {
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
            // for type-conditional spec refinements on traits (behavioral subtyping rules will be checked
            // against the resolved spec).
            SpecQuery::FunctionDefEncoding(proc_def_id, substs)
            | SpecQuery::GetProcKind(proc_def_id, substs) => ConstraintSolvingContext {
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
                let span = env.query.get_def_span(context.proc_def_id);
                return Err(PrustiError::unsupported("Multiple different applicable specification obligations found, which is currently not supported in Prusti", MultiSpan::from_span(span)).add_note(
                    "This error is triggered because of a call to this function",
                    context.caller_proc_def_id.map(|caller| env.query.get_def_span(caller)),
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
    substs: GenericArgsRef<'tcx>,
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

mod trait_bounds {
    use super::*;
    use prusti_interface::{utils::has_trait_bounds_type_cond_spec, PrustiError};
    use rustc_hash::FxHashMap;

    #[tracing::instrument(
        name = "trait_bounds::resolve",
        level = "debug",
        skip(env, proc_spec),
        ret
    )]
    pub(super) fn resolve<'spec, 'env: 'spec, 'tcx: 'env>(
        env: &'env Environment<'tcx>,
        context: &ConstraintSolvingContext<'tcx>,
        proc_spec: &'spec ProcedureSpecification,
    ) -> bool {
        let param_env_constraint = extract_param_env(env, proc_spec);
        let param_env_constraint =
            perform_param_env_substitutions(env, context, param_env_constraint);

        // There is no caller when encoding a function.
        // We still resolve obligations to account for constrained specs on a trait
        // for which we encode its implementation. The corresponding encoding will
        // contain a behavioral subtyping check which will be performed on the
        // resolved spec.
        let param_env_lookup = if let Some(caller_def_id) = context.caller_proc_def_id {
            caller_def_id
        } else {
            context.proc_def_id
        };

        param_env_constraint
            .caller_bounds()
            .iter()
            .all(|predicate| {
                // Normalize any associated type projections.
                // This needs to be done because type-conditional spec refinements might contain "deeply nested"
                // associated types, e.g. `T: A<SomeAssocType = <Self as B>::OtherAssocType`
                // where `<Self as B>::OtherAssocType` can be normalized to some concrete type.
                let normalized_predicate =
                    env.query.resolve_assoc_types(predicate, param_env_lookup);

                env.query
                    .evaluate_predicate(normalized_predicate.as_predicate(), param_env_lookup)
            })
    }

    /// Substitutes the param environment
    #[tracing::instrument(level = "debug", skip(env), ret)]
    fn perform_param_env_substitutions<'env, 'tcx: 'env>(
        env: &'env Environment<'tcx>,
        context: &ConstraintSolvingContext<'tcx>,
        param_env: ty::ParamEnv<'tcx>,
    ) -> ty::ParamEnv<'tcx> {
        let maybe_trait_method = env
            .query
            .find_trait_method_substs(context.proc_def_id, context.substs);
        let param_env = if let Some((_, trait_substs)) = maybe_trait_method {
            trace!("Applying trait substs {:?}", trait_substs);
            ty::EarlyBinder::bind(param_env).instantiate(env.tcx(), trait_substs)
        } else {
            param_env
        };

        trace!(
            "Constraints after substituting trait substs: {:#?}",
            param_env
        );

        if context.substs.is_empty() {
            param_env
        } else {
            trace!("Applying call substs {:?}", context.substs);
            ty::EarlyBinder::bind(param_env).instantiate(env.tcx(), context.substs)
        }
    }

    fn extract_param_env<'a, 'tcx>(
        env: &'a Environment<'tcx>,
        spec: &ProcedureSpecification,
    ) -> ty::ParamEnv<'tcx> {
        let mut param_envs: FxHashMap<ty::ParamEnv<'tcx>, Vec<Span>> = FxHashMap::default();

        let pres: Vec<DefId> = spec
            .pres
            .expect_empty_or_inherent()
            .cloned()
            .unwrap_or_default();
        let posts: Vec<DefId> = spec
            .posts
            .expect_empty_or_inherent()
            .cloned()
            .unwrap_or_default();
        let purity = spec
            .purity
            .expect_empty_or_inherent()
            .cloned()
            .unwrap_or_default();
        for spec_id in pres.iter().chain(posts.iter()).chain(purity.iter()) {
            let param_env = env.tcx().param_env(spec_id);
            let spec_span = env.query.get_def_span(spec_id);
            let attrs = env.query.get_attributes(*spec_id);
            if has_trait_bounds_type_cond_spec(attrs) {
                param_envs.entry(param_env).or_default().push(spec_span);
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
                "Multiple type-conditional spec refinements with different bounds defined",
                MultiSpan::from_spans(spans),
            )
            .add_note("This is currently not supported.", None)
            .emit(&env.diagnostic);
        }

        param_envs.into_keys().next().unwrap()
    }
}
