use prusti_rustc_interface::{
    errors::MultiSpan,
    hir::{
        def_id::{DefId, LocalDefId},
        intravisit::{self, Visitor},
    },
    middle::hir::map::Map,
    span::Span,
};

use crate::{
    environment::{EnvDiagnostic, EnvName, EnvQuery, Environment},
    PrustiError,
};
use prusti_rustc_interface::{data_structures::fx::FxHashMap, middle::ty::GenericArgsRef};
use prusti_specs::ExternSpecKind;
use std::cmp::{Eq, PartialEq};

pub enum ExternSpecResolverError {
    /// Occurs when the user declares an extern spec in an impl block but the
    /// annotated method is a trait method.
    ///
    /// # Example:
    /// ```
    /// trait A { fn a(); }
    /// struct S;
    /// impl A for S { fn a() {...} }
    /// #[extern_spec]
    /// impl S {
    ///     // specs
    ///     fn a();
    /// }
    /// ```
    InvalidExternSpecForTraitImpl(DefId, Span),

    /// Occurs when the extern spec is invalid due to mismatched type params.
    InvalidGenerics(isize, DefId, Span),

    /// Occurs when a trait impl extern spec resolves to the trait method.
    ResolvedToDefault(DefId, Span),
}

#[derive(Debug, Eq, PartialEq, Hash, Clone)]
pub enum ExternSpecDeclaration {
    /// An external specification for inherent methods of impl blocks.
    Inherent(DefId),

    /// An external specification for a trait method (first `DefId`), resolved to its implementation
    /// method (second `DefId`).
    TraitImpl(DefId, DefId),

    /// An external specification for a trait method.
    Trait(DefId),

    /// An external specification for a free-standing method.
    Method(DefId),
}

impl ExternSpecDeclaration {
    /// Constructs [ExternSpecDeclaration] from a method call with the given substitutions.
    fn from_method_call<'tcx>(
        def_id: DefId,
        substs: GenericArgsRef<'tcx>,
        env_query: EnvQuery<'tcx>,
    ) -> Self {
        let is_impl_method = env_query.is_trait_method_impl(def_id);
        let is_trait_method = env_query.get_trait_of_item(def_id).is_some();
        let maybe_impl_def_id = env_query.find_impl_of_trait_method_call(def_id, substs);

        if is_trait_method && maybe_impl_def_id.is_none() {
            Self::Trait(def_id)
        } else if is_trait_method && maybe_impl_def_id.is_some() {
            Self::TraitImpl(def_id, maybe_impl_def_id.unwrap())
        } else if is_impl_method {
            Self::Inherent(def_id)
        } else {
            Self::Method(def_id)
        }
    }

    /// Returns the **target** [DefId] for which an external spec was declared.
    pub fn get_target_def_id(&self) -> DefId {
        match self {
            Self::Inherent(did)
            | Self::TraitImpl(_, did)
            | Self::Trait(did)
            | Self::Method(did) => *did,
        }
    }
}

/// This struct is used to build a mapping of external functions to their
/// Prusti specifications (see `extern_fn_map`).
pub struct ExternSpecResolver<'tcx> {
    env_name: EnvName<'tcx>,
    env_query: EnvQuery<'tcx>,

    /// Maps real functions to Prusti-generated fake functions with specifications.
    pub extern_fn_map: FxHashMap<ExternSpecDeclaration, DefId>,

    /// Duplicate specifications detected, keyed by the `DefId` of the function
    /// to be specified.
    spec_duplicates: FxHashMap<DefId, Vec<(DefId, Span)>>,

    /// Encountered errors while resolving external specs.
    errors: Vec<ExternSpecResolverError>,
}

impl<'tcx> ExternSpecResolver<'tcx> {
    pub fn new(env: &Environment<'tcx>) -> Self {
        Self {
            env_name: env.name,
            env_query: env.query,
            extern_fn_map: FxHashMap::default(),
            spec_duplicates: FxHashMap::default(),
            errors: vec![],
        }
    }

    /// Registers an external function specification. The arguments for this
    /// function are the same as arguments given to a function visit in an
    /// intravisit visitor.
    ///
    /// In case of duplicates, the function is added to `spec_duplicates`, and
    /// will later (in `check_duplicates`) be reported as an error. Otherwise,
    /// the function is added to `extern_fn_map`.
    pub fn add_extern_fn(
        &mut self,
        fn_kind: intravisit::FnKind<'tcx>,
        fn_decl: &'tcx prusti_rustc_interface::hir::FnDecl,
        body_id: prusti_rustc_interface::hir::BodyId,
        span: Span,
        local_id: LocalDefId,
        extern_spec_kind: ExternSpecKind,
    ) {
        let mut visitor = ExternSpecVisitor {
            env_query: self.env_query,
            spec_found: None,
        };
        visitor.visit_fn(fn_kind, fn_decl, body_id, span, local_id);
        let current_def_id = local_id.to_def_id();
        if let Some((target_def_id, substs, span)) = visitor.spec_found {
            let extern_spec_decl =
                ExternSpecDeclaration::from_method_call(target_def_id, substs, self.env_query);

            if matches!(extern_spec_kind, ExternSpecKind::Trait)
                && !matches!(extern_spec_decl, ExternSpecDeclaration::Trait(_))
            {
                unreachable!(
                    "External specification declared on a trait did not resolve to a trait method"
                );
            } else if matches!(extern_spec_kind, ExternSpecKind::TraitImpl)
                && !matches!(extern_spec_decl, ExternSpecDeclaration::TraitImpl(_, _))
            {
                unreachable!("External specification declared on a trait implementation did not resolve to a concrete type");
            }

            {
                // TODO: this resolution happens here but also in SpecCollector
                // maybe it can be done once only?
                let (resolved_def_id, _) =
                    self.env_query
                        .resolve_method_call(current_def_id, target_def_id, substs);
                if matches!(extern_spec_kind, ExternSpecKind::TraitImpl)
                    && resolved_def_id == target_def_id
                {
                    // should have resolved but did not: resolved to default
                    self.errors.push(ExternSpecResolverError::ResolvedToDefault(
                        target_def_id,
                        span,
                    ));
                } else {
                    // A call to the extern spec must be possible with the same exact
                    // type substitutions applied.
                    // TODO: there is more that we could check, e.g. that trait
                    // constraints are the same (otherwise specs might not make sense)
                    let (resolved_gens, current_gens) = (
                        self.env_query
                            .identity_substs(resolved_def_id)
                            .non_erasable_generics(self.env_query.tcx(), resolved_def_id)
                            .count(),
                        self.env_query
                            .identity_substs(current_def_id)
                            .non_erasable_generics(self.env_query.tcx(), current_def_id)
                            .count(),
                    );
                    if resolved_gens != current_gens {
                        let diff = resolved_gens as isize - current_gens as isize;
                        self.errors.push(ExternSpecResolverError::InvalidGenerics(
                            diff,
                            resolved_def_id,
                            span,
                        ));
                    }
                }
            }

            if self.extern_fn_map.contains_key(&extern_spec_decl) {
                self.register_duplicate_spec(target_def_id, current_def_id, span);
            } else {
                self.check_validity(extern_spec_kind, &extern_spec_decl, span);
                self.extern_fn_map
                    .insert(extern_spec_decl.clone(), current_def_id);
            }
        }
    }

    fn register_duplicate_spec(&mut self, decl_def_id: DefId, dup_spec_def_id: DefId, span: Span) {
        self.spec_duplicates
            .entry(decl_def_id)
            .or_default()
            .push((dup_spec_def_id, span));
    }

    /// Checks whether the encoded method call (call to `spec_for_def_id`) is valid.
    /// See [ExternSpecResolverError] for possible errors (including examples)
    fn check_validity(
        &mut self,
        extern_spec_kind: ExternSpecKind,
        declared_spec: &ExternSpecDeclaration,
        span: Span,
    ) {
        if matches!(extern_spec_kind, ExternSpecKind::InherentImpl) {
            if let ExternSpecDeclaration::TraitImpl(def_id, _) = declared_spec {
                self.errors
                    .push(ExternSpecResolverError::InvalidExternSpecForTraitImpl(
                        *def_id, span,
                    ));
            }
        }
        // Note: A check for matches!(extern_spec_kind, ExternSpecKind::TraitImpl) && !is_trait_method
        // is not needed because this does not typecheck (using UFCS call syntax in encoding).
    }

    /// Report errors encountered when resolving extern specs
    pub fn check_errors(&self, env_diagnostic: &EnvDiagnostic<'tcx>) {
        self.check_duplicates(env_diagnostic);

        for error in self.errors.iter() {
            match error {
                // TODO: branches look very similar
                ExternSpecResolverError::InvalidExternSpecForTraitImpl(def_id, span) => {
                    let function_name = self.env_name.get_item_name(*def_id);
                    let err_note = format!("Defined an external spec for trait method '{function_name}'. Use '#[extern_spec] impl TheTrait for TheStruct {{ ... }}' syntax instead.");
                    PrustiError::incorrect(
                        "Invalid external specification",
                        MultiSpan::from_span(*span),
                    )
                    .add_note(err_note, None)
                    .emit(env_diagnostic);
                }
                ExternSpecResolverError::InvalidGenerics(diff, def_id, span) => {
                    let function_name = self.env_name.get_item_name(*def_id);
                    let err_note = format!("Invalid type parameters for method '{function_name}'. The number of type parameters must match the target method; change by {diff} to get rid of this error.");
                    PrustiError::incorrect(
                        "Invalid external specification",
                        MultiSpan::from_span(*span),
                    )
                    .add_note(err_note, None)
                    .emit(env_diagnostic);
                }
                ExternSpecResolverError::ResolvedToDefault(def_id, span) => {
                    let function_name = self.env_name.get_item_name(*def_id);
                    let err_note = format!("Specified method ('{function_name}') resolved to the trait's implementation. Add specification to the trait instead.");
                    PrustiError::incorrect(
                        "Invalid external specification",
                        MultiSpan::from_span(*span),
                    )
                    .add_note(err_note, None)
                    .emit(env_diagnostic);
                }
            }
        }
    }

    /// Report errors for duplicate specifications found during specification
    /// collection.
    fn check_duplicates(&self, env_diagnostic: &EnvDiagnostic<'tcx>) {
        for (&def_id, specs) in self.spec_duplicates.iter() {
            let function_name = self.env_name.get_item_name(def_id);
            PrustiError::incorrect(
                format!("duplicate specification for {function_name}"),
                MultiSpan::from_spans(specs.iter().map(|s| s.1).collect()),
            )
            .emit(env_diagnostic);
        }
    }
}

/// A visitor that is called on external specification methods, as generated by
/// the external spec rewriter, looking specifically for the call to the
/// external function.
///
/// TODO: is the HIR representation stable enought that this could be
/// accomplished by a nested match rather than a full visitor?
struct ExternSpecVisitor<'tcx> {
    env_query: EnvQuery<'tcx>,
    spec_found: Option<(DefId, GenericArgsRef<'tcx>, Span)>,
}

impl<'tcx> Visitor<'tcx> for ExternSpecVisitor<'tcx> {
    type Map = Map<'tcx>;
    type NestedFilter = prusti_rustc_interface::middle::hir::nested_filter::All;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.env_query.hir()
    }

    fn visit_expr(&mut self, ex: &'tcx prusti_rustc_interface::hir::Expr<'tcx>) {
        if self.spec_found.is_some() {
            return;
        }
        if let prusti_rustc_interface::hir::ExprKind::Call(callee_expr, _arguments) = ex.kind {
            if let prusti_rustc_interface::hir::ExprKind::Path(ref qself) = callee_expr.kind {
                let tyck_res = self.env_query.tcx().typeck(callee_expr.hir_id.owner.def_id);
                let substs = tyck_res.node_args(callee_expr.hir_id);
                let res = tyck_res.qpath_res(qself, callee_expr.hir_id);
                if let prusti_rustc_interface::hir::def::Res::Def(_, def_id) = res {
                    self.spec_found = Some((def_id, substs, ex.span));
                    return;
                }
            }
        }
        intravisit::walk_expr(self, ex);
    }
}
