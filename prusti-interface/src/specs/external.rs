use rustc_hir::{
    def_id::DefId,
    intravisit::{self, Visitor},
};
use rustc_middle::{hir::map::Map, ty::TyCtxt};
use rustc_span::{MultiSpan, Span};

use crate::{environment::Environment, PrustiError};
use std::collections::HashMap;
use prusti_specs::ExternSpecKind;

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
    InvalidExternSpecForTraitImpl(DefId, Span)
}

/// This struct is used to build a mapping of external functions to their
/// Prusti specifications (see `extern_fn_map`).
pub struct ExternSpecResolver<'tcx> {
    tcx: TyCtxt<'tcx>,

    /// Maps real functions (keyed by their `DefId`) to Prusti-generated fake
    /// functions with specifications. The mapping may also optionally contain
    /// the `DefId` of the implementing type to account for trait
    /// implementations.
    pub extern_fn_map: HashMap<DefId, (Option<DefId>, DefId)>,

    /// Duplicate specifications detected, keyed by the `DefId` of the function
    /// to be specified.
    spec_duplicates: HashMap<DefId, Vec<(DefId, Span)>>,

    /// Encountered errors while resolving external specs
    errors: Vec<ExternSpecResolverError>,
}

impl<'tcx> ExternSpecResolver<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            extern_fn_map: HashMap::new(),
            spec_duplicates: HashMap::new(),
            errors: Vec::new(),
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
        fn_decl: &'tcx rustc_hir::FnDecl,
        body_id: rustc_hir::BodyId,
        span: Span,
        id: rustc_hir::hir_id::HirId,
        extern_spec_kind: ExternSpecKind,
    ) {
        let mut visitor = ExternSpecVisitor {
            tcx: self.tcx,
            spec_found: None,
            kind: extern_spec_kind,
        };
        visitor.visit_fn(fn_kind, fn_decl, body_id, span, id);
        let current_def_id = self.tcx.hir().local_def_id(id).to_def_id();
        if let Some((def_id, impl_ty, span)) = visitor.spec_found {
            match self.extern_fn_map.get(&def_id) {
                Some((existing_impl_ty, _)) if existing_impl_ty == &impl_ty => {
                    match self.spec_duplicates.get_mut(&def_id) {
                        Some(dups) => {
                            dups.push((current_def_id, span));
                        }
                        None => {
                            self.spec_duplicates
                                .insert(def_id, vec![(current_def_id, span)]);
                        }
                    }
                }
                _ => {
                    self.check_validity(extern_spec_kind, def_id, span);
                    // TODO: what if def_id was present, but impl_ty was different?
                    self.extern_fn_map.insert(def_id, (impl_ty, current_def_id));
                }
            }
        }
    }

    /// Checks whether the encoded method call (call to `spec_for_def_id`) is valid.
    /// See [ExternSpecResolverError] for possible errors (including examples)
    fn check_validity(&mut self, extern_spec_kind: ExternSpecKind, spec_for_def_id: DefId, span: Span) {
        let is_trait_method = self.tcx.trait_of_item(spec_for_def_id).is_some();

        if matches!(extern_spec_kind, ExternSpecKind::InherentImpl) && is_trait_method {
            self.errors.push(
                ExternSpecResolverError::InvalidExternSpecForTraitImpl(spec_for_def_id, span)
            );
        }
        // Note: A check for matches!(extern_spec_kind, ExternSpecKind::TraitImpl) && !is_trait_method
        // is not needed because this does not typecheck (using UFCS call syntax in encoding).

        // Duplicate specs

    }

    /// Report errors encountered when resolving extern specs
    pub fn check_errors(&self, env: &Environment<'tcx>) {
        self.check_duplicates(env);

        for error in self.errors.iter() {
            match error {
                ExternSpecResolverError::InvalidExternSpecForTraitImpl(def_id, span) => {
                    let function_name = env.get_item_name(*def_id);
                    let err_note = format!("Defined an external spec for trait method '{}'. Use '#[extern_spec] impl TheTrait for TheStruct {{ ... }}' syntax instead.", function_name);
                    PrustiError::incorrect(
                        "Invalid external specification",
                        MultiSpan::from_span(*span),
                    ).add_note(err_note, None)
                        .emit(env);
                }
            }
        }
    }

    /// Report errors for duplicate specifications found during specification
    /// collection.
    fn check_duplicates(&self, env: &Environment<'tcx>) {
        for (&def_id, specs) in self.spec_duplicates.iter() {
            let function_name = env.get_item_name(def_id);
            PrustiError::incorrect(
                format!("duplicate specification for {}", function_name),
                MultiSpan::from_spans(specs.iter().map(|s| s.1).collect()),
            ).emit(env);
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
    tcx: TyCtxt<'tcx>,
    spec_found: Option<(DefId, Option<DefId>, Span)>,
    kind: ExternSpecKind,
}

/// Gets the `DefId` from the given path.
fn get_impl_type(qself: &rustc_hir::QPath<'_>) -> Option<DefId> {
    let ty = match qself {
        rustc_hir::QPath::TypeRelative(ty, _) => ty,
        rustc_hir::QPath::Resolved(Some(ty), _) => ty,
        _ => return None,
    };

    if let rustc_hir::TyKind::Path(rustc_hir::QPath::Resolved(_, path)) = ty.kind {
        if let rustc_hir::def::Res::Def(_, id) = path.res {
            return Some(id);
        }
    }

    None
}

impl<'tcx> Visitor<'tcx> for ExternSpecVisitor<'tcx> {
    type Map = Map<'tcx>;
    type NestedFilter = rustc_middle::hir::nested_filter::All;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.tcx.hir()
    }

    fn visit_expr(&mut self, ex: &'tcx rustc_hir::Expr<'tcx>) {
        if self.spec_found.is_some() {
            return;
        }
        if let rustc_hir::ExprKind::Call(callee_expr, _arguments) = ex.kind {
            if let rustc_hir::ExprKind::Path(ref qself) = callee_expr.kind {
                let res = self
                    .tcx
                    .typeck(callee_expr.hir_id.owner)
                    .qpath_res(qself, callee_expr.hir_id);
                if let rustc_hir::def::Res::Def(_, def_id) = res {
                    // We do not fetch the impl type for a trait spec, because
                    // the impl will be an auxiliary generated struct used for typechecking
                    let impl_type = if matches!(self.kind, ExternSpecKind::Trait) {
                        None
                    } else {
                        get_impl_type(qself)
                    };
                    self.spec_found = Some((def_id, impl_type, ex.span));
                    return;
                }
            }
        }
        intravisit::walk_expr(self, ex);
    }
}