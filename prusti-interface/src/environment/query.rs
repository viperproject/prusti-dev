use std::fmt::Debug;

use crate::data::ProcedureDefId;
use log::debug;
use prusti_rustc_interface::{
    ast::ast::Attribute,
    hir::hir_id::HirId,
    middle::{
        hir::map::Map,
        ty::{self, GenericArgsRef, ImplPolarity, ParamEnv, TraitPredicate, TyCtxt},
    },
    span::{
        def_id::{DefId, LocalDefId},
        source_map::SourceMap,
        Span,
    },
    trait_selection::{
        infer::{InferCtxtExt, TyCtxtInferExt},
        traits::{
            query::evaluate_obligation::InferCtxtExt as QueryInferCtxtExt, ImplSource, Obligation,
            ObligationCause, SelectionContext,
        },
    },
};
use sealed::{IntoParam, IntoParamTcx};

#[derive(Copy, Clone)]
pub struct EnvQuery<'tcx> {
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> EnvQuery<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        EnvQuery { tcx }
    }

    /// Returns the typing context
    pub(crate) fn tcx(self) -> TyCtxt<'tcx> {
        self.tcx
    }

    /// Returns the hir context
    pub fn hir(self) -> Map<'tcx> {
        self.tcx.hir()
    }

    /// Returns the `CodeMap`
    pub fn codemap(self) -> &'tcx SourceMap {
        self.tcx.sess.source_map()
    }

    // /// Returns the type of a `HirId`
    // pub fn hir_id_to_type(self, hir_id: HirId) -> ty::Ty<'tcx> {
    //     let def_id = self.tcx.hir().local_def_id(hir_id);
    //     self.tcx.type_of(def_id)
    // }

    /// Convert HirId to LocalDefId (see `local_def_id` in hir Map)
    pub fn as_local_def_id(self, def_id: HirId) -> LocalDefId {
        IntoParamTcx::into_param(def_id, self.tcx)
    }

    /// Convert LocalDefId to HirId (see `local_def_id_to_hir_id` in hir Map)
    pub fn as_hir_id(self, def_id: LocalDefId) -> HirId {
        IntoParamTcx::into_param(def_id, self.tcx)
    }

    pub fn get_local_attributes(self, def_id: impl IntoParamTcx<'tcx, HirId>) -> &'tcx [Attribute] {
        self.tcx.hir().attrs(def_id.into_param(self.tcx))
    }

    pub fn get_attributes(self, def_id: impl IntoParam<ProcedureDefId>) -> &'tcx [Attribute] {
        let def_id = def_id.into_param();
        if let Some(local_def_id) = def_id.as_local() {
            self.get_local_attributes(local_def_id)
        } else {
            self.tcx.item_attrs(def_id)
        }
    }

    /// Find whether the procedure has a particular `prusti::<name>` attribute.
    pub fn has_prusti_attribute(self, def_id: impl IntoParam<ProcedureDefId>, name: &str) -> bool {
        crate::utils::has_prusti_attr(self.get_attributes(def_id.into_param()), name)
    }

    /// Get the span of the given definition.
    pub fn get_def_span(self, def_id: impl IntoParam<DefId>) -> Span {
        self.tcx.def_span(def_id.into_param())
    }

    /// Returns true iff `def_id` has an MIR body which we may want to access
    pub fn has_body(self, def_id: impl IntoParam<DefId>) -> bool {
        let id = def_id.into_param();
        self.tcx.is_mir_available(id) && !self.tcx.is_constructor(id)
    }

    // /// Get all relevant trait declarations for some type.
    // pub fn get_traits_decls_for_type(self, ty: &ty::Ty<'tcx>) -> FxHashSet<DefId> {
    //     let mut res = FxHashSet::default();
    //     let traits = self.tcx.all_traits();
    //     for trait_id in traits {
    //         self.tcx.for_each_relevant_impl(trait_id, *ty, |impl_id| {
    //             if let Some(relevant_trait_id) = self.tcx.trait_id_of_impl(impl_id) {
    //                 res.insert(relevant_trait_id);
    //             }
    //         });
    //     }
    //     res
    // }

    /// Get an associated item by name.
    pub fn get_assoc_item(
        self,
        trait_id: impl IntoParam<DefId>,
        item_id: impl IntoParam<DefId>,
    ) -> Option<ty::AssocItem> {
        // FIXME: Probably we should use https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/ty/struct.AssociatedItems.html#method.find_by_name_and_namespace
        // instead.
        self.tcx
            .associated_items(trait_id.into_param())
            .filter_by_name_unhygienic(self.tcx.item_name(item_id.into_param()))
            .next()
            .cloned()
    }

    /// If the given DefId describes an item belonging to a trait, returns the DefId
    /// of the trait that the trait item belongs to; otherwise, returns None.
    #[tracing::instrument(level = "trace", skip(self))]
    pub fn get_trait_of_item(
        self,
        def_id: impl IntoParam<ProcedureDefId> + Debug,
    ) -> Option<DefId> {
        self.tcx.trait_of_item(def_id.into_param())
    }

    /// Returns true iff `def_id` is an implementation of a trait method
    pub fn is_trait_method_impl(self, def_id: impl IntoParam<ProcedureDefId>) -> bool {
        self.tcx
            .impl_of_method(def_id.into_param())
            .and_then(|impl_id| self.tcx.trait_id_of_impl(impl_id))
            .is_some()
    }

    /// Returns true iff `def_id` is an unsafe function.
    pub fn is_unsafe_function(self, def_id: impl IntoParam<ProcedureDefId>) -> bool {
        self.tcx
            .fn_sig(def_id.into_param())
            .instantiate_identity()
            .unsafety()
            == prusti_rustc_interface::hir::Unsafety::Unsafe
    }

    /// Computes the signature of the function with subst applied.
    pub fn get_fn_sig(
        self,
        def_id: impl IntoParam<ProcedureDefId>,
        substs: GenericArgsRef<'tcx>,
    ) -> ty::PolyFnSig<'tcx> {
        let def_id = def_id.into_param();
        let sig = if self.tcx.is_closure(def_id) {
            ty::EarlyBinder::bind(substs.as_closure().sig())
        } else {
            self.tcx.fn_sig(def_id)
        };
        sig.instantiate(self.tcx, substs)
    }

    /// Computes the signature of the function with subst applied and associated types resolved.
    pub fn get_fn_sig_resolved(
        self,
        def_id: impl IntoParam<ProcedureDefId>,
        substs: GenericArgsRef<'tcx>,
        caller_def_id: impl IntoParam<ProcedureDefId>,
    ) -> ty::PolyFnSig<'tcx> {
        let def_id = def_id.into_param();
        let sig = self.get_fn_sig(def_id, substs);
        self.resolve_assoc_types(sig, caller_def_id.into_param())
    }

    /// Returns true iff `def_id` is a closure.
    pub fn is_closure(self, def_id: impl IntoParam<DefId>) -> bool {
        self.tcx.is_closure(def_id.into_param())
    }

    // /// Returns the `DefId` of the corresponding trait method, if any.
    // /// This should not be used to resolve calls (where substs are known): use
    // /// `find_trait_method_substs` instead!
    // pub fn find_trait_method(
    //     self,
    //     impl_def_id: impl IntoParam<ProcedureDefId>, // what are we calling?
    // ) -> Option<DefId> {
    //     let impl_def_id = impl_def_id.into_param();
    //     self.tcx
    //         .impl_of_method(impl_def_id)
    //         .and_then(|impl_id| self.tcx.trait_id_of_impl(impl_id))
    //         .and_then(|trait_id| self.get_assoc_item(trait_id, impl_def_id))
    //         .map(|assoc_item| assoc_item.def_id)
    // }

    /// If the given `impl_method_def_id` is an implementation of a trait
    /// method, return the `DefId` of that trait method as well as an adapted
    /// version of the callsite `impl_method_substs` substitutions.
    pub fn find_trait_method_substs(
        self,
        impl_method_def_id: impl IntoParam<ProcedureDefId>, // what are we calling?
        impl_method_substs: GenericArgsRef<'tcx>,           // what are the substs on the call?
    ) -> Option<(ProcedureDefId, GenericArgsRef<'tcx>)> {
        let impl_method_def_id = impl_method_def_id.into_param();
        let impl_def_id = self.tcx.impl_of_method(impl_method_def_id)?;
        let trait_ref = self.tcx.impl_trait_ref(impl_def_id)?.skip_binder();

        // At this point, we know that the given method:
        // - belongs to an impl block and
        // - the impl block implements a trait.
        // For the `get_assoc_item` call, we therefore `unwrap`, as not finding
        // the associated item would be a (compiler) internal error.
        let trait_def_id = trait_ref.def_id;
        let trait_method_def_id = self
            .get_assoc_item(trait_def_id, impl_method_def_id)
            .unwrap()
            .def_id;

        // sanity check: have we been given the correct number of substs?
        let identity_impl_method = self.identity_substs(impl_method_def_id);
        assert_eq!(identity_impl_method.len(), impl_method_substs.len());

        // Given:
        // ```
        // trait Trait<Tp> {
        //     fn f<Tx, Ty, Tz>();
        // }
        // struct Struct<Ex, Ey> { ... }
        // impl<A, B, C> Trait<A> for Struct<B, C> {
        //     fn f<X, Y, Z>() { ... }
        // }
        // ```
        //
        // The various substs look like this:
        // - identity for Trait:           `[Self, Tp]`
        // - identity for Trait::f:        `[Self, Tp, Tx, Ty, Tz]`
        // - substs of the impl trait ref: `[Struct<B, C>, A]`
        // - identity for the impl:        `[A, B, C]`
        // - identity for Struct::f:       `[A, B, C, X, Y, Z]`
        //
        // What we need is a substs suitable for a call to Trait::f, which is in
        // this case `[Struct<B, C>, A, X, Y, Z]`. More generally, it is the
        // concatenation of the trait ref substs with the identity of the impl
        // method after skipping the identity of the impl.
        //
        // We also need to subst the prefix (`[Struct<B, C>, A]` in the example
        // above) with call substs, so that we get the trait's type parameters
        // more precisely. We can do this directly with `impl_method_substs`
        // because they contain the substs for the `impl` block as a prefix.
        let call_trait_substs =
            ty::EarlyBinder::bind(trait_ref.args).instantiate(self.tcx, impl_method_substs);
        let impl_substs = self.identity_substs(impl_def_id);
        let trait_method_substs = self.tcx.mk_args_from_iter(
            call_trait_substs
                .iter()
                .chain(impl_method_substs.iter().skip(impl_substs.len())),
        );

        // sanity check: do we now have the correct number of substs?
        let identity_trait_method = self.identity_substs(trait_method_def_id);
        assert_eq!(trait_method_substs.len(), identity_trait_method.len());

        Some((trait_method_def_id, trait_method_substs))
    }

    /// Given some procedure `proc_def_id` which is called, this method returns the actual method which will be executed when `proc_def_id` is defined on a trait.
    /// Returns `None` if this method can not be found or the provided `proc_def_id` is no trait item.
    #[tracing::instrument(level = "debug", skip(self))]
    pub fn find_impl_of_trait_method_call(
        self,
        proc_def_id: impl IntoParam<ProcedureDefId> + Debug,
        substs: GenericArgsRef<'tcx>,
    ) -> Option<ProcedureDefId> {
        // TODO(tymap): remove this method?
        let proc_def_id = proc_def_id.into_param();
        if let Some(trait_id) = self.get_trait_of_item(proc_def_id) {
            debug!("Fetching implementations of method '{:?}' defined in trait '{}' with substs '{:?}'", proc_def_id, self.tcx.def_path_str(trait_id), substs);
            let infcx = self.tcx.infer_ctxt().build();
            let mut sc = SelectionContext::new(&infcx);
            let trait_ref = ty::TraitRef::new(self.tcx, trait_id, substs);
            let obligation = Obligation::new(
                self.tcx,
                ObligationCause::dummy(),
                // TODO(tymap): don't use reveal_all
                ParamEnv::reveal_all(),
                TraitPredicate {
                    trait_ref,
                    polarity: ImplPolarity::Positive,
                },
            );
            let result = sc.select(&obligation);
            match result {
                Ok(Some(ImplSource::UserDefined(data))) => {
                    for item in self
                        .tcx
                        .associated_items(data.impl_def_id)
                        .in_definition_order()
                    {
                        if let Some(id) = item.trait_item_def_id {
                            if id == proc_def_id {
                                return Some(item.def_id);
                            }
                        }
                    }
                    unreachable!()
                }
                _ => None,
            }
        } else {
            None
        }
    }

    /// Given a call to `called_def_id` from within `caller_def_id`, returns
    /// the `DefId` that will actually be called if known (i.e. if a trait
    /// method call actually resolves to a concrete implementation), as well as
    /// the correct substitutions for that call. If a method is not resolved,
    /// returns the original `called_def_id` and `call_substs`.
    pub fn resolve_method_call(
        self,
        caller_def_id: impl IntoParam<ProcedureDefId>, // where are we calling from?
        called_def_id: impl IntoParam<ProcedureDefId>, // what are we calling?
        call_substs: GenericArgsRef<'tcx>,
    ) -> (ProcedureDefId, GenericArgsRef<'tcx>) {
        let called_def_id = called_def_id.into_param();

        (|| {
            // trait resolution does not depend on lifetimes, and in fact fails in the presence of uninferred regions
            let clean_substs = self.tcx.erase_regions(call_substs);

            let param_env = self.tcx.param_env(caller_def_id.into_param());
            let instance = self
                .tcx
                .resolve_instance(param_env.and((called_def_id, clean_substs)))
                .ok()??;
            let resolved_def_id = instance.def_id();
            let resolved_substs = if resolved_def_id == called_def_id {
                // if no trait resolution occurred, we can keep the non-erased substs
                call_substs
            } else {
                instance.args
            };

            Some((resolved_def_id, resolved_substs))
        })()
        .unwrap_or((called_def_id, call_substs))
    }

    /// Checks whether `ty` is copy.
    /// The type is wrapped into a `Binder` to handle regions correctly.
    /// The `param_env` should be passed as a `ProcedureDefId` which is
    /// then used to calculate the param env; i.e. the set of
    /// where-clauses that are in scope at this particular point.
    pub fn type_is_copy(
        self,
        ty: ty::Binder<'tcx, ty::Ty<'tcx>>,
        param_env: impl IntoParamTcx<'tcx, ParamEnv<'tcx>>,
    ) -> bool {
        let param_env = param_env.into_param(self.tcx);
        // Normalize the type to account for associated types
        let ty = self.resolve_assoc_types(ty, param_env);
        let ty = self.tcx.erase_late_bound_regions(ty);
        ty.is_copy_modulo_regions(
            *self.tcx.at(prusti_rustc_interface::span::DUMMY_SP),
            param_env,
        )
    }

    /// Checks whether the given type implements the trait with the given DefId.
    /// The `param_env` should be passed as a `ProcedureDefId` which is
    /// then used to calculate the param env; i.e. the set of
    /// where-clauses that are in scope at this particular point.
    pub fn type_implements_trait(
        self,
        trait_def_id: DefId,
        ty: ty::Ty<'tcx>,
        param_env: impl IntoParamTcx<'tcx, ParamEnv<'tcx>>,
    ) -> bool {
        self.type_implements_trait_with_trait_substs(trait_def_id, [ty], param_env)
    }

    /// Checks whether the given type implements the trait with the given DefId.
    /// Accounts for generic params on the trait by the given `trait_substs`.
    /// The `param_env` should be passed as a `ProcedureDefId` which is
    /// then used to calculate the param env; i.e. the set of
    /// where-clauses that are in scope at this particular point.
    pub fn type_implements_trait_with_trait_substs(
        self,
        trait_def_id: DefId,
        trait_substs: impl IntoIterator<Item = impl Into<ty::GenericArg<'tcx>>>,
        param_env: impl IntoParamTcx<'tcx, ParamEnv<'tcx>>,
    ) -> bool {
        assert!(self.tcx.is_trait(trait_def_id));
        let infcx = self.tcx.infer_ctxt().build();
        infcx
            .type_implements_trait(
                trait_def_id,
                // If `ty` has any inference variables (e.g. a region variable), then using it with
                // the freshly-created `InferCtxt` (i.e. `tcx.infer_ctxt().enter(..)`) will cause
                // a panic, since those inference variables don't exist in the new `InferCtxt`.
                // See: https://rust-lang.zulipchat.com/#narrow/stream/182449-t-compiler.2Fhelp/topic/.E2.9C.94.20Panic.20in.20is_copy_modulo_regions
                trait_substs.into_iter().map(|ty| infcx.freshen(ty.into())),
                param_env.into_param(self.tcx),
            )
            .must_apply_considering_regions()
    }

    /// Return the default substitutions for a particular item, i.e. where each
    /// generic maps to itself.
    pub fn identity_substs(self, def_id: impl IntoParam<ProcedureDefId>) -> GenericArgsRef<'tcx> {
        ty::List::identity_for_item(self.tcx, def_id.into_param())
    }

    /// Evaluates the provided [ty::Predicate].
    /// Returns true if the predicate is fulfilled.
    /// Returns false if the predicate is not fulfilled or it could not be evaluated.
    /// The `param_env` should be passed as a `ProcedureDefId` which is
    /// then used to calculate the param env; i.e. the set of
    /// where-clauses that are in scope at this particular point.
    #[tracing::instrument(level = "debug", skip(self))]
    pub fn evaluate_predicate(
        self,
        predicate: ty::Predicate<'tcx>,
        param_env: impl IntoParamTcx<'tcx, ParamEnv<'tcx>> + Debug,
    ) -> bool {
        let obligation = Obligation::new(
            self.tcx,
            ObligationCause::dummy(),
            param_env.into_param(self.tcx),
            predicate,
        );

        self.tcx
            .infer_ctxt()
            .build()
            .predicate_must_hold_considering_regions(&obligation)
    }

    /// Normalizes associated types in foldable types,
    /// i.e. this resolves projection types ([ty::TyKind::Projection]s)
    /// **Important:** Regions while be erased during this process
    /// The `param_env` should be passed as a `ProcedureDefId` which is
    /// then used to calculate the param env; i.e. the set of
    /// where-clauses that are in scope at this particular point.
    #[tracing::instrument(level = "debug", skip(self))]
    pub fn resolve_assoc_types<T: ty::TypeFoldable<TyCtxt<'tcx>> + Debug + Copy>(
        self,
        normalizable: T,
        param_env: impl IntoParamTcx<'tcx, ParamEnv<'tcx>> + Debug,
    ) -> T {
        let param_env = param_env.into_param(self.tcx);
        let norm_res = self
            .tcx
            .try_normalize_erasing_regions(param_env, normalizable);

        match norm_res {
            Ok(normalized) => {
                debug!("Normalized {:?}: {:?}", normalizable, normalized);
                normalized
            }
            Err(err) => {
                debug!(
                    "Error while resolving associated types for {:?}: {:?}",
                    normalizable, err
                );
                normalizable
            }
        }
    }
}

mod sealed {
    use prusti_rustc_interface::{
        hir::hir_id::{HirId, OwnerId},
        middle::ty::{ParamEnv, TyCtxt},
        span::def_id::{DefId, LocalDefId},
    };

    pub trait IntoParam<P> {
        fn into_param(self) -> P;
    }
    impl<P> IntoParam<P> for P {
        #[inline(always)]
        fn into_param(self) -> P {
            self
        }
    }
    impl<'a, P: Copy> IntoParam<P> for &'a P {
        #[inline(always)]
        fn into_param(self) -> P {
            *self
        }
    }
    impl IntoParam<DefId> for LocalDefId {
        #[inline(always)]
        fn into_param(self) -> DefId {
            self.to_def_id()
        }
    }
    impl IntoParam<DefId> for OwnerId {
        #[inline(always)]
        fn into_param(self) -> DefId {
            self.to_def_id()
        }
    }
    impl IntoParam<LocalDefId> for OwnerId {
        #[inline(always)]
        fn into_param(self) -> LocalDefId {
            self.def_id
        }
    }

    pub trait IntoParamTcx<'tcx, P> {
        fn into_param(self, tcx: TyCtxt<'tcx>) -> P;
    }
    impl<'tcx, T: IntoParam<U>, U> IntoParamTcx<'tcx, U> for T {
        #[inline(always)]
        fn into_param(self, _tcx: TyCtxt<'tcx>) -> U {
            self.into_param()
        }
    }
    impl<'tcx> IntoParamTcx<'tcx, HirId> for OwnerId {
        #[inline(always)]
        fn into_param(self, tcx: TyCtxt<'tcx>) -> HirId {
            tcx.hir().local_def_id_to_hir_id(self.def_id)
        }
    }
    impl<'tcx> IntoParamTcx<'tcx, HirId> for LocalDefId {
        #[inline(always)]
        fn into_param(self, tcx: TyCtxt<'tcx>) -> HirId {
            tcx.hir().local_def_id_to_hir_id(self)
        }
    }
    impl<'tcx> IntoParamTcx<'tcx, LocalDefId> for HirId {
        #[inline(always)]
        fn into_param(self, _tcx: TyCtxt<'tcx>) -> LocalDefId {
            self.owner.def_id
        }
    }
    impl<'tcx> IntoParamTcx<'tcx, ParamEnv<'tcx>> for DefId {
        #[inline(always)]
        fn into_param(self, tcx: TyCtxt<'tcx>) -> ParamEnv<'tcx> {
            tcx.param_env(self)
        }
    }
}
