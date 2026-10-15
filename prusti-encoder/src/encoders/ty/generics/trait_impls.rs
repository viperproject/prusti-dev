use prusti_interface::PrustiError;
use prusti_rustc_interface::{
    data_structures::fx::{FxHashSet, FxIndexMap, FxIndexSet},
    errors::MultiSpan,
    middle::{mir, traits::specialization_graph, ty},
    span::def_id::DefId,
};
use task_encoder::{EncodeFullError, EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{CastType, Domain, Method, MethodIdn, ViperIdent, vir_format_identifier};

use crate::{
    encoders::{
        ConstEnc, FunctionCallEnc, MirLocalDefEnc, MirLocalDefEncTask, MirSpecEnc, Pure,
        r#const::ConstEncTask,
        mir_fn::{CallTaskDescription, RustSignature},
        pure::spec::MirSpecEncMode,
        ty::{
            RustTy, RustTyDecomposition,
            generics::{
                GArgs, GArgsCastEnc, GArgsTyEnc, GParams, GenericParamsEnc, r#trait::TraitEnc,
                trait_fn::TraitFnEnc,
            },
            lifted::TyConstructorEnc,
        },
    },
    trait_support::is_function_with_body,
};

/// Encodes the behavioral-subtyping proof obligations of a trait impl:
/// methods checking that each impl fn weakens the trait fn's precondition and
/// strengthens its postcondition. Only run on local impls (foreign impls are
/// trusted to conform, their conditions and axioms are encoded by
/// [`TraitImplConditionEnc`]).
pub struct TraitImplEnc;

impl TaskEncoder for TraitImplEnc {
    task_encoder::encoder_cache!(TraitImplEnc);
    const ENCODER_NAME: &'static str = "trait impl encoder";

    type TaskDescription<'vir> = DefId;
    type OutputFullLocal<'vir> = Vec<Method<'vir>>;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;

        vir::with_vcx(|vcx| {
            let tcx = vcx.tcx();

            let all_impls = tcx.trait_impls_in_crate(task_key.krate);
            let idx = all_impls.iter().position(|did| did == task_key).unwrap();

            let impl_context = GParams::from(*task_key);

            let trait_ref = tcx.impl_trait_ref(*task_key).instantiate_identity();
            let trait_did = trait_ref.skip_normalization().def_id;
            let trait_data = deps.require_ref::<TraitEnc>(trait_did)?;
            let trait_name = trait_data.trait_name;

            let mut methods = Vec::new();

            let implementing_ty = tcx
                .type_of(*task_key)
                .instantiate_identity()
                .skip_normalization();
            let implementing_ty = RustTyDecomposition::from_ty(implementing_ty, impl_context);
            let implementing_ty = implementing_ty.ty.name();

            for impl_item in tcx.associated_items(*task_key).in_definition_order() {
                let ty::AssocKind::Fn { .. } = impl_item.kind else {
                    continue;
                };
                let trait_item_def_id = impl_item.trait_item_def_id().unwrap();
                let impl_item_def_id = impl_item.def_id;
                let impl_span = vcx.tcx().def_span(impl_item_def_id);
                let item_name = ViperIdent::from_def_id(vcx, impl_item_def_id);

                let impl_item_context = GParams::from(impl_item_def_id);
                let impl_item_params = deps.require_dep::<GenericParamsEnc>(impl_item_context)?;
                let trait_ty_decls = impl_item_params.ty_decls();
                let trait_const_decls = impl_item_params.const_decls();

                let local_defs = deps.require_dep::<MirLocalDefEnc>(MirLocalDefEncTask::Local {
                    def_id: impl_item_def_id,
                    all_locals: false,
                })?;
                let arg_count = local_defs.arg_count + 1;
                let ref_args = vcx.alloc_slice(&vec![vir::TYPE_REF; arg_count]);

                let impl_item_is_pure = crate::encoders::is_function_pure(
                    impl_item_def_id,
                    GArgs::new(impl_item_context, impl_item_context.rust_params()),
                );

                let impl_item_has_body = is_function_with_body(vcx.tcx(), impl_item_def_id);

                let trait_item_spec = deps.require_dep_spanned::<MirSpecEnc>(
                    (trait_item_def_id, impl_item_def_id, MirSpecEncMode::Impure),
                    impl_span,
                )?;
                let impl_item_spec = deps.require_dep_spanned::<MirSpecEnc>(
                    (impl_item_def_id, impl_item_def_id, MirSpecEncMode::Impure),
                    impl_span,
                )?;

                let mut impure_arg_preds = Vec::new();
                let mut ref_arg_decls = Vec::with_capacity(arg_count);
                for arg_idx in (0..arg_count).map(mir::Local::from) {
                    let name_p = local_defs[arg_idx].local.name;
                    ref_arg_decls.push(vir::vir_local_decl! { vcx; [name_p] : Ref });
                    if arg_idx != mir::RETURN_PLACE {
                        impure_arg_preds.push(local_defs[arg_idx].impure_pred);
                    }
                }
                // TODO: wands

                let mut pre_weaken_pres = impure_arg_preds.clone();
                pre_weaken_pres.extend(trait_item_spec.pre_exprs());

                // Spans of the trait method's preconditions, to point the
                // behavioral-subtyping error's hint at them.
                let trait_pre_spans: Vec<_> =
                    trait_item_spec.pres.iter().map(|(_, s)| *s).collect();

                // Both checks are only needed where the impl applies.
                let bounds = Self::assume_context_bounds(vcx, deps, impl_item_context)?;

                methods.push(vcx.mk_method(
                    MethodIdn::<(vir::ManyRef, vir::ManyTyVal, vir::ManyCSnap)>::new(
                        vir_format_identifier!(vcx, "trait_{trait_name}_impl_{implementing_ty}_{idx}_fn_pre_weaken_{item_name}"),
                        (ref_args, impl_item_params.ty_args(), impl_item_params.const_args()),
                    ),
                    (ref_arg_decls.as_slice(), trait_ty_decls, trait_const_decls),
                    &[],
                    vcx.alloc_slice(&pre_weaken_pres),
                    &[],
                    Some(vcx.alloc_slice(&[
                        vcx.mk_cfg_block(
                            &vir::CfgBlockLabelData::Start,
                            &[],
                            vcx.alloc_slice(&bounds.iter().copied().chain(impl_item_spec.pres.iter().copied()
                                .map(|(pre, pre_span)| vcx.with_span(pre_span, |vcx| {
                                    let trait_pre_spans = trait_pre_spans.clone();
                                    vcx.handle_error("exhale.failed:assertion.false", move |_| {
                                        let mut err = PrustiError::verification(
                                            "the implementation's precondition may be stronger than the trait method's",
                                            pre_span.into(),
                                        );
                                        for trait_span in &trait_pre_spans {
                                            err = err.add_note(
                                                "the trait method's precondition is declared here",
                                                Some(*trait_span),
                                            );
                                        }
                                        Some(vec![err])
                                    });
                                    vcx.mk_exhale_stmt(pre)
                                })))
                                .collect::<Vec<_>>()),
                            vcx.alloc(vir::TerminatorStmtData::Exit),
                        )
                    ])),
                ));

                let mut post_strengthen_pres = impure_arg_preds;
                post_strengthen_pres.extend(trait_item_spec.pre_exprs());

                // exceptionally, we also put the allocated result in the precondition
                post_strengthen_pres.push(local_defs[mir::RETURN_PLACE].impure_pred);

                // here we inhale the impl postconditions, since they
                // can contain "old" variables
                let mut stmts = bounds;
                for post in impl_item_spec.post_exprs() {
                    stmts.push(vcx.mk_inhale_stmt(post));
                }
                if impl_item_has_body && impl_item_is_pure {
                    let pure_func = deps.require_dep::<FunctionCallEnc>(
                        CallTaskDescription::new(
                            impl_item_def_id,
                            impl_item_context.rust_params(),
                            impl_item_def_id,
                        )
                        .resolve_trait_calls(false),
                    )?;
                    let pure_func_app = pure_func.call_pure(
                        local_defs
                            .args()
                            .map(|arg| arg.impure_snap)
                            .collect::<Vec<_>>(),
                    );
                    stmts.push(vcx.mk_inhale_stmt(vir::expr! {
                        ([local_defs[mir::RETURN_PLACE].impure_snap]) == ([pure_func_app])
                    }));
                }
                // The failing exhale is a trait postcondition, but the problem
                // is the impl's postcondition being too weak: point the error at
                // the impl's postcondition(s) and hint at the trait's.
                let impl_post_spans: Vec<_> =
                    impl_item_spec.posts.iter().map(|(_, s)| *s).collect();
                for &(post, trait_post_span) in &trait_item_spec.posts {
                    let impl_post_spans = impl_post_spans.clone();
                    vcx.with_span(impl_span, |vcx| {
                        vcx.handle_error("exhale.failed:assertion.false", move |_| {
                            let primary = if impl_post_spans.is_empty() {
                                impl_span.into()
                            } else {
                                MultiSpan::from_spans(impl_post_spans.clone())
                            };
                            let err = PrustiError::verification(
                                "the implementation's postcondition may be weaker than the trait method's",
                                primary,
                            )
                            .add_note(
                                "the trait method's (stronger) postcondition is declared here",
                                Some(trait_post_span),
                            );
                            Some(vec![err])
                        });
                        stmts.push(vcx.mk_exhale_stmt(post));
                    });
                }

                methods.push(vcx.mk_method(
                    MethodIdn::<(vir::ManyRef, vir::ManyTyVal, vir::ManyCSnap)>::new(
                        vir_format_identifier!(vcx, "trait_{trait_name}_impl_{implementing_ty}_{idx}_fn_post_strengthen_{item_name}"),
                        (ref_args, impl_item_params.ty_args(), impl_item_params.const_args()),
                    ),
                    (ref_arg_decls.as_slice(), trait_ty_decls, trait_const_decls),
                    &[],
                    vcx.alloc_slice(&post_strengthen_pres),
                    &[],
                    Some(vcx.alloc_slice(&[
                        vcx.mk_cfg_block(
                            &vir::CfgBlockLabelData::Start,
                            &[],
                            vcx.alloc_slice(&stmts),
                            vcx.alloc(vir::TerminatorStmtData::Exit),
                        )
                    ])),
                ));
            }

            // Make the impl visible to the trait's `impl_fun`.
            if implements_trait(tcx, *task_key) {
                deps.require_dep::<TraitImplConditionEnc>(*task_key)?;
            }

            Ok((methods, ()))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for methods in Self::all_outputs_local_no_errors(program) {
            for method in methods {
                program.add_method(method);
            }
        }
    }
}

/// Encodes the applicability condition of a trait impl: the axiom that the
/// trait's `impl_fun` holds at the impl's trait ref wherever the impl's
/// where-clauses do. The per-item assumable content (associated type
/// resolution, fn-spec axioms) is encoded individually by
/// [`TraitImplItemEnc`], guarded by the same where-clauses. Unlike
/// [`TraitImplEnc`], this is safe to run on foreign impls: it produces no
/// proof obligations, so foreign impls are assumed - not re-verified - to be
/// behavioural subtypes.
pub struct TraitImplConditionEnc;

impl TaskEncoder for TraitImplConditionEnc {
    task_encoder::encoder_cache!(TraitImplConditionEnc);
    const ENCODER_NAME: &'static str = "trait impl condition encoder";

    type TaskDescription<'vir> = DefId;
    type OutputFullLocal<'vir> = Domain<'vir>;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;

        vir::with_vcx(|vcx| {
            let tcx = vcx.tcx();
            let impl_name = impl_name(vcx, *task_key);

            let impl_context = GParams::from(*task_key);
            let trait_ref = tcx
                .impl_trait_ref(*task_key)
                .instantiate_identity()
                .skip_normalization();
            let trait_ = deps.require_ref::<TraitEnc>(trait_ref.def_id)?;
            let args = deps.require_dep::<GArgsTyEnc>(GArgs::new(impl_context, trait_ref.args))?;
            let impl_check = (trait_.impl_fun)(args.get_ty(), args.get_const());

            // Triggering on the application at the impl's trait ref (rather
            // than quantifying over the trait's parameters) keeps an impl's
            // axiom from firing for applications it cannot match.
            let axiom = TraitImplEnc::guarded_forall(
                vcx,
                deps,
                *task_key,
                *task_key,
                &[],
                impl_check.upcast_ty(),
                impl_check,
            )?;
            let domain = vcx.mk_domain(
                vir_format_identifier!(vcx, "trait_{impl_name}_condition"),
                &[],
                vcx.alloc_slice(&[vcx
                    .mk_domain_axiom(vir_format_identifier!(vcx, "{impl_name}_condition"), axiom)]),
                &[],
                None,
            );
            Ok((domain, ()))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for domain in Self::all_outputs_local_no_errors(program) {
            program.add_domain(domain);
        }
    }
}

impl TraitImplEnc {
    /// The generic indices a projection requires to be bound before it can be
    /// processed, and those it binds itself.
    fn projection_deps<'vir>(
        projection: ty::ProjectionPredicate<'vir>,
    ) -> (FxIndexSet<u32>, FxIndexSet<u32>) {
        let generic_idx = |arg: ty::GenericArg| match arg.kind() {
            ty::GenericArgKind::Type(ty) if let ty::TyKind::Param(p) = ty.kind() => Some(p.index),
            ty::GenericArgKind::Const(const_) if let ty::ConstKind::Param(p) = const_.kind() => {
                Some(p.index)
            }
            _ => None,
        };

        let required = projection
            .projection_term
            .args
            .iter()
            .flat_map(|arg| arg.walk().filter_map(generic_idx))
            .collect();

        let produced = projection.term.walk().filter_map(generic_idx).collect();

        (required, produced)
    }

    /// Topologically sorts the projections such that each one requires only
    /// generics that are initially known or produced by an earlier projection
    /// (Kahn's algorithm, where emitting a projection makes its produced
    /// generics known). Panics if no such order exists; rustc's constrained-
    /// parameter check guarantees one does for valid impls.
    fn order_projections<'vir>(
        known_generics: impl IntoIterator<Item = u32>,
        projections: impl IntoIterator<Item = ty::ProjectionPredicate<'vir>>,
    ) -> Vec<ty::ProjectionPredicate<'vir>> {
        let mut known: FxIndexSet<u32> = known_generics.into_iter().collect();

        let projections: Vec<_> = projections
            .into_iter()
            .map(|p| (p, Self::projection_deps(p)))
            .collect();

        // For each unknown generic, the projections waiting on it; for each
        // projection, the number of its required generics still unknown.
        let mut waiting_on: FxIndexMap<u32, Vec<usize>> = FxIndexMap::default();
        let mut unmet = vec![0usize; projections.len()];
        // The output doubles as the FIFO worklist: `ordered[cursor..]` are the
        // ready but not yet processed projections.
        let mut ordered = Vec::with_capacity(projections.len());
        for (i, (_, (required, _))) in projections.iter().enumerate() {
            for &g in required {
                if !known.contains(&g) {
                    unmet[i] += 1;
                    waiting_on.entry(g).or_default().push(i);
                }
            }
            if unmet[i] == 0 {
                ordered.push(i);
            }
        }

        let mut cursor = 0;
        while let Some(&i) = ordered.get(cursor) {
            cursor += 1;
            let (_, (_, produced)) = &projections[i];
            for &g in produced {
                if known.insert(g) {
                    for &j in waiting_on.get(&g).into_iter().flatten() {
                        unmet[j] -= 1;
                        if unmet[j] == 0 {
                            ordered.push(j);
                        }
                    }
                }
            }
        }

        assert_eq!(
            ordered.len(),
            projections.len(),
            "cyclic or unresolvable projection bounds"
        );
        ordered.into_iter().map(|i| projections[i].0).collect()
    }

    fn discover_bind_points<'vir, E: TaskEncoder + 'vir + ?Sized>(
        deps: &mut TaskEncoderDependencies<'vir, E>,
        generic_map: &mut FxIndexMap<u32, vir::ExprDyn<'vir>>,
        ctx: GParams<'vir>,
        expr: vir::ExprTyVal<'vir>,
        ty: ty::Ty<'vir>,
    ) -> Result<(), EncodeFullError<'vir, E>> {
        if let ty::TyKind::Param(p) = ty.kind() {
            generic_map.entry(p.index).or_insert(expr.upcast_ty());
            return Ok(());
        }

        let decomp = RustTyDecomposition::from_ty(ty, ctx);
        let ty_enc = deps.require_ref::<TyConstructorEnc>(decomp.ty)?;

        let args = decomp.args.args();
        let inner_types = args.iter().filter_map(|arg| arg.as_type());
        for (i, inner_ty) in inner_types.enumerate() {
            let accessor = ty_enc.ty_param_accessors[i];
            let inner_expr = accessor.call()(expr);

            Self::discover_bind_points(deps, generic_map, ctx, inner_expr, inner_ty)?;
        }

        let inner_consts = args.iter().filter_map(|arg| arg.as_const());
        for (i, inner_const) in inner_consts.enumerate() {
            let accessor = ty_enc.const_param_accessors[i];
            let inner_expr = accessor.call()(expr);

            if let ty::ConstKind::Param(p) = inner_const.kind() {
                generic_map.entry(p.index).or_insert(inner_expr.upcast_ty());
            }
        }
        Ok(())
    }

    /// Assumes the where-clauses in force in `ctx`. rustc guarantees them at
    /// every instantiation, and resolving through an impl (its associated
    /// types and fn specs are guarded by its where-clauses) may depend on
    /// them. Assumed rather than required, since callers could not always
    /// discharge them (e.g. `Fn*` bounds, which have no encoded impls).
    pub(crate) fn assume_context_bounds<'vir, E: TaskEncoder + 'vir + ?Sized>(
        vcx: &'vir vir::VirCtxt<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, E>,
        ctx: GParams<'vir>,
    ) -> Result<Vec<vir::Stmt<'vir>>, EncodeFullError<'vir, E>> {
        Ok(Self::context_bounds(vcx, deps, ctx, None)?
            .into_iter()
            .map(|bound| vcx.mk_inhale_stmt(bound))
            .collect())
    }

    /// The where-clauses in force in `ctx`, stated over its parameters.
    ///
    /// With `bind_points`, the projection bounds are processed in an order in
    /// which each only reads parameters already bound, and any parameter a
    /// projection determines is added to `bind_points` (the parameters
    /// initially in `bind_points` count as bound).
    pub(crate) fn context_bounds<'vir, E: TaskEncoder + 'vir + ?Sized>(
        vcx: &'vir vir::VirCtxt<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, E>,
        ctx: GParams<'vir>,
        mut bind_points: Option<&mut FxIndexMap<u32, vir::ExprDyn<'vir>>>,
    ) -> Result<Vec<vir::ExprBool<'vir>>, EncodeFullError<'vir, E>> {
        let tcx = vcx.tcx();
        let params = deps.require_dep::<GenericParamsEnc>(ctx)?;
        let caller_bounds = ctx.typing_env().param_env.caller_bounds();
        let mut checks = Vec::new();

        let trait_preds = caller_bounds
            .iter()
            .filter_map(ty::Clause::as_trait_clause)
            .map(ty::Binder::skip_binder)
            .filter(|pred| pred.polarity == ty::PredicatePolarity::Positive)
            // Holds of every type (see `SizednessEnc`).
            .filter(|pred| Some(pred.def_id()) != tcx.lang_items().pointee_sized_trait());
        for trait_pred in trait_preds {
            let trait_ = deps.require_ref::<TraitEnc>(trait_pred.def_id())?;
            let gargs = GArgs::new(ctx, trait_pred.trait_ref.args);
            let gargs = deps.require_dep::<GArgsTyEnc>(gargs)?;
            checks.push((trait_.impl_fun)(gargs.get_ty(), gargs.get_const()));
        }

        let proj_preds = caller_bounds
            .iter()
            .filter_map(ty::Clause::as_projection_clause)
            .map(ty::Binder::skip_binder);
        let proj_preds: Vec<_> = match &bind_points {
            Some(bound) => Self::order_projections(bound.keys().copied(), proj_preds),
            None => proj_preds.collect(),
        };
        for proj_pred in proj_preds {
            let trait_did = proj_pred.trait_def_id(tcx);
            let trait_ = deps.require_ref::<TraitEnc>(trait_did)?;
            let gargs = GArgs::new(ctx, proj_pred.projection_term.args);
            let gargs = deps.require_dep::<GArgsTyEnc>(gargs)?;

            let (projection, expr): (vir::ExprDyn, vir::ExprDyn) = match proj_pred.term.kind() {
                ty::TermKind::Ty(ty) => {
                    let projection =
                        trait_.assoc_types[&proj_pred.def_id()](gargs.get_ty(), gargs.get_const());
                    let decomp = RustTyDecomposition::from_ty(ty, ctx);
                    let ty_expr = params.ty_expr(deps, decomp);
                    if let Some(bound) = bind_points.as_deref_mut() {
                        Self::discover_bind_points(deps, bound, ctx, projection, ty)?;
                    }
                    (projection.upcast_ty(), ty_expr?.upcast_ty())
                }
                ty::TermKind::Const(const_) => {
                    let projection =
                        trait_.assoc_consts[&proj_pred.def_id()](gargs.get_ty(), gargs.get_const());
                    let ty = tcx
                        .type_of(proj_pred.def_id())
                        .instantiate_identity()
                        .skip_normalization();
                    let const_task = ConstEncTask::Ty {
                        const_,
                        ty,
                        context: ctx,
                    };
                    let const_expr = deps.require_dep::<ConstEnc>(const_task)?;
                    if let Some(bound) = bind_points.as_deref_mut()
                        && let ty::ConstKind::Param(p) = const_.kind()
                    {
                        bound.entry(p.index).or_insert(const_expr.upcast_ty());
                    }
                    (projection.upcast_ty(), const_expr.upcast_ty())
                }
            };

            checks.push(vcx.mk_eq_expr(projection, expr));
        }

        Ok(checks)
    }

    /// `forall params :: {trigger} impl_bounds ==> body`: an assertion about
    /// the impl `impl_did` that only holds where the impl applies, i.e. where
    /// its where-clauses hold.
    ///
    /// Quantifies over the parameters of `item_did` (the impl itself or one
    /// of its items, whose parameters extend the impl's) and `extra`. The
    /// trigger is applied to the impl's trait ref followed by the item's own
    /// parameters; an impl parameter not occurring in those is instead
    /// let-bound to the projection that determines it: rustc only accepts
    /// such an impl parameter if a projection bound constrains it (E0207),
    /// and binding it keeps every quantified variable covered by the
    /// trigger. If the trigger mentions it nonetheless (through `extra` or
    /// `trigger`, e.g. in an item's signature), it is quantified and
    /// constrained to equal the projection instead.
    pub(super) fn guarded_forall<'vir, E: TaskEncoder + 'vir + ?Sized>(
        vcx: &'vir vir::VirCtxt<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, E>,
        impl_did: DefId,
        item_did: DefId,
        extra: &[vir::LocalDeclDyn<'vir>],
        trigger: vir::ExprDyn<'vir>,
        body: vir::ExprBool<'vir>,
    ) -> Result<vir::ExprBool<'vir>, EncodeFullError<'vir, E>> {
        Self::guarded_forall_in(
            vcx,
            deps,
            impl_did,
            GParams::from(impl_did),
            GParams::from(item_did),
            extra,
            trigger,
            body,
        )
    }

    /// [`Self::guarded_forall`] with the contexts of the impl and the item
    /// given explicitly, e.g. suffixed so that their parameters cannot capture
    /// variables of `body`.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn guarded_forall_in<'vir, E: TaskEncoder + 'vir + ?Sized>(
        vcx: &'vir vir::VirCtxt<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, E>,
        impl_did: DefId,
        impl_ctx: GParams<'vir>,
        item_ctx: GParams<'vir>,
        extra: &[vir::LocalDeclDyn<'vir>],
        trigger: vir::ExprDyn<'vir>,
        body: vir::ExprBool<'vir>,
    ) -> Result<vir::ExprBool<'vir>, EncodeFullError<'vir, E>> {
        let item_params = deps.require_dep::<GenericParamsEnc>(item_ctx)?;
        let decl = |idx: u32| match item_params.map_idx(idx) {
            Ok(idx) => item_params.ty_decls()[idx].upcast_ty(),
            Err(idx) => item_params.const_decls()[idx].upcast_ty(),
        };

        let trait_ref = vcx
            .tcx()
            .impl_trait_ref(impl_did)
            .instantiate_identity()
            .skip_normalization();
        let item_args = &item_ctx.rust_params()[impl_ctx.rust_params().len()..];
        let pinned = trait_ref.args.iter().chain(item_args.iter().copied());

        let mut bind_points = FxIndexMap::default();
        for arg in pinned.flat_map(|arg| arg.walk()) {
            let idx = match arg.kind() {
                ty::GenericArgKind::Type(ty) if let ty::TyKind::Param(p) = ty.kind() => p.index,
                ty::GenericArgKind::Const(c) if let ty::ConstKind::Param(p) = c.kind() => p.index,
                _ => continue,
            };
            bind_points
                .entry(idx)
                .or_insert_with(|| vcx.mk_local_ex(decl(idx)).upcast_ty());
        }
        let pinned_count = bind_points.len();

        let bounds = Self::context_bounds(vcx, deps, impl_ctx, Some(&mut bind_points))?;
        let body = if bounds.is_empty() {
            body
        } else {
            let guard = vcx.mk_conj(&bounds);
            vir::expr! { (guard) ==> (body) }
        };

        // A parameter determined by a projection that the trigger mentions
        // (e.g. `U` of `F: FnMut(T) -> U` in an item's signature) cannot be
        // let-bound, since the trigger would refer to a variable bound only
        // in the body. It is quantified instead, constrained to equal the
        // projection inside the remaining lets.
        let mut trigger_locals = FxHashSet::default();
        vir::collect_locals(trigger, &mut trigger_locals);
        let (constrained, lets): (Vec<_>, Vec<_>) = bind_points
            .split_off(pinned_count)
            .into_iter()
            .partition(|&(idx, _)| trigger_locals.contains(decl(idx).name));
        let body = if constrained.is_empty() {
            body
        } else {
            let eqs = constrained
                .iter()
                .map(|&(idx, expr)| vcx.mk_eq_expr(vcx.mk_local_ex(decl(idx)).upcast_ty(), expr))
                .collect::<Vec<_>>();
            let eqs = vcx.mk_conj(&eqs);
            vir::expr! { (eqs) ==> (body) }
        };
        let body = lets.iter().rfold(body, |acc, &(idx, expr)| {
            vcx.mk_let_expr(decl(idx), expr, acc)
        });

        let qvars = (0..item_ctx.rust_params().len() as u32)
            .filter(|&idx| item_ctx.rust_params()[idx as usize].as_region().is_none())
            .filter(|idx| !lets.iter().any(|(let_idx, _)| let_idx == idx))
            .map(decl)
            .chain(extra.iter().copied())
            .collect::<Vec<_>>();
        // Known matching loop: an impl forwarding to a projection of its own
        // parameter, such as rand_core's
        //
        //     impl<R: DerefMut> TryRng for R where R::Target: TryRng {
        //         type Error = <R::Target as TryRng>::Error;
        //     }
        //
        // gets `{TryRng_impl(R)}` with the guard `TryRng_impl(Target(R))`,
        // and `{Error(R)}` with the equation `Error(R) == Error(Target(R))`.
        // Each instance creates a term matching its trigger again with
        // `R := Target(R)`, and `Target` never resolves at a type without a
        // `Deref` impl. Z3 defers such deep instances. Requiring `Target(R)`
        // in the trigger would stop the chain, but also stop resolving
        // `<&mut S as TryRng>::Error` where only `Error(&mut S)` occurs.
        Ok(vcx.mk_forall_expr(
            vcx.alloc_slice(&qvars),
            vcx.alloc_slice(&[vcx.mk_trigger(&[trigger])]),
            body,
        ))
    }

    /// Whether the impl applies at the trait ref with the given arguments:
    /// they are the impl's trait ref at some instantiation of its parameters,
    /// and its where-clauses hold there. Unlike [`Self::guarded_forall`],
    /// which quantifies over the impl's parameters, this is stated over the
    /// arguments; the impl's parameters are let-bound to the subterms of the
    /// arguments they occur in (in a suffixed context, so that they cannot
    /// capture the arguments' variables), or to the projection determining
    /// them.
    pub(super) fn applies_at<'vir, E: TaskEncoder + 'vir + ?Sized>(
        vcx: &'vir vir::VirCtxt<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, E>,
        impl_did: DefId,
        trait_tys: &[vir::ExprTyVal<'vir>],
        trait_consts: &[vir::ExprCSnap<'vir>],
    ) -> Result<vir::ExprBool<'vir>, EncodeFullError<'vir, E>> {
        let impl_ctx = GParams::from(impl_did).with_suffix("impl");
        let impl_params = deps.require_dep::<GenericParamsEnc>(impl_ctx)?;
        let trait_ref = vcx
            .tcx()
            .impl_trait_ref(impl_did)
            .instantiate_identity()
            .skip_normalization();

        let mut bind_points = FxIndexMap::default();
        for (&expr, ty) in std::iter::zip(trait_tys, trait_ref.args.types()) {
            Self::discover_bind_points(deps, &mut bind_points, impl_ctx, expr, ty)?;
        }
        for (&expr, const_) in std::iter::zip(trait_consts, trait_ref.args.consts()) {
            if let ty::ConstKind::Param(p) = const_.kind() {
                bind_points.entry(p.index).or_insert(expr.upcast_ty());
            }
        }

        let args = deps.require_dep::<GArgsTyEnc>(GArgs::new(impl_ctx, trait_ref.args))?;
        let mut checks = Vec::new();
        for (&arg, &impl_arg) in std::iter::zip(trait_tys, args.get_ty()) {
            checks.push(vcx.mk_eq_expr(arg, impl_arg));
        }
        for (&arg, &impl_arg) in std::iter::zip(trait_consts, args.get_const()) {
            checks.push(vcx.mk_eq_expr(arg, impl_arg));
        }
        checks.extend(Self::context_bounds(
            vcx,
            deps,
            impl_ctx,
            Some(&mut bind_points),
        )?);

        let checks = vcx.mk_conj(&checks);
        Ok(bind_points.iter().rfold(checks, |acc, (&idx, &expr)| {
            let decl = match impl_params.map_idx(idx) {
                Ok(idx) => impl_params.ty_decls()[idx].upcast_ty(),
                Err(idx) => impl_params.const_decls()[idx].upcast_ty(),
            };
            vcx.mk_let_expr(decl, expr, acc)
        }))
    }
}

/// The impls of a trait that make it hold (see [`implements_trait`]).
pub(super) fn implementing_impls(
    tcx: ty::TyCtxt<'_>,
    trait_did: DefId,
) -> impl Iterator<Item = DefId> {
    tcx.all_impls(trait_did)
        .filter(move |&impl_did| implements_trait(tcx, impl_did))
}

/// Whether the impl makes its trait ref hold, i.e. whether its condition
/// and items may be assumed. Negative impls (`impl !Tr for X`) and
/// reservation impls (`#[rustc_reservation_impl]`) are not used by trait
/// selection, and a partial `default impl` only provides items for the impls
/// specializing it.
pub(super) fn implements_trait(tcx: ty::TyCtxt<'_>, impl_did: DefId) -> bool {
    tcx.impl_polarity(impl_did) == ty::ImplPolarity::Positive
        && !tcx.defaultness(impl_did).is_default()
}

/// The definition of `trait_item` that Rust uses wherever the impl applies,
/// if it is final: the impl's own item, or one it inherits from an impl it
/// specializes or from the trait (an inherited item cannot be specialized
/// further, E0520). A `default` item may be overridden by a specializing
/// impl, possibly in a crate this one cannot see; like rustc, which only
/// resolves such an item once all types are known, it stays opaque.
///
/// Only for impls that implement the trait: `leaf_def` counts an item that
/// the starting impl does not mention as finalized by it, which does not
/// hold for a partial `default impl`.
pub(super) fn final_leaf_def(
    tcx: ty::TyCtxt<'_>,
    impl_did: DefId,
    trait_item: DefId,
) -> Option<specialization_graph::LeafDef> {
    debug_assert!(implements_trait(tcx, impl_did));
    let trait_did = tcx.impl_trait_ref(impl_did).skip_binder().def_id;
    specialization_graph::ancestors(tcx, trait_did, impl_did)
        .ok()?
        .leaf_def(tcx, trait_item)
        .filter(specialization_graph::LeafDef::is_final)
}

/// The Viper name of an impl. `idx` is only unique within a crate, so foreign
/// impls need the crate name for disambiguation.
fn impl_name<'vir>(vcx: &'vir vir::VirCtxt<'vir>, impl_did: DefId) -> &'vir str {
    let tcx = vcx.tcx();
    let all_impls = tcx.trait_impls_in_crate(impl_did.krate);
    let idx = all_impls.iter().position(|did| *did == impl_did).unwrap();
    let krate = tcx.crate_name(impl_did.krate);
    let trait_did = tcx.impl_trait_ref(impl_did).skip_binder().def_id;
    let trait_name = ViperIdent::from_def_id(vcx, trait_did);
    let implementing_ty = tcx
        .type_of(impl_did)
        .instantiate_identity()
        .skip_normalization();
    let implementing_ty = RustTyDecomposition::from_ty(implementing_ty, GParams::from(impl_did));
    let implementing_ty = implementing_ty.ty.name();
    vir::vir_format!(vcx, "{trait_name}_impl_{krate}_{implementing_ty}_{idx}")
}

/// The constructor keys gating the inclusion of an impl's content. An
/// `impl<T> MyTrait<ArgType> for MyType<T, OtherType>` is only relevant if
/// a) it is in the current crate (in which case it will be encoded by
/// [`TraitImplEnc`]) or b) the `TyConstructorEnc` has been called with
/// `MyType`, `OtherType` and `ArgType` (callers guard on the conjunction of
/// the returned keys). Gating on the trait args (not just the self type) is
/// fail-closed: any site that states a dependence on this impl does so by
/// applying `impl_fun` to type expressions for the full trait ref, and
/// building those requests exactly the constructors gated on here. Without
/// the arg gate, encoding one impl's condition constructs its arg types as a
/// side effect, unlocking further impls transitively (e.g. `Array` alone
/// would pull in every `core::arch` <-> `Simd` `From` impl).
pub(super) fn impl_unlock_keys<'vir>(impl_did: DefId) -> Vec<RustTy<'vir>> {
    vir::with_vcx(|vcx| {
        let tcx = vcx.tcx();
        let impl_trait_ref = tcx
            .impl_trait_ref(impl_did)
            .instantiate_identity()
            .skip_normalization();
        fn collect_ctor_keys<'vir>(ty: ty::Ty<'vir>, ctx: DefId, out: &mut Vec<RustTy<'vir>>) {
            let decomp = RustTyDecomposition::from_ty(ty, ctx);
            if decomp.ty.specifics.is_param() {
                return;
            }
            out.push(decomp.ty);
            for inner in decomp.args.args().iter().filter_map(|arg| arg.as_type()) {
                collect_ctor_keys(inner, ctx, out);
            }
        }
        let mut keys = Vec::new();
        for ty in impl_trait_ref.args.iter().filter_map(|arg| arg.as_type()) {
            collect_ctor_keys(ty, impl_did, &mut keys);
        }
        keys
    })
}

/// Encodes the assumable content of a single trait-impl item, each pulled in
/// individually and only when needed. For an associated fn: the axioms
/// bridging the trait's abstract pre/post functions (see `TraitFnEnc`) to
/// this item's concrete specification, instantiated at the impl's trait ref
/// (triggered per called function by `TraitFnEnc`). For an associated type:
/// the axiom resolving the trait's type function to the impl's concrete type
/// (triggered alongside the impl condition by `TraitEnc`).
///
/// An item that the impl inherits from an impl it specializes is encoded in
/// the context of the latter, additionally guarded by the inheriting impl
/// applying (see [`TraitImplEnc::applies_at`]).
pub struct TraitImplItemEnc;

impl TaskEncoder for TraitImplItemEnc {
    task_encoder::encoder_cache!(TraitImplItemEnc);
    const ENCODER_NAME: &'static str = "trait impl item encoder";

    /// The impl and its final definition of an item (see [`final_leaf_def`]):
    /// its own item, or one it inherits from an impl it specializes.
    type TaskDescription<'vir> = (DefId, DefId);
    type OutputFullLocal<'vir> = Domain<'vir>;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for domain in Self::all_outputs_local_no_errors(program) {
            program.add_domain(domain);
        }
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;

        vir::with_vcx(|vcx| {
            let tcx = vcx.tcx();

            let (applying_impl, impl_item_def_id) = *task_key;
            let impl_did = tcx.impl_of_assoc(impl_item_def_id).unwrap();
            let impl_item = tcx.associated_item(impl_item_def_id);
            let trait_item_def_id = impl_item.trait_item_def_id().unwrap();
            let impl_span = tcx.def_span(impl_item_def_id);
            let item_name = ViperIdent::from_def_id(vcx, impl_item_def_id);
            let impl_name = impl_name(vcx, applying_impl);

            let impl_context = GParams::from(impl_did);
            let impl_params = deps.require_dep::<GenericParamsEnc>(impl_context)?;
            let trait_ref = tcx
                .impl_trait_ref(impl_did)
                .instantiate_identity()
                .skip_normalization();

            let impl_item_context = GParams::from(impl_item_def_id);
            let impl_item_params = deps.require_dep::<GenericParamsEnc>(impl_item_context)?;

            // The ty and const decls of the trait items are the decls of the
            // item itself prefixed by the decls of the impl itself (so the
            // impl's where-clauses can guard the item's axioms).
            assert_eq!(
                impl_params.ty_decls(),
                &impl_item_params.ty_decls()[..impl_params.ty_decls().len()]
            );
            assert_eq!(
                impl_params.const_decls(),
                &impl_item_params.const_decls()[..impl_params.const_decls().len()]
            );

            // Combine the args to the trait in the impl and the identity args
            // for the item itself. That is, for:
            // ```
            // trait MyTrait<'a, A> { fn foo<'b, B>() {} }
            // impl<T> MyTrait<'static, (T, bool)> for MyType {
            //     fn foo<'b, B>() {}
            // }
            // ```
            // The `impl_item_context` of `foo` is `<T, 'b, B>` and
            // `impl_context` is `<T>`. We take the suffix of the impl item's
            // params that are specific to the item (i.e. not inherited from
            // the impl) and combine them with the trait args to get:
            // `<MyType, 'static, (T, bool), 'b, B>`. We use
            // `impl_item_context` rather than the trait item's context because
            // the parameter indices must match the `impl_item_context` used in
            // `GArgs::new` below.
            let trait_item_context = GParams::from(trait_item_def_id);
            let item_args = &impl_item_context.rust_params()[impl_context.rust_params().len()..];
            let args = trait_ref.args.iter().chain(item_args.iter().copied());
            let args = tcx.mk_args_from_iter(args);
            let impl_item_args = GArgs::new(impl_item_context, args);
            let args = deps.require_dep::<GArgsTyEnc>(impl_item_args)?;

            let trait_tys = args.get_ty();
            let trait_consts = args.get_const();

            // An inherited item describes only the inheriting impl's trait
            // refs: other impls specializing the defining one may override it.
            let inherited_guard = if applying_impl == impl_did {
                None
            } else {
                Some(TraitImplEnc::applies_at(
                    vcx,
                    deps,
                    applying_impl,
                    trait_tys,
                    trait_consts,
                )?)
            };
            let guard_inherited = |body: vir::ExprBool<'vir>| match inherited_guard {
                Some(applies) => vir::expr! { (applies) ==> (body) },
                None => body,
            };

            let mut axioms = Vec::new();

            match impl_item.kind {
                ty::AssocKind::Type { .. } => {
                    let trait_data = deps.require_ref::<TraitEnc>(trait_ref.def_id)?;
                    let assoc_type = trait_data.assoc_types[&trait_item_def_id];

                    // the type we want to resolve the type alias to
                    let assoc_type_expr = impl_item_params.ty_expr(
                        deps,
                        RustTyDecomposition::from_ty(
                            tcx.type_of(impl_item_def_id)
                                .instantiate_identity()
                                .skip_normalization(),
                            impl_item_context,
                        ),
                    )?;
                    // Guarded by the impl's where-clauses: a blanket impl and
                    // a more specific one that Rust keeps apart by them would
                    // otherwise resolve the same projection to two distinct
                    // types, which is false and makes everything provable.
                    let projection = assoc_type(trait_tys, trait_consts);
                    let equation = vcx.mk_eq_expr(projection, assoc_type_expr);
                    axioms.push(vcx.mk_domain_axiom(
                        vir_format_identifier!(vcx, "{impl_name}_assoc_type_{item_name}"),
                        TraitImplEnc::guarded_forall(
                            vcx,
                            deps,
                            impl_did,
                            impl_item_def_id,
                            &[],
                            projection.upcast_ty(),
                            guard_inherited(equation),
                        )?,
                    ));
                }
                ty::AssocKind::Fn { .. } => {
                    let assoc_fn = deps.require_ref::<TraitFnEnc>(trait_item_def_id)?;
                    let local_defs =
                        deps.require_dep::<MirLocalDefEnc>(MirLocalDefEncTask::Local {
                            def_id: impl_item_def_id,
                            all_locals: false,
                        })?;
                    let func_args = local_defs.local_decl_args().collect::<Vec<_>>();
                    let func_ret = local_defs.local_decl_ret();

                    let impl_item_is_pure = crate::encoders::is_function_pure(
                        impl_item_def_id,
                        GArgs::new(impl_item_context, impl_item_context.rust_params()),
                    );
                    let impl_item_has_body = is_function_with_body(vcx.tcx(), impl_item_def_id);

                    let impl_item_spec = deps.require_dep_spanned::<MirSpecEnc>(
                        (
                            impl_item_def_id,
                            impl_item_def_id,
                            MirSpecEncMode::PureWithoutResult,
                        ),
                        impl_span,
                    )?;
                    let pres = vcx.mk_conj(&impl_item_spec.pre_exprs().collect::<Vec<_>>());

                    let signature = RustSignature::new(trait_item_def_id);

                    // TODO: clean up: this kind of casting also happens in
                    //   `FunctionCallEncOutput::call_pure`.
                    let casted_args = func_args
                        .iter()
                        .zip(signature.inputs)
                        .map(|(arg, ty)| {
                            let normalized =
                                ty.decompose_compare_normalize(trait_item_context, impl_item_args);
                            let caster =
                                deps.require_dep::<GArgsCastEnc<Pure>>(normalized).unwrap();
                            caster.cast_to_callee_ctx(vcx.mk_local_ex(arg))
                        })
                        .collect::<Vec<_>>();
                    let casted_args_slice = vcx.alloc_slice(&casted_args);
                    let pre_func_call =
                        assoc_fn.pre_func.call()(casted_args_slice, trait_tys, trait_consts);
                    let arg_decls = func_args
                        .iter()
                        .map(|arg| arg.upcast_ty())
                        .collect::<Vec<vir::LocalDeclDyn>>();
                    axioms.push(vcx.mk_domain_axiom(
                        vir_format_identifier!(vcx, "{impl_name}_fn_pre_{item_name}"),
                        TraitImplEnc::guarded_forall(
                            vcx,
                            deps,
                            impl_did,
                            impl_item_def_id,
                            &arg_decls,
                            pre_func_call.upcast_ty(),
                            guard_inherited(vir::expr! { (pres) ==> (pre_func_call) }),
                        )?,
                    ));
                    let mut posts = impl_item_spec.post_exprs().collect::<Vec<_>>();
                    if impl_item_has_body && impl_item_is_pure {
                        let pure_func = deps.require_dep::<FunctionCallEnc>(
                            CallTaskDescription::new(
                                impl_item_def_id,
                                impl_item_context.rust_params(),
                                impl_item_def_id,
                            )
                            .resolve_trait_calls(false),
                        )?;
                        let raw_args = func_args
                            .iter()
                            .map(|arg| vcx.mk_local_ex(arg))
                            .collect::<Vec<_>>();
                        let pure_func_app = pure_func.call_pure(raw_args);
                        posts.push(vir::expr! {
                            ([func_ret]) == ([pure_func_app])
                        });
                    }
                    let posts = vcx.mk_conj(&posts);
                    let post_func_call = assoc_fn.post_func.call()(
                        {
                            let normalized = signature
                                .output
                                .decompose_compare_normalize(trait_item_context, impl_item_args);
                            let caster =
                                deps.require_dep::<GArgsCastEnc<Pure>>(normalized).unwrap();
                            caster.cast_to_callee_ctx(vcx.mk_local_ex(func_ret))
                        },
                        casted_args_slice,
                        trait_tys,
                        trait_consts,
                    );
                    let ret_and_arg_decls = std::iter::once(func_ret.upcast_ty())
                        .chain(arg_decls)
                        .collect::<Vec<_>>();
                    axioms.push(vcx.mk_domain_axiom(
                        vir_format_identifier!(vcx, "{impl_name}_fn_post_{item_name}"),
                        TraitImplEnc::guarded_forall(
                            vcx,
                            deps,
                            impl_did,
                            impl_item_def_id,
                            &ret_and_arg_decls,
                            post_func_call.upcast_ty(),
                            guard_inherited(vir::expr! { (post_func_call) ==> (posts) }),
                        )?,
                    ));
                }
                ty::AssocKind::Const { .. } => (),
            }

            let domain = vcx.mk_domain(
                vir_format_identifier!(vcx, "trait_{impl_name}_{item_name}"),
                &[],
                vcx.alloc_slice(&axioms),
                &[],
                None,
            );
            Ok((domain, ()))
        })
    }
}

/// Encodes, for an impl that inherits the default body of a pure trait fn,
/// the axiom that at the impl's trait refs the fn returns what the default
/// body does. The default body is not part of the trait's contract (impls
/// may override it with a different result, see `TraitFnEnc`), so it is
/// stated per inheriting impl, like the fn items of overriding impls (see
/// [`TraitImplItemEnc`]).
pub struct TraitImplDefaultFnEnc;

impl TaskEncoder for TraitImplDefaultFnEnc {
    task_encoder::encoder_cache!(TraitImplDefaultFnEnc);
    const ENCODER_NAME: &'static str = "trait impl default fn encoder";

    /// The impl and the trait fn whose default body it inherits.
    type TaskDescription<'vir> = (DefId, DefId);
    type OutputFullLocal<'vir> = Domain<'vir>;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;

        vir::with_vcx(|vcx| {
            let (impl_did, trait_fn) = *task_key;
            let impl_name = impl_name(vcx, impl_did);
            let item_name = ViperIdent::from_def_id(vcx, trait_fn);
            let trait_ref = vcx
                .tcx()
                .impl_trait_ref(impl_did)
                .instantiate_identity()
                .skip_normalization();

            // The trait fn's parameters: the trait's, then the fn's own.
            let item_params = GParams::from(trait_fn);
            let item_generics = deps.require_dep::<GenericParamsEnc>(item_params)?;
            let post_func = deps.require_ref::<TraitFnEnc>(trait_fn)?.post_func;
            let local_defs = deps.require_dep::<MirLocalDefEnc>(MirLocalDefEncTask::Local {
                def_id: trait_fn,
                all_locals: false,
            })?;
            let func_args = local_defs.local_decl_args().collect::<Vec<_>>();
            let func_arg_exprs = func_args
                .iter()
                .map(|arg| vcx.mk_local_ex(arg))
                .collect::<Vec<_>>();
            let func_ret = local_defs.local_decl_ret();

            let default_body = deps.require_dep::<FunctionCallEnc>(
                CallTaskDescription::new(trait_fn, item_params.rust_params(), trait_fn)
                    .resolve_trait_calls(false),
            )?;
            let default_body_app = default_body.call_pure(func_arg_exprs.clone());
            let post_func_call = post_func.call()(
                vcx.mk_local_ex(func_ret),
                vcx.alloc_slice(&func_arg_exprs),
                item_generics.ty_exprs(),
                item_generics.const_exprs(),
            );

            // Quantified over the impl's parameters (in a suffixed context, so
            // that they cannot capture the trait fn's) and the fn's own, and
            // triggered on the application at the impl's trait ref, so that
            // the axiom only fires for calls it can match. The trait's
            // parameters, which form the trait ref, are let-bound to it.
            let impl_ctx = GParams::from(impl_did).with_suffix("impl");
            let impl_args = deps.require_dep::<GArgsTyEnc>(GArgs::new(impl_ctx, trait_ref.args))?;
            let (impl_tys, impl_consts) = (impl_args.get_ty(), impl_args.get_const());
            let own_ty_decls = &item_generics.ty_decls()[impl_tys.len()..];
            let own_const_decls = &item_generics.const_decls()[impl_consts.len()..];

            let trigger_tys = impl_tys
                .iter()
                .chain(&item_generics.ty_exprs()[impl_tys.len()..])
                .copied()
                .collect::<Vec<_>>();
            let trigger_consts = impl_consts
                .iter()
                .chain(&item_generics.const_exprs()[impl_consts.len()..])
                .copied()
                .collect::<Vec<_>>();
            let trigger = post_func.call()(
                vcx.mk_local_ex(func_ret),
                vcx.alloc_slice(&func_arg_exprs),
                vcx.alloc_slice(&trigger_tys),
                vcx.alloc_slice(&trigger_consts),
            );

            let body = vir::expr! {
                (post_func_call) ==> (([func_ret]) == ([default_body_app]))
            };
            let trait_lets = std::iter::zip(item_generics.ty_decls(), impl_tys)
                .map(|(decl, &ty)| (decl.upcast_ty(), ty.upcast_ty()))
                .chain(
                    std::iter::zip(item_generics.const_decls(), impl_consts)
                        .map(|(decl, &const_)| (decl.upcast_ty(), const_.upcast_ty())),
                )
                .collect::<Vec<(vir::LocalDeclDyn, vir::ExprDyn)>>();
            let body = trait_lets
                .into_iter()
                .rfold(body, |acc, (decl, expr)| vcx.mk_let_expr(decl, expr, acc));

            let extra = std::iter::once(func_ret.upcast_ty())
                .chain(func_args.iter().map(|arg| arg.upcast_ty()))
                .chain(own_ty_decls.iter().map(|decl| decl.upcast_ty()))
                .chain(own_const_decls.iter().map(|decl| decl.upcast_ty()))
                .collect::<Vec<_>>();
            let axiom = TraitImplEnc::guarded_forall_in(
                vcx,
                deps,
                impl_did,
                impl_ctx,
                impl_ctx,
                &extra,
                trigger.upcast_ty(),
                body,
            )?;
            let domain = vcx.mk_domain(
                vir_format_identifier!(vcx, "trait_{impl_name}_default_{item_name}"),
                &[],
                vcx.alloc_slice(&[vcx.mk_domain_axiom(
                    vir_format_identifier!(vcx, "{impl_name}_fn_default_{item_name}"),
                    axiom,
                )]),
                &[],
                None,
            );
            Ok((domain, ()))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for domain in Self::all_outputs_local_no_errors(program) {
            program.add_domain(domain);
        }
    }
}
