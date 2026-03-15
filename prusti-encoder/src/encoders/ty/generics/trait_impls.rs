use std::collections::VecDeque;

use prusti_interface::{PrustiError, specs::specifications::SpecQuery};
use prusti_rustc_interface::{
    index::bit_set::DenseBitSet,
    middle::{mir, ty},
    span::def_id::DefId,
};
use task_encoder::{EncodeFullError, EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{CastType, Domain, Method, MethodIdn, vir_format_identifier};

use crate::{
    encoders::{
        ConstEnc, FunctionCallEnc, MirLocalDefEnc, MirLocalDefEncTask, MirSpecEnc, Pure,
        r#const::ConstEncTask,
        mir_fn::{CallTaskDescription, RustSignature},
        pure::spec::MirSpecEncMode,
        ty::{
            RustTyDecomposition,
            generics::{
                GArgs, GArgsCastEnc, GArgsTyEnc, GParams, GenericParamsEnc, r#trait::TraitEnc,
                trait_fn::TraitFnEnc,
            },
            lifted::TyConstructorEnc,
        },
    },
    trait_support::is_function_with_body,
};

pub struct TraitImplEnc;

#[derive(Debug, Clone)]
pub struct TraitImplEncOutput<'vir> {
    pub impl_condition: vir::ExprBool<'vir>,
}

impl TaskEncoder for TraitImplEnc {
    task_encoder::encoder_cache!(TraitImplEnc);

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for (dom, methods) in Self::all_outputs_local_no_errors() {
            program.add_domain(dom);
            for method in methods {
                program.add_method(method);
            }
        }
    }

    type TaskDescription<'vir> = DefId;
    type OutputFullDependency<'vir> = TraitImplEncOutput<'vir>;
    type OutputFullLocal<'vir> = (Domain<'vir>, Vec<Method<'vir>>);

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
            let impl_params = deps.require_dep::<GenericParamsEnc>(impl_context)?;

            let trait_ref = tcx.impl_trait_ref(task_key).unwrap().instantiate_identity();
            let trait_did = trait_ref.def_id;
            let trait_data = deps.require_ref::<TraitEnc>(trait_did)?;
            let trait_name = trait_data.trait_name;

            let mut axioms = Vec::new();
            let mut methods = Vec::new();

            let implementing_ty = tcx.type_of(task_key).instantiate_identity();
            let implementing_ty = RustTyDecomposition::from_ty(implementing_ty, impl_context);
            let implementing_ty = implementing_ty.ty.name();

            let impl_ty_decls = impl_params.ty_decls();
            let impl_const_decls = impl_params.const_decls();

            for impl_item in tcx.associated_items(task_key).in_definition_order() {
                let trait_item_def_id = impl_item.trait_item_def_id.unwrap();
                let impl_item_def_id = impl_item.def_id;
                let impl_span = vcx.tcx().def_span(impl_item_def_id);
                let item_name = tcx.item_name(impl_item_def_id);

                // construct arguments for assoc_item function
                // parameters of the trait are substituted
                // by the arguments used in the impl
                // parameters of the associated type are kept

                // parameters of assoc item include already substituted arguments
                let impl_item_context = GParams::from(impl_item_def_id);
                let impl_item_params = deps.require_dep::<GenericParamsEnc>(impl_item_context)?;

                // The ty and const decls of the trait items are the decls of
                // the item itself prefixed by the decls of the impl itself.
                assert_eq!(
                    impl_ty_decls,
                    &impl_item_params.ty_decls()[..impl_ty_decls.len()]
                );
                let trait_ty_decls = impl_item_params.ty_decls();
                assert_eq!(
                    impl_const_decls,
                    &impl_item_params.const_decls()[..impl_const_decls.len()]
                );
                let trait_const_decls = impl_item_params.const_decls();

                // Combine the args to the trait in the impl and the identity
                // args for the item itself. That is, for:
                // ```
                // trait MyTrait<'a, A> { fn foo<'b, B>() {} }
                // impl<T> MyTrait<'static, (T, bool)> for MyType {
                //     fn foo<'b, B>() {}
                // }
                // ```
                // The `trait_item_context` of `foo` is `<Self, 'a, A, 'b, B>`
                // and we combine the identity suffix of this with the args to
                // the trait to get: `<MyType, 'static, (T, bool), 'b, B>`.
                let trait_item_context = GParams::from(trait_item_def_id);
                let item_args = &trait_item_context.rust_params()[trait_ref.args.len()..];
                let args = trait_ref.args.iter().chain(item_args.iter().copied());
                let args = tcx.mk_args_from_iter(args);
                let impl_item_args = GArgs::new(impl_item_context, args);
                let args = deps.require_dep::<GArgsTyEnc>(impl_item_args)?;

                let trait_tys = args.get_ty();
                let trait_consts = args.get_const();

                match impl_item.kind {
                    ty::AssocKind::Type { .. } => {
                        let assoc_type = trait_data.assoc_types[&trait_item_def_id];

                        // the type we want to resolve the type alias to
                        let assoc_type_expr = impl_item_params.ty_expr(
                            deps,
                            RustTyDecomposition::from_ty(
                                tcx.type_of(impl_item_def_id).instantiate_identity(),
                                impl_item_context,
                            ),
                        )?;
                        axioms.push(vcx.mk_domain_axiom(
                            vir_format_identifier!(
                                vcx,
                                "{trait_name}_impl_{implementing_ty}_{idx}_assoc_type_{item_name}"
                            ),
                            vir::expr! {forall ..[trait_ty_decls], ..[trait_const_decls] ::
                                {[assoc_type(trait_tys, trait_consts)]}
                            ([assoc_type(trait_tys, trait_consts)]) == (assoc_type_expr)},
                        ));
                    }
                    ty::AssocKind::Fn { .. } => {
                        let assoc_fn = deps.require_ref::<TraitFnEnc>(trait_item_def_id)?;
                        let local_defs =
                            deps.require_dep::<MirLocalDefEnc>(MirLocalDefEncTask::Local {
                                def_id: impl_item_def_id,
                                all_locals: false,
                            })?;
                        let arg_count = local_defs.arg_count + 1;
                        let func_args = local_defs.local_decl_args().collect::<Vec<_>>();
                        let ref_args = vcx.alloc_slice(&vec![vir::TYPE_REF; arg_count]);
                        let func_ret = local_defs.local_decl_ret();

                        let trait_item_is_pure = crate::encoders::with_proc_spec(
                            SpecQuery::GetProcKind(
                                trait_item_def_id,
                                trait_item_context.rust_params(),
                            ),
                            |spec| spec.kind.is_pure().unwrap_or_default(),
                        )
                        .unwrap_or_default();
                        let impl_item_is_pure = crate::encoders::with_proc_spec(
                            SpecQuery::GetProcKind(
                                impl_item_def_id,
                                impl_item_context.rust_params(),
                            ),
                            |spec| spec.kind.is_pure().unwrap_or_default(),
                        )
                        .unwrap_or_default();

                        let trait_item_has_body =
                            is_function_with_body(vcx.tcx(), trait_item_def_id);
                        let impl_item_has_body = is_function_with_body(vcx.tcx(), impl_item_def_id);

                        let impl_item_spec = deps.require_dep_spanned::<MirSpecEnc>(
                            (
                                impl_item_def_id,
                                impl_item_def_id,
                                MirSpecEncMode::PureWithoutResult,
                            ),
                            impl_span,
                        )?;
                        let pres = vcx.mk_conj(&impl_item_spec.pres);

                        let signature = RustSignature::new(trait_item_def_id);

                        let pre_func_args = func_args
                            .iter()
                            .zip(signature.inputs)
                            .map(|(arg, ty)| {
                                let normalized = ty.decompose_compare_normalize(
                                    trait_item_context,
                                    impl_item_args,
                                );
                                let caster =
                                    deps.require_dep::<GArgsCastEnc<Pure>>(normalized).unwrap();
                                caster.cast_to_callee_ctx(vcx.mk_local_ex(arg))
                            })
                            .collect::<Vec<_>>();
                        let pre_func_call = assoc_fn.pre_func.call()(
                            vcx.alloc_slice(&pre_func_args),
                            trait_tys,
                            trait_consts,
                        );
                        axioms.push(vcx.mk_domain_axiom(
                            vir_format_identifier!(
                                vcx,
                                "{trait_name}_impl_{implementing_ty}_{idx}_fn_pre_{item_name}",
                            ),
                            vir::expr! {
                                forall ..[func_args], ..[trait_ty_decls] :: {[pre_func_call]}
                                    (pres) ==> (pre_func_call)
                            },
                        ));
                        let mut posts = impl_item_spec.posts;
                        if impl_item_has_body && impl_item_is_pure {
                            let pure_func = deps.require_dep::<FunctionCallEnc>(
                                CallTaskDescription::new(
                                    impl_item_def_id,
                                    impl_item_context.rust_params(),
                                    impl_item_def_id,
                                )
                                .resolve_trait_calls(false),
                            )?;
                            let pure_func_app = pure_func.call_pure(pre_func_args);
                            posts.push(vir::expr! {
                                ([func_ret]) == ([pure_func_app])
                            });
                        }
                        let posts = vcx.mk_conj(&posts);
                        // TODO: clean up: this kind of casting also happens in
                        //   `FunctionCallEncOutput::call_pure`.
                        let post_func_call = assoc_fn.post_func.call()(
                            {
                                let normalized = signature.output.decompose_compare_normalize(
                                    trait_item_context,
                                    impl_item_args,
                                );
                                let caster =
                                    deps.require_dep::<GArgsCastEnc<Pure>>(normalized).unwrap();
                                caster.cast_to_callee_ctx(vcx.mk_local_ex(func_ret))
                            },
                            vcx.alloc_slice(
                                &func_args
                                    .iter()
                                    .zip(signature.inputs)
                                    .map(|(arg, ty)| {
                                        let normalized = ty.decompose_compare_normalize(
                                            trait_item_context,
                                            impl_item_args,
                                        );
                                        let caster = deps
                                            .require_dep::<GArgsCastEnc<Pure>>(normalized)
                                            .unwrap();
                                        caster.cast_to_callee_ctx(vcx.mk_local_ex(arg))
                                    })
                                    .collect::<Vec<_>>(),
                            ),
                            trait_tys,
                            trait_consts,
                        );
                        axioms.push(vcx.mk_domain_axiom(
                            vir_format_identifier!(
                                vcx,
                                "{trait_name}_impl_{implementing_ty}_{idx}_fn_post_{item_name}",
                            ),
                            vir::expr! {
                                forall [func_ret], ..[func_args], ..[trait_ty_decls] :: {[post_func_call]}
                                    (post_func_call) ==> (posts)
                            },
                        ));

                        let trait_item_spec = deps.require_dep_spanned::<MirSpecEnc>(
                            (trait_item_def_id, impl_item_def_id, MirSpecEncMode::Impure),
                            impl_span,
                        )?;
                        let impl_item_spec = deps.require_dep_spanned::<MirSpecEnc>(
                            (impl_item_def_id, impl_item_def_id, MirSpecEncMode::Impure),
                            impl_span,
                        )?;

                        let mut pre_weaken_pres = Vec::new();
                        let mut args = Vec::with_capacity(arg_count + impl_item_context.count());
                        for arg_idx in (0..arg_count).map(mir::Local::from) {
                            let name_p = local_defs[arg_idx].local.name;
                            args.push(vir::vir_local_decl! { vcx; [name_p] : Ref });
                            if arg_idx != mir::RETURN_PLACE {
                                pre_weaken_pres.push(local_defs[arg_idx].impure_pred);
                            }
                        }
                        // TODO: wands

                        pre_weaken_pres.extend(trait_item_spec.pres.clone());

                        methods.push(vcx.mk_method(
                            MethodIdn::<(vir::ManyRef, vir::ManyTyVal, vir::ManyCSnap)>::new(
                                vir_format_identifier!(vcx, "trait_{trait_name}_impl_{implementing_ty}_{idx}_fn_pre_weaken_{item_name}"),
                                (ref_args, impl_item_params.ty_args(), impl_item_params.const_args()),
                            ),
                            (args.as_slice(), trait_ty_decls, trait_const_decls),
                            &[],
                            vcx.alloc_slice(&pre_weaken_pres),
                            &[],
                            Some(vcx.alloc_slice(&[
                                vcx.mk_cfg_block(
                                    &vir::CfgBlockLabelData::Start,
                                    &[],
                                    vcx.alloc_slice(&impl_item_spec.pres.iter()
                                        .map(|pre| vcx.with_span(impl_span, |vcx| {
                                            // TODO: make span point precisely to the precondition we cannot show
                                            vcx.handle_error("exhale.failed:assertion.false", move |_| {
                                                Some(vec![PrustiError::verification("trait implementation is not a behavioral subtype (precondition is not weakened)", impl_span.into())])
                                            });
                                            vcx.mk_exhale_stmt(pre)
                                        }))
                                        .collect::<Vec<_>>()),
                                    vcx.alloc(vir::TerminatorStmtData::Exit),
                                )
                            ])),
                        ));

                        let mut post_strengthen_pres = Vec::new();
                        let mut args = Vec::with_capacity(arg_count + impl_item_context.count());
                        for arg_idx in (0..arg_count).map(mir::Local::from) {
                            let name_p = local_defs[arg_idx].local.name;
                            args.push(vir::vir_local_decl! { vcx; [name_p] : Ref });
                            if arg_idx != mir::RETURN_PLACE {
                                post_strengthen_pres.push(local_defs[arg_idx].impure_pred);
                            }
                        }
                        // TODO: wands

                        post_strengthen_pres.extend(trait_item_spec.pres);

                        // exceptionally, we also put the allocated result in the precondition
                        post_strengthen_pres.push(local_defs[mir::RETURN_PLACE].impure_pred);

                        // here we inhale the impl postconditions, since they
                        // can contain "old" variables
                        let mut stmts = Vec::new();
                        for post in &impl_item_spec.posts {
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
                        for post in trait_item_spec.posts {
                            vcx.with_span(impl_span, |vcx| {
                                // TODO: make span point precisely to the postcondition we cannot show
                                vcx.handle_error("exhale.failed:assertion.false", move |_| {
                                    Some(vec![PrustiError::verification("trait implementation is not a behavioral subtype (postcondition is not strengthened)", impl_span.into())])
                                });
                                stmts.push(vcx.mk_exhale_stmt(post));
                            });
                        }
                        if trait_item_has_body && trait_item_is_pure {
                            let pure_func = deps.require_dep::<FunctionCallEnc>(
                                CallTaskDescription::new(
                                    impl_item_def_id,
                                    trait_ref.args,
                                    trait_item_def_id,
                                )
                                .resolve_trait_calls(false),
                            )?;
                            let pure_func_app = pure_func.call_pure(
                                local_defs
                                    .args()
                                    .map(|arg| arg.impure_snap)
                                    .collect::<Vec<_>>(),
                            );
                            vcx.with_span(impl_span, |vcx| {
                                vcx.handle_error("exhale.failed:assertion.false", move |_| {
                                    Some(vec![PrustiError::verification("trait implementation is not a behavioral subtype (body is not strengthened)", impl_span.into())])
                                });
                                stmts.push(vcx.mk_exhale_stmt(vir::expr! {
                                    ([local_defs[mir::RETURN_PLACE].impure_snap]) == ([pure_func_app])
                                }));
                            });
                        }

                        methods.push(vcx.mk_method(
                            MethodIdn::<(vir::ManyRef, vir::ManyTyVal, vir::ManyCSnap)>::new(
                                vir_format_identifier!(vcx, "trait_{trait_name}_impl_{implementing_ty}_{idx}_fn_post_strengthen_{item_name}"),
                                (ref_args, impl_item_params.ty_args(), impl_item_params.const_args()),
                            ),
                            (args.as_slice(), trait_ty_decls, trait_const_decls),
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
                    ty::AssocKind::Const { .. } => (),
                }
            }

            let trait_ref = tcx.impl_trait_ref(task_key).unwrap().instantiate_identity();
            let impl_condition =
                Self::impl_block_check(vcx, deps, GParams::from(*task_key), trait_ref)?;

            Ok((
                (
                    vcx.mk_domain(
                        vir_format_identifier!(
                            vcx,
                            "trait_{trait_name}_impl_{implementing_ty}_{idx}"
                        ),
                        &[],
                        vcx.alloc_slice(&axioms),
                        &[],
                        None,
                    ),
                    methods,
                ),
                TraitImplEncOutput { impl_condition },
            ))
        })
    }
}
impl TraitImplEnc {
    fn bitset_from(iter: impl IntoIterator<Item = u32>, size: usize) -> DenseBitSet<u32> {
        iter.into_iter()
            .fold(DenseBitSet::new_empty(size), |mut acc, idx| {
                acc.insert(idx);
                acc
            })
    }
    fn projection_deps<'vir>(
        projection: ty::ProjectionPredicate<'vir>,
        generics_count: usize,
    ) -> (DenseBitSet<u32>, DenseBitSet<u32>) {
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
            .flat_map(|arg| arg.walk().filter_map(generic_idx));

        let produced = projection.term.walk().filter_map(generic_idx);

        (
            Self::bitset_from(required, generics_count),
            Self::bitset_from(produced, generics_count),
        )
    }

    fn order_projections<'vir>(
        known_generics: impl IntoIterator<Item = u32>,
        projections: impl IntoIterator<Item = ty::ProjectionPredicate<'vir>>,
        generics_count: usize,
    ) -> Vec<ty::ProjectionPredicate<'vir>> {
        let mut known_generics = Self::bitset_from(known_generics, generics_count);

        let mut worklist: VecDeque<_> = projections
            .into_iter()
            .map(|p| (p, Self::projection_deps(p, generics_count)))
            .collect();

        let mut ordered = Vec::new();

        while let Some((proj, (required, produced))) = worklist.pop_front() {
            if known_generics.superset(&required) {
                known_generics.union(&produced);
                ordered.push(proj);
            } else {
                worklist.push_back((proj, (required, produced)));
            }
        }

        ordered
    }

    fn discover_bind_points<'vir, E: TaskEncoder + 'vir + ?Sized>(
        deps: &mut TaskEncoderDependencies<'vir, E>,
        generic_map: &mut GenericsMap<'vir>,
        ctx: GParams<'vir>,
        expr: vir::ExprTyVal<'vir>,
        ty: ty::Ty<'vir>,
    ) -> Result<(), EncodeFullError<'vir, E>> {
        if let ty::TyKind::Param(p) = ty.kind() {
            generic_map.try_insert(p.index, expr.upcast_ty());
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
                generic_map.try_insert(p.index, inner_expr.upcast_ty());
            }
        }
        Ok(())
    }

    pub(super) fn impl_block_check<'vir, E: TaskEncoder + 'vir + ?Sized>(
        vcx: &'vir vir::VirCtxt<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, E>,
        impl_ctx: GParams<'vir>,
        trait_ref: ty::TraitRef<'vir>,
    ) -> Result<vir::ExprBool<'vir>, EncodeFullError<'vir, E>> {
        let tcx = vcx.tcx();
        let impl_ctx = impl_ctx.with_suffix("impl");
        let impl_params = deps.require_dep::<GenericParamsEnc>(impl_ctx)?;

        let trait_ctx = TraitEnc::trait_params(trait_ref.def_id);
        let trait_params = deps.require_dep::<GenericParamsEnc>(trait_ctx)?;

        let args = deps.require_dep::<GArgsTyEnc>(GArgs::new(impl_ctx, trait_ref.args))?;

        let generics_count = impl_ctx.rust_params().len();

        // Collect the bindings for the generics of this impl block
        let mut generics_map = GenericsMap::new(generics_count);

        // Walk the trait type generic arguments
        let impl_rust_tys = trait_ref.args.iter().filter_map(|arg| arg.as_type());
        for (ty_arg, rust_ty) in std::iter::zip(trait_params.ty_exprs(), impl_rust_tys) {
            Self::discover_bind_points(deps, &mut generics_map, trait_ctx, ty_arg, rust_ty)?;
        }

        // Walk the trait const generic arguments
        let impl_rust_consts = trait_ref.args.iter().filter_map(|arg| arg.as_const());
        for (const_arg, rust_const) in std::iter::zip(trait_params.const_exprs(), impl_rust_consts)
        {
            if let ty::ConstKind::Param(p) = rust_const.kind() {
                generics_map.try_insert(p.index, const_arg.upcast_ty());
            }
        }

        let mut checks = Vec::new();
        // Collect checks for the generics of the trait and their corresponding arguments in the impl
        for (trait_ty_param, ty_args) in std::iter::zip(trait_params.ty_exprs(), args.get_ty()) {
            checks.push(vcx.mk_eq_expr(trait_ty_param, ty_args));
        }
        for (trait_const_param, const_args) in
            std::iter::zip(trait_params.const_exprs(), args.get_const())
        {
            checks.push(vcx.mk_eq_expr(trait_const_param, const_args));
        }

        let caller_bounds = impl_ctx.typing_env().param_env.caller_bounds();

        // Collect checks for the trait bounds
        let trait_preds = caller_bounds
            .iter()
            .filter_map(ty::Clause::as_trait_clause)
            .map(ty::Binder::skip_binder);
        for trait_pred in trait_preds {
            let trait_did = trait_pred.def_id();
            let trait_ = deps.require_ref::<TraitEnc>(trait_did)?;
            let gargs = GArgs::new(impl_ctx, trait_pred.trait_ref.args);
            let gargs = deps.require_dep::<GArgsTyEnc>(gargs)?;

            let impl_check = (trait_.impl_fun)(gargs.get_ty(), gargs.get_const());
            checks.push(impl_check);
        }

        // Collect checks for the projection predicates. These have to be processed in a way such that
        // any bindpoints they introduce are introduced with the let-bindings in the correct order.
        let proj_preds = caller_bounds
            .iter()
            .filter_map(ty::Clause::as_projection_clause)
            .map(ty::Binder::skip_binder);
        let proj_preds = Self::order_projections(generics_map.keys(), proj_preds, generics_count);
        for proj_pred in proj_preds {
            let trait_did = proj_pred.trait_def_id(tcx);
            let trait_ = deps.require_ref::<TraitEnc>(trait_did)?;
            let gargs = GArgs::new(impl_ctx, proj_pred.projection_term.args);
            let gargs = deps.require_dep::<GArgsTyEnc>(gargs)?;

            let (projection, expr): (vir::ExprDyn, vir::ExprDyn) = match proj_pred.term.kind() {
                ty::TermKind::Ty(ty) => {
                    let projection =
                        trait_.assoc_types[&proj_pred.def_id()](gargs.get_ty(), gargs.get_const());
                    let decomp = RustTyDecomposition::from_ty(ty, impl_ctx);
                    let ty_expr = impl_params.ty_expr(deps, decomp)?;
                    Self::discover_bind_points(deps, &mut generics_map, impl_ctx, projection, ty)?;
                    (projection.upcast_ty(), ty_expr.upcast_ty())
                }
                ty::TermKind::Const(const_) => {
                    let projection =
                        trait_.assoc_consts[&proj_pred.def_id()](gargs.get_ty(), gargs.get_const());
                    let ty = tcx.type_of(proj_pred.def_id()).instantiate_identity();
                    let const_task = ConstEncTask::Ty {
                        const_,
                        ty,
                        context: impl_ctx,
                    };
                    let const_expr = deps.require_dep::<ConstEnc>(const_task)?;
                    if let ty::ConstKind::Param(p) = const_.kind() {
                        generics_map.try_insert(p.index, const_expr.upcast_ty());
                    }
                    (projection.upcast_ty(), const_expr.upcast_ty())
                }
            };

            let projection_check = vcx.mk_eq_expr(projection, expr);
            checks.push(projection_check);
        }

        let checks = vcx.mk_conj(&checks);

        Ok(generics_map
            .insertion_ordered()
            .rfold(checks, |acc, (idx, expr)| {
                let idx = impl_params.map_idx(idx);
                let decl = match idx {
                    Result::Ok(idx) => impl_params.ty_decls()[idx].upcast_ty(),
                    Result::Err(idx) => impl_params.const_decls()[idx].upcast_ty(),
                };
                vcx.mk_let_expr(decl, expr, acc)
            }))
    }
}

/// Collects bindings for generics in the order they are discovered.
#[derive(Clone, Debug)]
struct GenericsMap<'vir> {
    order: usize,
    map: Vec<Option<(usize, vir::ExprDyn<'vir>)>>,
}

impl<'vir> GenericsMap<'vir> {
    fn new(size: usize) -> Self {
        GenericsMap {
            order: 0,
            map: vec![None; size],
        }
    }

    /// Insert the given expression as the binding for the `idx`-th generic, while recording the
    /// insertion order. Returns `false` if the generic already has a binding, and `true`
    /// otherwise.
    fn try_insert(&mut self, idx: u32, expr: vir::ExprDyn<'vir>) -> bool {
        let idx = idx as usize;
        if self.map[idx].is_some() {
            return false;
        }
        self.map[idx] = Some((self.order, expr));
        self.order += 1;
        true
    }

    /// Collect the bindings in their insertion order.
    fn insertion_ordered(&self) -> impl DoubleEndedIterator<Item = (u32, vir::ExprDyn<'vir>)> {
        let mut ordered = self
            .map
            .iter()
            .enumerate()
            .filter_map(|(idx, opt)| opt.map(|(order, expr)| (order, (idx as u32, expr))))
            .collect::<Vec<_>>();
        ordered.sort_by_key(|(order, _)| *order);
        ordered.into_iter().map(|(_, (idx, expr))| (idx, expr))
    }

    /// Already present generics.
    fn keys(&self) -> impl Iterator<Item = u32> {
        self.map
            .iter()
            .enumerate()
            .filter_map(|(idx, opt)| opt.as_ref().map(|_| idx as u32))
    }
}
