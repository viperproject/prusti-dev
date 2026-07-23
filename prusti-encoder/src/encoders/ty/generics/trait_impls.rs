use prusti_interface::PrustiError;
use prusti_rustc_interface::{
    data_structures::fx::{FxIndexMap, FxIndexSet},
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

            let trait_ref = tcx.impl_trait_ref(task_key).unwrap().instantiate_identity();
            let trait_did = trait_ref.def_id;
            let trait_data = deps.require_ref::<TraitEnc>(trait_did)?;
            let trait_name = trait_data.trait_name;

            let mut methods = Vec::new();

            let implementing_ty = tcx.type_of(task_key).instantiate_identity();
            let implementing_ty = RustTyDecomposition::from_ty(implementing_ty, impl_context);
            let implementing_ty = implementing_ty.ty.name();

            for impl_item in tcx.associated_items(task_key).in_definition_order() {
                let ty::AssocKind::Fn { .. } = impl_item.kind else {
                    continue;
                };
                let trait_item_def_id = impl_item.trait_item_def_id.unwrap();
                let impl_item_def_id = impl_item.def_id;
                let impl_span = vcx.tcx().def_span(impl_item_def_id);
                let item_name = tcx.item_name(impl_item_def_id);

                let impl_item_context = GParams::from(impl_item_def_id);
                let impl_item_params = deps.require_dep::<GenericParamsEnc>(impl_item_context)?;
                let trait_ty_decls = impl_item_params.ty_decls();
                let trait_const_decls = impl_item_params.const_decls();
                let trait_item_context = GParams::from(trait_item_def_id);

                let local_defs = deps.require_dep::<MirLocalDefEnc>(MirLocalDefEncTask::Local {
                    def_id: impl_item_def_id,
                    all_locals: false,
                })?;
                let arg_count = local_defs.arg_count + 1;
                let ref_args = vcx.alloc_slice(&vec![vir::TYPE_REF; arg_count]);

                let trait_item_is_pure = crate::encoders::is_function_pure(
                    trait_item_def_id,
                    GArgs::new(trait_item_context, trait_item_context.rust_params()),
                );
                let impl_item_is_pure = crate::encoders::is_function_pure(
                    impl_item_def_id,
                    GArgs::new(impl_item_context, impl_item_context.rust_params()),
                );

                let trait_item_has_body = is_function_with_body(vcx.tcx(), trait_item_def_id);
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
                pre_weaken_pres.extend(trait_item_spec.pres.clone());

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

                let mut post_strengthen_pres = impure_arg_preds;
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

            // Make the impl visible to the trait's `impl_fun` disjunction, and
            // resolve its associated types and specification.
            deps.require_dep::<TraitImplConditionEnc>(*task_key)?;

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

/// Encodes the assumable content of a trait impl: its applicability condition
/// (the check that a given instantiation of the trait's parameters matches
/// this impl and that the impl's where-clauses hold) and its axioms (the
/// resolution of its associated types and the bridging of the trait's
/// abstract pre/post functions to the impl items' concrete specifications -
/// how a call through the trait resolves to a concrete contract once the
/// `Self` type is known). Unlike [`TraitImplEnc`], this is safe to run on
/// foreign impls: it produces no proof obligations, so foreign impls are
/// assumed - not re-verified - to be behavioural subtypes.
pub struct TraitImplConditionEnc;

impl TaskEncoder for TraitImplConditionEnc {
    task_encoder::encoder_cache!(TraitImplConditionEnc);
    const ENCODER_NAME: &'static str = "trait impl condition encoder";

    type TaskDescription<'vir> = DefId;
    /// The implemented trait, the condition, and the axioms. This encoder does
    /// not have its own `emit_outputs`, instead the output is consumed (any
    /// errors form here are reported there) by `TraitEnc::emit_outputs`, which
    /// disjoins the conditions into each trait's `impl_fun` and emits the domains.
    type OutputFullLocal<'vir> = (DefId, vir::ExprBool<'vir>, Domain<'vir>);

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
            let krate = tcx.crate_name(task_key.krate);

            let impl_context = GParams::from(*task_key);
            let impl_params = deps.require_dep::<GenericParamsEnc>(impl_context)?;

            let trait_ref = tcx.impl_trait_ref(task_key).unwrap().instantiate_identity();
            let trait_did = trait_ref.def_id;
            let condition = TraitImplEnc::impl_block_check(vcx, deps, impl_context, trait_ref)?;
            let trait_data = deps.require_ref::<TraitEnc>(trait_did)?;
            let trait_name = trait_data.trait_name;

            let mut axioms = Vec::new();

            let implementing_ty = tcx.type_of(task_key).instantiate_identity();
            let implementing_ty = RustTyDecomposition::from_ty(implementing_ty, impl_context);
            let implementing_ty = implementing_ty.ty.name();
            // `idx` is only unique within a crate, so foreign impls need the
            // crate name for disambiguation.
            let impl_name =
                vir::vir_format!(vcx, "{trait_name}_impl_{krate}_{implementing_ty}_{idx}");

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
                // The `impl_item_context` of `foo` is `<T, 'b, B>` and
                // `impl_context` is `<T>`. We take the suffix of the impl
                // item's params that are specific to the method (i.e. not
                // inherited from the impl) and combine them with the trait
                // args to get: `<MyType, 'static, (T, bool), 'b, B>`.
                // We use `impl_item_context` rather than the trait item's
                // context because the parameter indices must match the
                // `impl_item_context` used in `GArgs::new` below.
                let trait_item_context = GParams::from(trait_item_def_id);
                let item_args =
                    &impl_item_context.rust_params()[impl_context.rust_params().len()..];
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
                            vir_format_identifier!(vcx, "{impl_name}_assoc_type_{item_name}"),
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
                        let pres = vcx.mk_conj(&impl_item_spec.pres);

                        let signature = RustSignature::new(trait_item_def_id);

                        // TODO: clean up: this kind of casting also happens in
                        //   `FunctionCallEncOutput::call_pure`.
                        let casted_args = func_args
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
                        let casted_args_slice = vcx.alloc_slice(&casted_args);
                        let pre_func_call =
                            assoc_fn.pre_func.call()(casted_args_slice, trait_tys, trait_consts);
                        axioms.push(vcx.mk_domain_axiom(
                            vir_format_identifier!(vcx, "{impl_name}_fn_pre_{item_name}"),
                            vir::expr! {
                                forall ..[func_args], ..[trait_ty_decls], ..[trait_const_decls] :: {[pre_func_call]}
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
                            let pure_func_app = pure_func.call_pure(casted_args);
                            posts.push(vir::expr! {
                                ([func_ret]) == ([pure_func_app])
                            });
                        }
                        let posts = vcx.mk_conj(&posts);
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
                            casted_args_slice,
                            trait_tys,
                            trait_consts,
                        );
                        axioms.push(vcx.mk_domain_axiom(
                            vir_format_identifier!(vcx, "{impl_name}_fn_post_{item_name}"),
                            vir::expr! {
                                forall [func_ret], ..[func_args], ..[trait_ty_decls], ..[trait_const_decls] :: {[post_func_call]}
                                    (post_func_call) ==> (posts)
                            },
                        ));
                    }
                    ty::AssocKind::Const { .. } => (),
                }
            }

            let axioms = vcx.mk_domain(
                vir_format_identifier!(vcx, "trait_{impl_name}"),
                &[],
                vcx.alloc_slice(&axioms),
                &[],
                None,
            );
            Ok(((trait_did, condition, axioms), ()))
        })
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

        // Collect the bindings for the generics of this impl block
        let mut generics_map = FxIndexMap::default();

        // Walk the trait type generic arguments. The types come from the
        // impl's side of the `trait_ref`, so they are decomposed in the
        // impl's context.
        let impl_rust_tys = trait_ref.args.iter().filter_map(|arg| arg.as_type());
        for (ty_arg, rust_ty) in std::iter::zip(trait_params.ty_exprs(), impl_rust_tys) {
            Self::discover_bind_points(deps, &mut generics_map, impl_ctx, ty_arg, rust_ty)?;
        }

        // Walk the trait const generic arguments
        let impl_rust_consts = trait_ref.args.iter().filter_map(|arg| arg.as_const());
        for (const_arg, rust_const) in std::iter::zip(trait_params.const_exprs(), impl_rust_consts)
        {
            if let ty::ConstKind::Param(p) = rust_const.kind() {
                generics_map.entry(p.index).or_insert(const_arg.upcast_ty());
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
        let proj_preds = Self::order_projections(generics_map.keys().copied(), proj_preds);
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
                    let ty_expr = impl_params.ty_expr(deps, decomp);
                    Self::discover_bind_points(deps, &mut generics_map, impl_ctx, projection, ty)?;
                    (projection.upcast_ty(), ty_expr?.upcast_ty())
                }
                ty::TermKind::Const(const_) => {
                    let projection =
                        trait_.assoc_consts[&proj_pred.def_id()](gargs.get_ty(), gargs.get_const());
                    let ty = tcx.type_of(proj_pred.def_id()).instantiate_identity();
                    let ty = RustTyDecomposition::from_ty(ty, impl_ctx);
                    let const_task = ConstEncTask::Ty { const_, ty };
                    let const_expr = deps.require_dep::<ConstEnc>(const_task)?;
                    if let ty::ConstKind::Param(p) = const_.kind() {
                        generics_map
                            .entry(p.index)
                            .or_insert(const_expr.upcast_ty());
                    }
                    (projection.upcast_ty(), const_expr.upcast_ty())
                }
            };

            let projection_check = vcx.mk_eq_expr(projection, expr);
            checks.push(projection_check);
        }

        let checks = vcx.mk_conj(&checks);

        Ok(generics_map.iter().rfold(checks, |acc, (&idx, expr)| {
            let idx = impl_params.map_idx(idx);
            let decl = match idx {
                Ok(idx) => impl_params.ty_decls()[idx].upcast_ty(),
                Err(idx) => impl_params.const_decls()[idx].upcast_ty(),
            };
            vcx.mk_let_expr(decl, expr, acc)
        }))
    }
}
