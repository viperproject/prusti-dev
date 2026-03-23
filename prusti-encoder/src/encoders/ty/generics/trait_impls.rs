use prusti_interface::{PrustiError, specs::specifications::SpecQuery};
use prusti_rustc_interface::{
    middle::{mir, ty},
    span::def_id::DefId,
};
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{Domain, Method, MethodIdn, vir_format_identifier};

use crate::{
    encoders::{
        FunctionCallEnc, MirLocalDefEnc, MirLocalDefEncTask, MirSpecEnc, Pure,
        mir_fn::{CallTaskDescription, RustSignature},
        pure::spec::MirSpecEncMode,
        ty::{
            RustTyDecomposition,
            generics::{
                GArgs, GArgsCastEnc, GArgsTyEnc, GParams, GenericParamsEnc, r#trait::TraitEnc,
                trait_fn::TraitFnEnc,
            },
        },
    },
    trait_support::is_function_with_body,
};

pub struct TraitImplEnc;

impl TaskEncoder for TraitImplEnc {
    task_encoder::encoder_cache!(TraitImplEnc);
    const ENCODER_NAME: &'static str = "trait impl encoder";

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

            let args = deps.require_dep::<GArgsTyEnc>(GArgs::new(impl_context, trait_ref.args))?;

            let mut axioms = Vec::new();
            let mut methods = Vec::new();

            let implementing_ty = tcx.type_of(task_key).instantiate_identity();
            let implementing_ty = RustTyDecomposition::from_ty(implementing_ty, impl_context);
            let implementing_ty = implementing_ty.ty.name();

            let impl_fun = trait_data.impl_fun;
            let impl_ty_decls = impl_params.ty_decls();
            let impl_const_decls = impl_params.const_decls();
            let trait_tys = args.get_ty();
            let trait_consts = args.get_const();

            axioms.push(vcx.mk_domain_axiom(
                vir_format_identifier!(vcx, "{trait_name}_impl_{implementing_ty}_{idx}_does_impl"),
                vir::expr! {forall ..[impl_ty_decls], ..[impl_const_decls] :: {[impl_fun(trait_tys, trait_consts)]} [impl_fun(trait_tys, trait_consts)]},
            ));

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
                let impl_item_params = deps
                    .require_dep::<GenericParamsEnc>(impl_item_context)
                    .unwrap();

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
                        );
                        axioms.push(vcx.mk_domain_axiom(
                            vir_format_identifier!(vcx, "{trait_name}_impl_{implementing_ty}_{idx}_assoc_type_{item_name}"),
                            vir::expr! {forall ..[trait_ty_decls], ..[trait_const_decls] :: {[assoc_type(trait_tys, trait_consts)]} ([assoc_type(trait_tys, trait_consts)]) == (assoc_type_expr)},
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
                (),
            ))
        })
    }
}
