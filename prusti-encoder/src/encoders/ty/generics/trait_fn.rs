use prusti_interface::specs::{is_spec_fn, specifications::SpecQuery};
use prusti_rustc_interface::{
    middle::{mir, ty},
    span::def_id::DefId,
};
use task_encoder::{EncodeFullResult, OutputRefAny, TaskEncoder, TaskEncoderDependencies};
use vir::{FunctionIdn, MethodIdn, vir_format_identifier};

use crate::{
    encoders::{
        FunctionCallEnc, MirLocalDefEnc, MirLocalDefEncTask, MirSpecEnc,
        mir_fn::CallTaskDescription,
        pure::spec::MirSpecEncMode,
        ty::generics::{GParams, GenericParamsEnc},
    },
    trait_support::is_function_with_body,
};

pub struct TraitFnEnc;

#[derive(Debug, Clone, Copy)]
pub struct TraitFnEncOutputRef<'vir> {
    pub pre_func: FunctionIdn<'vir, (vir::ManySnap, vir::ManyTyVal, vir::ManyCSnap), vir::Bool>,
    pub post_func:
        FunctionIdn<'vir, (vir::Snap, vir::ManySnap, vir::ManyTyVal, vir::ManyCSnap), vir::Bool>,
    pub call_stub_impure: Option<MethodIdn<'vir, (vir::ManyRef, vir::ManyTyVal, vir::ManyCSnap)>>,
    pub call_stub_pure_caller:
        Option<FunctionIdn<'vir, (vir::ManySnap, vir::ManyTyVal, vir::ManyCSnap), vir::Snap>>,
    pub call_stub_pure_function:
        Option<FunctionIdn<'vir, (vir::ManySnap, vir::ManyTyVal, vir::ManyCSnap), vir::Snap>>,
}

impl<'vir> OutputRefAny for TraitFnEncOutputRef<'vir> {}

impl TaskEncoder for TraitFnEnc {
    task_encoder::encoder_cache!(TraitFnEnc);

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    type TaskDescription<'vir> = DefId;

    type OutputRef<'vir> = TraitFnEncOutputRef<'vir>;
    type OutputFullLocal<'vir> = (
        vir::Domain<'vir>,
        Vec<vir::Function<'vir>>,
        Vec<vir::Method<'vir>>,
    );

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for (dom, funcs, methods) in Self::all_outputs_local_no_errors() {
            program.add_domain(dom);
            for func in funcs {
                program.add_function(func);
            }
            for method in methods {
                program.add_method(method);
            }
        }
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        vir::with_vcx(|vcx| {
            let tcx = vcx.tcx();

            let assoc_item = tcx
                .opt_associated_item(*task_key)
                .expect("task key should be the associated item of a trait");
            let def_id = assoc_item.def_id;
            let span = vcx.tcx().def_span(def_id);
            assert!(matches!(assoc_item.kind, ty::AssocKind::Fn { .. }));
            assert_eq!(def_id, *task_key);

            // Prusti specifications on trait methods emit additional spec-
            // only fn items (with default implementations). These should never
            // be passed here, even though they are part of the trait as far as
            // Rust typing is concerned.
            assert!(!is_spec_fn(tcx, def_id));

            let trait_def_id = assoc_item
                .trait_container(tcx)
                .expect("task key should be the associated item of a trait");

            let trait_name = vcx.alloc_str(tcx.item_name(trait_def_id).as_str());

            let mut axioms = Vec::new();
            let mut funcs = Vec::new();
            let mut dom_funcs = Vec::new();
            let mut methods = Vec::new();

            // item_generics also includes parameters of trait itself
            let item_params = GParams::from(def_id);
            let item_generics = deps.require_dep::<GenericParamsEnc>(item_params)?;
            let item_name = tcx.item_name(def_id);

            let local_defs = deps.require_dep::<MirLocalDefEnc>(MirLocalDefEncTask::Local {
                def_id,
                all_locals: false,
            })?;
            let arg_count = local_defs.arg_count + 1;
            let arg_types = vcx.alloc_slice(&local_defs.snap_ty_args().collect::<Vec<_>>());
            let return_type = local_defs.snap_ty_return();
            let ref_args = vcx.alloc_slice(&vec![vir::TYPE_REF; arg_count]);

            let is_pure = crate::encoders::with_proc_spec(
                SpecQuery::GetProcKind(def_id, item_params.rust_params()),
                |spec| spec.kind.is_pure().unwrap_or_default(),
            )
            .unwrap_or_default();

            let pre_func = FunctionIdn::new(
                vir_format_identifier!(vcx, "{trait_name}_fn_pre_{item_name}"),
                (
                    arg_types,
                    item_generics.ty_args(),
                    item_generics.const_args(),
                ),
                vir::TYPE_BOOL,
            );
            let post_func = FunctionIdn::new(
                vir_format_identifier!(vcx, "{trait_name}_fn_post_{item_name}"),
                // TODO: old(arg) types (if applicable)
                (
                    return_type,
                    arg_types,
                    item_generics.ty_args(),
                    item_generics.const_args(),
                ),
                vir::TYPE_BOOL,
            );
            // TODO: spec functions for each pledge

            let call_stub_impure = (!is_pure).then(|| {
                MethodIdn::new(
                    vir_format_identifier!(vcx, "{trait_name}_fn_stub_{item_name}"),
                    (
                        ref_args,
                        item_generics.ty_args(),
                        item_generics.const_args(),
                    ),
                )
            });
            let call_stub_pure_caller = is_pure.then(|| {
                FunctionIdn::new(
                    vir_format_identifier!(vcx, "{trait_name}_cfn_stub_{item_name}"),
                    (
                        arg_types,
                        item_generics.ty_args(),
                        item_generics.const_args(),
                    ),
                    return_type,
                )
            });
            let call_stub_pure_function = is_pure.then(|| {
                FunctionIdn::new(
                    vir_format_identifier!(vcx, "{trait_name}_fn_stub_{item_name}"),
                    (
                        arg_types,
                        item_generics.ty_args(),
                        item_generics.const_args(),
                    ),
                    return_type,
                )
            });
            deps.emit_output_ref(
                *task_key,
                TraitFnEncOutputRef {
                    pre_func,
                    post_func,
                    call_stub_impure,
                    call_stub_pure_caller,
                    call_stub_pure_function,
                },
            )?;
            dom_funcs.push(vcx.mk_domain_function(pre_func, false, None));
            dom_funcs.push(vcx.mk_domain_function(post_func, false, None));

            let func_args = local_defs.local_decl_args().collect::<Vec<_>>();
            let func_ret = local_defs.local_decl_ret();

            let has_body = is_function_with_body(vcx.tcx(), def_id);

            let spec = deps.require_dep_spanned::<MirSpecEnc>(
                (def_id, def_id, MirSpecEncMode::PureWithoutResult),
                span,
            )?;
            let pres = vcx.mk_conj(&spec.pres);
            let pre_func_call = pre_func.call()(
                vcx.alloc_slice(
                    &func_args
                        .iter()
                        .map(|arg| vcx.mk_local_ex(arg))
                        .collect::<Vec<_>>(),
                ),
                item_generics.ty_exprs(),
                item_generics.const_exprs(),
            );
            axioms.push(vcx.mk_domain_axiom(
                vir_format_identifier!(
                    vcx,
                    "{trait_name}_fn_pre_{item_name}_base",
                ),
                vir::expr! {
                    forall ..[func_args], ..[item_generics.ty_decls()], ..[item_generics.const_decls()] :: {[pre_func_call]}
                        (pres) ==> (pre_func_call)
                },
            ));
            let mut posts = spec.posts;
            if has_body && is_pure {
                let pure_func = deps.require_dep::<FunctionCallEnc>(
                    CallTaskDescription::new(def_id, item_params.rust_params(), def_id)
                        .resolve_trait_calls(false),
                )?;
                let pure_func_app = pure_func.call_pure(
                    func_args
                        .iter()
                        .map(|arg| vcx.mk_local_ex(arg))
                        .collect::<Vec<_>>(),
                );
                posts.push(vir::expr! {
                    ([func_ret]) == ([pure_func_app])
                });
            }
            let posts = vcx.mk_conj(&posts);
            let post_func_call = post_func.call()(
                vcx.mk_local_ex(func_ret),
                vcx.alloc_slice(
                    &func_args
                        .iter()
                        .map(|arg| vcx.mk_local_ex(arg))
                        .collect::<Vec<_>>(),
                ),
                item_generics.ty_exprs(),
                item_generics.const_exprs(),
            );
            axioms.push(vcx.mk_domain_axiom(
                vir_format_identifier!(
                    vcx,
                    "{trait_name}_fn_post_{item_name}_base",
                ),
                vir::expr! {
                    forall [func_ret], ..[func_args], ..[item_generics.ty_decls()], ..[item_generics.const_decls()] :: {[post_func_call]}
                        (post_func_call) ==> (posts)
                },
            ));

            if is_pure {
                let mut stub_pres = Vec::new();
                let mut stub_posts = Vec::new();
                stub_pres.push(pre_func.call()(
                    vcx.alloc_slice(
                        &local_defs
                            .args()
                            .map(|arg| vcx.mk_local_ex(arg.local_snap))
                            .collect::<Vec<_>>(),
                    ),
                    item_generics.ty_exprs(),
                    item_generics.const_exprs(),
                ));
                stub_posts.push(post_func.call()(
                    vcx.mk_result(local_defs.snap_ty_return()),
                    vcx.alloc_slice(
                        &local_defs
                            .args()
                            .map(|arg| vcx.mk_local_ex(arg.local_snap))
                            .collect::<Vec<_>>(),
                    ),
                    item_generics.ty_exprs(),
                    item_generics.const_exprs(),
                ));
                let wrapped_call = call_stub_pure_function.unwrap().call()(
                    &func_args
                        .iter()
                        .map(|arg| vcx.mk_local_ex(arg))
                        .collect::<Vec<_>>(),
                    item_generics.ty_exprs(),
                    item_generics.const_exprs(),
                );
                funcs.push(vcx.mk_function(
                    call_stub_pure_caller.unwrap(),
                    (
                        &func_args,
                        item_generics.ty_decls(),
                        item_generics.const_decls(),
                    ),
                    vcx.alloc_slice(&stub_pres),
                    vcx.alloc_slice(&stub_posts),
                    Some(&vir::DecreasesGenData::Star),
                    Some(wrapped_call),
                ));
                funcs.push(vcx.mk_function(
                    call_stub_pure_function.unwrap(),
                    (
                        &func_args,
                        item_generics.ty_decls(),
                        item_generics.const_decls(),
                    ),
                    &[],
                    vcx.alloc_slice(&stub_posts),
                    None,
                    None,
                ));
            } else {
                let mut stub_pres = Vec::new();
                let mut stub_posts = Vec::new();
                let mut args = Vec::with_capacity(arg_count + item_params.count());
                for arg_idx in (0..arg_count).map(mir::Local::from) {
                    let name_p = local_defs[arg_idx].local.name;
                    args.push(vir::vir_local_decl! { vcx; [name_p] : Ref });
                    if arg_idx != mir::RETURN_PLACE {
                        stub_pres.push(local_defs[arg_idx].impure_pred);
                    }
                }
                stub_posts.push(local_defs[mir::RETURN_PLACE].impure_pred);
                // TODO: wands

                stub_pres.push(pre_func.call()(
                    vcx.alloc_slice(
                        &local_defs
                            .args()
                            .map(|arg| arg.impure_snap)
                            .collect::<Vec<_>>(),
                    ),
                    item_generics.ty_exprs(),
                    item_generics.const_exprs(),
                ));
                // TODO: mutable arguments should also have a post-state
                stub_posts.push(post_func.call()(
                    local_defs.ret().impure_snap,
                    vcx.alloc_slice(
                        &local_defs
                            .args()
                            .map(|arg| vcx.mk_old_expr(arg.impure_snap))
                            .collect::<Vec<_>>(),
                    ),
                    item_generics.ty_exprs(),
                    item_generics.const_exprs(),
                ));

                methods.push(vcx.mk_method(
                    call_stub_impure.unwrap(),
                    (
                        args.as_slice(),
                        item_generics.ty_decls(),
                        item_generics.const_decls(),
                    ),
                    &[],
                    vcx.alloc_slice(&stub_pres),
                    vcx.alloc_slice(&stub_posts),
                    None,
                ));
            }

            let trait_domain = vcx.mk_domain(
                vir_format_identifier!(vcx, "trait_fns_{trait_name}_{item_name}"),
                &[],
                vcx.alloc_slice(&axioms),
                vcx.alloc_slice(&dom_funcs),
                None,
            );

            Ok(((trait_domain, funcs, methods), ()))
        })
    }
}
