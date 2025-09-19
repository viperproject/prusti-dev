use prusti_interface::{PrustiError, specs::specifications::find_trait_method_substs};
use prusti_rustc_interface::{
    middle::{mir, ty},
    span::{Span, def_id::DefId},
};

use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{CastType, HasType, Reify};

use crate::encoders::{
    MirPureEnc,
    mir_pure::PureKind,
    ty::{RustTyDecomposition, use_pure::TyUsePureEnc},
};
pub struct MirSpecEnc;

#[derive(Clone)]
pub struct MirSpecEncOutput<'vir> {
    pub pres: Vec<vir::ExprBool<'vir>>,
    pub posts: Vec<vir::ExprBool<'vir>>,
    #[allow(clippy::type_complexity)]
    pub pledges: Vec<(
        Option<(vir::ExprBool<'vir>, Span)>,
        vir::ExprBool<'vir>,
        Span,
    )>, // TODO: associate with a named lifetime
    pub pre_args: &'vir [vir::ExprSnap<'vir>],
    #[allow(dead_code)]
    pub post_args: &'vir [vir::ExprSnap<'vir>],
}

impl TaskEncoder for MirSpecEnc {
    task_encoder::encoder_cache!(MirSpecEnc);

    type TaskDescription<'tcx> = (
        DefId, // The function annotated with specs
        bool,  // If to encode as pure or not
    );

    type OutputFullDependency<'vir> = MirSpecEncOutput<'vir>;

    type EncodingError = <MirPureEnc as TaskEncoder>::EncodingError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        let (def_id, pure) = *task_key;
        deps.emit_output_ref(*task_key, ())?;

        let local_defs =
            deps.require_dep::<crate::encoders::local_def::MirLocalDefEnc>((def_id, false))?;
        let specs =
            deps.require_dep::<crate::encoders::SpecEnc>(crate::encoders::SpecEncTask { def_id })?;

        vir::with_vcx(|vcx| {
            let is_panic_cold_explicit = is_panic_cold_explicit(vcx.tcx(), def_id);
            let substs = ty::GenericArgs::identity_for_item(vcx.tcx(), def_id);
            let local_iter = (1..=local_defs.arg_count).map(mir::Local::from);
            let all_args: Vec<vir::ExprSnap<'vir>> = if pure {
                let result_ty = local_defs[mir::RETURN_PLACE].local_snap.ty();
                local_iter
                    .map(|local| vcx.mk_local_ex(local_defs[local].local_snap))
                    .chain([vcx.mk_result(result_ty)])
                    .collect()
            } else {
                local_iter
                    .map(|local| local_defs[local].impure_snap)
                    .collect()
            };
            let all_args = vcx.alloc_slice(&all_args);
            let pre_args = if pure {
                &all_args[..all_args.len() - 1]
            } else {
                all_args
            };

            let to_bool = deps
                .require_dep::<TyUsePureEnc>(RustTyDecomposition::from_prim_ty(
                    vcx.tcx().types.bool,
                ))?
                .expect_primitive()
                .snap_to_prim;

            let substs = find_trait_method_substs(vcx.tcx(), def_id, substs)
                .map(|s| s.1)
                .unwrap_or(substs);

            let mut pres = specs
                .pres
                .iter()
                .map(|spec_def_id| {
                    let expr = deps
                        .require_dep::<crate::encoders::MirPureEnc>(
                            crate::encoders::MirPureEncTask {
                                encoding_depth: 0,
                                kind: PureKind::Spec(specs.extern_spec),
                                parent_def_id: *spec_def_id,
                                param_env: vcx.tcx().param_env(spec_def_id),
                                substs,
                                // TODO: should this be `def_id` or `caller_def_id`
                                caller_def_id: Some(def_id),
                            },
                        )
                        .unwrap()
                        .expr
                        .downcast_ty();
                    let expr = expr.reify(vcx, (*spec_def_id, pre_args));
                    let span = vcx.tcx().def_span(spec_def_id);
                    vcx.with_span(span, |_| to_bool(expr).downcast_ty())
                })
                .collect::<Vec<vir::ExprBool<'_>>>();

            let post_args = if pure {
                all_args
            } else {
                let post_args: Vec<vir::ExprSnap<'vir>> = pre_args
                    .iter()
                    .map(|arg| vcx.mk_old_expr(arg))
                    .chain([local_defs[mir::RETURN_PLACE].impure_snap])
                    .collect();
                vcx.alloc_slice(&post_args)
            };
            let posts = specs
                .posts
                .iter()
                .map(|spec_def_id| {
                    let span = vcx.tcx().def_span(spec_def_id);
                    vcx.with_span(span, |vcx| {
                        vcx.handle_error("postcondition.violated:assertion.false", move |_| {
                            Some(vec![PrustiError::verification(
                                "postcondition might not hold",
                                span.into(),
                            )])
                        });
                        let expr = deps
                            .require_dep::<crate::encoders::MirPureEnc>(
                                crate::encoders::MirPureEncTask {
                                    encoding_depth: 0,
                                    kind: PureKind::Spec(specs.extern_spec),
                                    parent_def_id: *spec_def_id,
                                    param_env: vcx.tcx().param_env(spec_def_id),
                                    substs,
                                    // TODO: should this be `def_id` or `caller_def_id`
                                    caller_def_id: Some(def_id),
                                },
                            )
                            .unwrap()
                            .expr
                            .downcast_ty();
                        let expr = expr.reify(vcx, (*spec_def_id, post_args));
                        to_bool(expr).downcast_ty()
                    })
                })
                .collect::<Vec<vir::ExprBool<'_>>>();
            let pledge_args = vcx.alloc_slice(
                &pre_args
                    .iter()
                    .map(|arg| vcx.mk_old_expr(arg))
                    .chain([local_defs[mir::RETURN_PLACE].impure_snap])
                    .collect::<Vec<_>>(),
            );
            let pledges = specs
                .pledges
                .iter()
                .map(|(lhs_def_id, rhs_def_id)| {
                    // TODO: report error locations
                    let lhs_expr = lhs_def_id.map(|lhs_def_id| {
                        deps.require_dep::<crate::encoders::MirPureEnc>(
                            crate::encoders::MirPureEncTask {
                                encoding_depth: 0,
                                kind: PureKind::Spec(specs.extern_spec),
                                parent_def_id: lhs_def_id,
                                param_env: vcx.tcx().param_env(lhs_def_id),
                                substs,
                                // TODO: should this be `def_id` or `caller_def_id`
                                caller_def_id: Some(def_id),
                            },
                        )
                        .unwrap()
                        .expr
                        .downcast_ty()
                    });
                    let rhs_expr = deps
                        .require_dep::<crate::encoders::MirPureEnc>(
                            crate::encoders::MirPureEncTask {
                                encoding_depth: 0,
                                kind: PureKind::Spec(specs.extern_spec),
                                parent_def_id: *rhs_def_id,
                                param_env: vcx.tcx().param_env(rhs_def_id),
                                substs,
                                // TODO: should this be `def_id` or `caller_def_id`
                                caller_def_id: Some(def_id),
                            },
                        )
                        .unwrap()
                        .expr
                        .downcast_ty();
                    let lhs_expr = lhs_expr
                        .map(|lhs_expr| lhs_expr.reify(vcx, (lhs_def_id.unwrap(), pledge_args)));
                    let rhs_expr = rhs_expr.reify(vcx, (*rhs_def_id, pledge_args));
                    let rhs_span = vcx.tcx().def_span(rhs_def_id);
                    (
                        lhs_expr.map(|lhs_expr| {
                            let lhs_span = vcx.tcx().def_span(lhs_def_id.unwrap());
                            (
                                vcx.with_span(lhs_span, |_| to_bool(lhs_expr).downcast_ty()),
                                lhs_span,
                            )
                        }),
                        vcx.with_span(rhs_span, |vcx| {
                            vcx.handle_error("exhale.failed:assertion.false", move |_| {
                                Some(vec![PrustiError::verification(
                                    "pledge postcondition might not hold",
                                    rhs_span.into(),
                                )])
                            });
                            to_bool(rhs_expr).downcast_ty()
                        }),
                        rhs_span,
                    )
                })
                .collect::<Vec<_>>();
            if is_panic_cold_explicit {
                assert!(pres.is_empty() && posts.is_empty() && pledges.is_empty());
                pres.push(vcx.mk_bool::<false>());
            }
            let data = MirSpecEncOutput {
                pres,
                posts,
                pledges,
                pre_args,
                post_args,
            };
            Ok(((), data))
        })
    }
}

/// TODO: fix this issue properly, rather than with a name matching hack (the
/// behaviour may also change in newer Rust versions)
///
/// Currently, rustc sometimes turns a `panic!()` into:
/// ```
/// #[inline(never)]
/// #[cold]
/// #[track_caller]
/// fn panic_cold_explicit() -> ! {
///    core::panicking::panic_explicit()
/// }
/// panic_cold_explicit();
/// ```
/// So we add a synthetic `#[requires(false)]` to any function that is called
/// `panic_cold_explicit`.
fn is_panic_cold_explicit(tcx: ty::TyCtxt<'_>, def_id: DefId) -> bool {
    tcx.item_name(def_id).as_str() == "panic_cold_explicit"
}
