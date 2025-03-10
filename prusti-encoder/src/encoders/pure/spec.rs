use prusti_interface::PrustiError;
use prusti_rustc_interface::{
    middle::{mir, ty},
    span::def_id::DefId,
};

use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::Reify;

use crate::encoders::{mir_pure::PureKind, rust_ty_predicates::RustTyPredicatesEnc, MirPureEnc};
pub struct MirSpecEnc;

#[derive(Clone)]
pub struct MirSpecEncOutput<'vir> {
    pub pres: Vec<vir::Expr<'vir>>,
    pub posts: Vec<vir::Expr<'vir>>,
    pub pledges: Vec<(Option<vir::Expr<'vir>>, vir::Expr<'vir>)>, // TODO: associate with a named lifetime
    pub pre_args: &'vir [vir::Expr<'vir>],
    #[allow(dead_code)]
    pub post_args: &'vir [vir::Expr<'vir>],
}

impl TaskEncoder for MirSpecEnc {
    task_encoder::encoder_cache!(MirSpecEnc);

    type TaskDescription<'tcx> = (
        DefId,                    // The function annotated with specs
        ty::GenericArgsRef<'tcx>, // ? this should be the "signature", after applying the env/substs
        Option<DefId>,            // ID of the caller function, if any
        bool,                     // If to encode as pure or not
    );

    type OutputFullLocal<'vir> = MirSpecEncOutput<'vir>;

    type EncodingError = <MirPureEnc as TaskEncoder>::EncodingError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        let (def_id, substs, caller_def_id, pure) = *task_key;
        deps.emit_output_ref(*task_key, ())?;

        let local_defs = deps.require_local::<crate::encoders::local_def::MirLocalDefEnc>((
            def_id,
            substs,
            caller_def_id,
        ))?;
        let specs = deps
            .require_local::<crate::encoders::SpecEnc>(crate::encoders::SpecEncTask { def_id })?;

        vir::with_vcx(|vcx| {
            let local_iter = (1..=local_defs.arg_count).map(mir::Local::from);
            let all_args: Vec<_> = if pure {
                let result_ty = local_defs.locals[mir::RETURN_PLACE].ty;
                local_iter
                    .map(|local| {
                        vcx.mk_local_ex(
                            local_defs.locals[local].local.name,
                            local_defs.locals[local].ty.snapshot,
                        )
                    })
                    .chain([vcx.mk_result(result_ty.snapshot)])
                    .collect()
            } else {
                local_iter
                    .map(|local| local_defs.locals[local].impure_snap)
                    .collect()
            };
            let all_args = vcx.alloc_slice(&all_args);
            let pre_args = if pure {
                &all_args[..all_args.len() - 1]
            } else {
                all_args
            };

            let to_bool = deps
                .require_ref::<RustTyPredicatesEnc>(vcx.tcx().types.bool)?
                .generic_predicate
                .expect_prim()
                .snap_to_prim;

            let pres = specs
                .pres
                .iter()
                .map(|spec_def_id| {
                    let expr = deps
                        .require_local::<crate::encoders::MirPureEnc>(
                            crate::encoders::MirPureEncTask {
                                encoding_depth: 0,
                                kind: PureKind::Spec,
                                parent_def_id: *spec_def_id,
                                param_env: vcx.tcx().param_env(spec_def_id),
                                substs,
                                // TODO: should this be `def_id` or `caller_def_id`
                                caller_def_id: Some(def_id),
                            },
                        )
                        .unwrap()
                        .expr;
                    let expr = expr.reify(vcx, (*spec_def_id, pre_args));
                    let span = vcx.tcx().def_span(spec_def_id);
                    vcx.with_span(span, |vcx| to_bool.apply(vcx, [expr]))
                })
                .collect::<Vec<vir::Expr<'_>>>();

            let post_args = if pure {
                all_args
            } else {
                let post_args: Vec<_> = pre_args
                    .iter()
                    .map(|arg| vcx.mk_old_expr(arg))
                    .chain([local_defs.locals[mir::RETURN_PLACE].impure_snap])
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
                            .require_local::<crate::encoders::MirPureEnc>(
                                crate::encoders::MirPureEncTask {
                                    encoding_depth: 0,
                                    kind: PureKind::Spec,
                                    parent_def_id: *spec_def_id,
                                    param_env: vcx.tcx().param_env(spec_def_id),
                                    substs,
                                    // TODO: should this be `def_id` or `caller_def_id`
                                    caller_def_id: Some(def_id),
                                },
                            )
                            .unwrap()
                            .expr;
                        let expr = expr.reify(vcx, (*spec_def_id, post_args));
                        to_bool.apply(vcx, [expr])
                    })
                })
                .collect::<Vec<vir::Expr<'_>>>();
            let pledges = specs
                .pledges
                .iter()
                .map(|(lhs_def_id, rhs_def_id)| {
                    // TODO: report error locations
                    let lhs_expr = lhs_def_id.map(|lhs_def_id| deps
                        .require_local::<crate::encoders::MirPureEnc>(
                            crate::encoders::MirPureEncTask {
                                encoding_depth: 0,
                                kind: PureKind::Spec,
                                parent_def_id: lhs_def_id,
                                param_env: vcx.tcx().param_env(lhs_def_id),
                                substs,
                                // TODO: should this be `def_id` or `caller_def_id`
                                caller_def_id: Some(def_id),
                            },
                        )
                        .unwrap()
                        .expr);
                    let rhs_expr = deps
                        .require_local::<crate::encoders::MirPureEnc>(
                            crate::encoders::MirPureEncTask {
                                encoding_depth: 0,
                                kind: PureKind::Spec,
                                parent_def_id: *rhs_def_id,
                                param_env: vcx.tcx().param_env(rhs_def_id),
                                substs,
                                // TODO: should this be `def_id` or `caller_def_id`
                                caller_def_id: Some(def_id),
                            },
                        )
                        .unwrap()
                        .expr;
                    let lhs_expr = lhs_expr.map(|lhs_expr| lhs_expr.reify(vcx, (lhs_def_id.unwrap(), post_args)));
                    let rhs_expr = rhs_expr.reify(vcx, (*rhs_def_id, post_args));
                    (
                        lhs_expr.map(|lhs_expr| vcx.with_span(vcx.tcx().def_span(lhs_def_id.unwrap()), |vcx| to_bool.apply(vcx, [lhs_expr]))),
                        vcx.with_span(vcx.tcx().def_span(rhs_def_id), |vcx| to_bool.apply(vcx, [rhs_expr])),
                    )
                })
                .collect::<Vec<_>>();
            let data = MirSpecEncOutput {
                pres,
                posts,
                pledges,
                pre_args,
                post_args,
            };
            Ok((data, ()))
        })
    }
}
