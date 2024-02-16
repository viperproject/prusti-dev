use prusti_rustc_interface::{middle::{mir, ty}, span::def_id::DefId};

use task_encoder::{TaskEncoder, TaskEncoderDependencies};
use vir::Reify;

use crate::encoders::{MirPureEnc, mir_pure::PureKind};
pub struct MirSpecEnc;

#[derive(Clone)]
pub struct MirSpecEncOutput<'vir> {
    pub pres: Vec<vir::Expr<'vir>>,
    pub posts: Vec<vir::Expr<'vir>>,
    pub pre_args: &'vir [vir::Expr<'vir>],
    pub post_args: &'vir [vir::Expr<'vir>],
}

impl TaskEncoder for MirSpecEnc {
    task_encoder::encoder_cache!(MirSpecEnc);

    type TaskDescription<'tcx> = (
        DefId,  // The function annotated with specs
        ty::GenericArgsRef<'tcx>, // ? this should be the "signature", after applying the env/substs
        Option<DefId>, // ID of the caller function, if any
        bool,   // If to encode as pure or not
    );

    type OutputFullLocal<'vir> = MirSpecEncOutput<'vir>;

    type EncodingError = <MirPureEnc as TaskEncoder>::EncodingError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'tcx: 'vir, 'vir>(
        task_key: &Self::TaskKey<'tcx>,
        deps: &mut TaskEncoderDependencies<'vir>,
    ) -> Result<
        (
            Self::OutputFullLocal<'vir>,
            Self::OutputFullDependency<'vir>,
        ),
        (
            Self::EncodingError,
            Option<Self::OutputFullDependency<'vir>>,
        ),
    > {
        let (def_id, substs, caller_def_id, pure) = *task_key;
        deps.emit_output_ref::<Self>(*task_key, ());

        let local_defs = deps.require_local::<crate::encoders::local_def::MirLocalDefEnc>(
            (def_id, substs, caller_def_id),
        ).unwrap();
        let specs = deps.require_local::<crate::encoders::SpecEnc>(
            crate::encoders::SpecEncTask {
                def_id,
            }
        ).unwrap();

        vir::with_vcx(|vcx| {
            let local_iter = (1..=local_defs.arg_count).map(mir::Local::from);
            let all_args: Vec<_> = if pure {
                let result_ty = local_defs.locals[mir::RETURN_PLACE].ty;
                local_iter
                    .map(|local| local_defs.locals[local].local_ex)
                    .chain([vcx.mk_local_ex(vir::vir_format!(vcx, "result"), result_ty.snapshot)])
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

            let to_bool = deps.require_ref::<crate::encoders::PredicateEnc>(
                vcx.tcx.types.bool,
            ).unwrap().expect_prim().snap_to_prim;

            let pres = specs.pres.iter().map(|spec_def_id| {
                let expr = deps.require_local::<crate::encoders::MirPureEnc>(
                    crate::encoders::MirPureEncTask {
                        encoding_depth: 0,
                        kind: PureKind::Spec,
                        parent_def_id: *spec_def_id,
                        param_env: vcx.tcx.param_env(spec_def_id),
                        substs,
                        // TODO: should this be `def_id` or `caller_def_id`
                        caller_def_id: def_id,
                    }
                ).unwrap().expr;
                let expr = expr.reify(vcx, (*spec_def_id, pre_args));
                to_bool.apply(vcx, [expr])
            }).collect::<Vec<vir::Expr<'_>>>();

            let post_args = if pure {
                all_args
            } else {
                let post_args: Vec<_> = pre_args.iter().map(|arg|
                        vcx.mk_old_expr(arg)
                    )
                    .chain([local_defs.locals[mir::RETURN_PLACE].impure_snap])
                    .collect();
                vcx.alloc_slice(&post_args)
            };
            let posts = specs.posts.iter().map(|spec_def_id| {
                let expr = deps.require_local::<crate::encoders::MirPureEnc>(
                    crate::encoders::MirPureEncTask {
                        encoding_depth: 0,
                        kind: PureKind::Spec,
                        parent_def_id: *spec_def_id,
                        param_env: vcx.tcx.param_env(spec_def_id),
                        substs,
                        // TODO: should this be `def_id` or `caller_def_id`
                        caller_def_id: def_id,
                    }
                ).unwrap().expr;
                let expr = expr.reify(vcx, (*spec_def_id, post_args));
                to_bool.apply(vcx, [expr])
            }).collect::<Vec<vir::Expr<'_>>>();
            let data = MirSpecEncOutput {
                pres,
                posts,
                pre_args,
                post_args,
            };
            Ok((data, ()))
        })
    }
}
