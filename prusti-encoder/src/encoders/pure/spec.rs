use prusti_rustc_interface::{middle::{mir, ty}, span::def_id::DefId};

use task_encoder::{TaskEncoder, TaskEncoderDependencies};
use vir::Reify;
use std::cell::RefCell;

use crate::encoders::{MirPureEncoder, mir_pure::PureKind};
pub struct MirSpecEncoder;

#[derive(Clone)]
pub struct MirSpecEncoderOutput<'vir> {
    pub pres: Vec<vir::Expr<'vir>>,
    pub posts: Vec<vir::Expr<'vir>>,
    pub pre_args: &'vir [vir::Expr<'vir>],
    pub post_args: &'vir [vir::Expr<'vir>],
}

thread_local! {
    static CACHE: task_encoder::CacheStaticRef<MirSpecEncoder> = RefCell::new(Default::default());
}

impl TaskEncoder for MirSpecEncoder {
    type TaskDescription<'tcx> = (
        DefId,  // The function annotated with specs
        ty::GenericArgsRef<'tcx>, // ? this should be the "signature", after applying the env/substs
        Option<DefId>, // ID of the caller function, if any
        bool,   // If to encode as pure or not
    );

    type OutputFullLocal<'vir> = MirSpecEncoderOutput<'vir>;

    type EncodingError = <MirPureEncoder as TaskEncoder>::EncodingError;

    fn with_cache<'tcx: 'vir, 'vir, F, R>(f: F) -> R
    where
        F: FnOnce(&'vir task_encoder::CacheRef<'tcx, 'vir, MirSpecEncoder>) -> R,
    {
        CACHE.with(|cache| {
            // SAFETY: the 'vir and 'tcx given to this function will always be
            //   the same (or shorter) than the lifetimes of the VIR arena and
            //   the rustc type context, respectively
            let cache = unsafe { std::mem::transmute(cache) };
            f(cache)
        })
    }

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

        let local_defs = deps.require_local::<crate::encoders::local_def::MirLocalDefEncoder>(
            (def_id, substs, caller_def_id),
        ).unwrap();
        let specs = deps.require_local::<crate::encoders::SpecEncoder>(
            crate::encoders::SpecEncoderTask {
                def_id,
            }
        ).unwrap();

        vir::with_vcx(|vcx| {
            let local_iter = (1..=local_defs.arg_count).map(mir::Local::from);
            let all_args: Vec<_> = if pure {
                    local_iter
                        .map(|local| local_defs.locals[local].local_ex)
                        .chain([vcx.mk_local_ex(vir::vir_format!(vcx, "result"))])
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

            let to_bool = deps.require_ref::<crate::encoders::TypeEncoder>(
                vcx.tcx.types.bool,
            ).unwrap().expect_prim().snap_to_prim;

            let pres = specs.pres.iter().map(|spec_def_id| {
                let expr = deps.require_local::<crate::encoders::MirPureEncoder>(
                    crate::encoders::MirPureEncoderTask {
                        encoding_depth: 0,
                        kind: PureKind::Spec,
                        parent_def_id: *spec_def_id,
                        promoted: None,
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
                let expr = deps.require_local::<crate::encoders::MirPureEncoder>(
                    crate::encoders::MirPureEncoderTask {
                        encoding_depth: 0,
                        kind: PureKind::Spec,
                        parent_def_id: *spec_def_id,
                        promoted: None,
                        param_env: vcx.tcx.param_env(spec_def_id),
                        substs,
                        // TODO: should this be `def_id` or `caller_def_id`
                        caller_def_id: def_id,
                    }
                ).unwrap().expr;
                let expr = expr.reify(vcx, (*spec_def_id, post_args));
                to_bool.apply(vcx, [expr])
            }).collect::<Vec<vir::Expr<'_>>>();
            let data = MirSpecEncoderOutput {
                pres,
                posts,
                pre_args,
                post_args,
            };
            Ok((data, ()))
        })
    }
}
