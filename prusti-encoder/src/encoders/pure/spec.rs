use prusti_rustc_interface::{middle::{mir, ty}, span::def_id::DefId};

use task_encoder::{TaskEncoder, TaskEncoderDependencies};
use vir::Reify;
use std::cell::RefCell;

use crate::encoders::MirPureEncoder;
pub struct MirSpecEncoder;

#[derive(Clone)]
pub struct MirSpecEncoderOutput<'vir> {
    pub pres: Vec<vir::Expr<'vir>>,
    pub posts: Vec<vir::Expr<'vir>>,
    pub pre_args: &'vir [vir::Expr<'vir>],
}

thread_local! {
    static CACHE: task_encoder::CacheStaticRef<MirSpecEncoder> = RefCell::new(Default::default());
}

impl TaskEncoder for MirSpecEncoder {
    type TaskDescription<'vir> = (
        DefId,  // The function annotated with specs
        bool,   // If to encode as pure or not
    );

    type OutputFullLocal<'vir> = MirSpecEncoderOutput<'vir>;

    type EncodingError = <MirPureEncoder as TaskEncoder>::EncodingError;

    fn with_cache<'vir, F, R>(f: F) -> R
    where
        F: FnOnce(&'vir task_encoder::CacheRef<'vir, MirSpecEncoder>) -> R,
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

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
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
        let (def_id, pure) = *task_key;
        deps.emit_output_ref::<Self>(*task_key, ());

        let local_defs = deps.require_local::<crate::encoders::local_def::MirLocalDefEncoder>(
            def_id,
        ).unwrap();
        let specs = deps.require_local::<crate::encoders::SpecEncoder>(
            crate::encoders::SpecEncoderTask {
                def_id,
            }
        ).unwrap();

        vir::with_vcx(|vcx| {
            let pre_args: Vec<_> = (0..=local_defs.arg_count)
                .map(mir::Local::from)
                .map(|local| {
                    if pure {
                        if local.index() == 0 {
                            vcx.mk_local_ex(vir::vir_format!(vcx, "result"))
                        } else {
                            local_defs.locals[local].local_ex
                        }
                    } else {
                        local_defs.locals[local].impure_snap
                    }
                })
                .collect();
            let pre_args = vcx.alloc_slice(&pre_args);

            let to_bool = deps.require_ref::<crate::encoders::TypeEncoder>(
                vcx.tcx.types.bool,
            ).unwrap().expect_prim().snap_to_prim;

            let pres = specs.pres.iter().map(|spec_def_id| {
                let expr = deps.require_local::<crate::encoders::MirPureEncoder>(
                    crate::encoders::MirPureEncoderTask {
                        encoding_depth: 0,
                        parent_def_id: *spec_def_id,
                        promoted: None,
                        param_env: vcx.tcx.param_env(spec_def_id),
                        substs: ty::List::identity_for_item(vcx.tcx, *spec_def_id),
                    }
                ).unwrap().expr;
                let expr = expr.reify(vcx, (*spec_def_id, &pre_args[1..]));
                to_bool.apply(vcx, [expr])
            }).collect::<Vec<vir::Expr<'_>>>();

            let post_args = if pure {
                pre_args
            } else {
                let post_args: Vec<_> = pre_args.iter().enumerate().map(|(idx, arg)| {
                    if idx == 0 {
                        arg
                    } else {
                        vcx.alloc(vir::ExprData::Old(arg))
                    }
                }).collect();
                vcx.alloc_slice(&post_args)
            };
            let posts = specs.posts.iter().map(|spec_def_id| {
                let expr = deps.require_local::<crate::encoders::MirPureEncoder>(
                    crate::encoders::MirPureEncoderTask {
                        encoding_depth: 0,
                        parent_def_id: *spec_def_id,
                        promoted: None,
                        param_env: vcx.tcx.param_env(spec_def_id),
                        substs: ty::List::identity_for_item(vcx.tcx, *spec_def_id),
                    }
                ).unwrap().expr;
                let expr = expr.reify(vcx, (*spec_def_id, post_args));
                to_bool.apply(vcx, [expr])
            }).collect::<Vec<vir::Expr<'_>>>();
            let data = MirSpecEncoderOutput {
                pres,
                posts,
                pre_args,
            };
            Ok((data, ()))
        })
    }
}
