use prusti_rustc_interface::{middle::{mir, ty}, span::def_id::DefId};

use task_encoder::{TaskEncoder, TaskEncoderDependencies};
use vir::{Reify, FunctionIdent, UnknownArity, CallableIdent};
use std::cell::RefCell;

use crate::encoders::{
    MirPureEncoder, MirPureEncoderTask, SpecEncoder, SpecEncoderTask, TypeEncoder,
};
pub struct MirFunctionEncoder;

#[derive(Clone, Debug)]
pub enum MirFunctionEncoderError {
    Unsupported,
}

#[derive(Clone, Debug)]
pub struct MirFunctionEncoderOutputRef<'vir> {
    pub function_ref: FunctionIdent<'vir, UnknownArity<'vir>>,
}
impl<'vir> task_encoder::OutputRefAny<'vir> for MirFunctionEncoderOutputRef<'vir> {}

#[derive(Clone, Debug)]
pub struct MirFunctionEncoderOutput<'vir> {
    pub function: vir::Function<'vir>,
}

thread_local! {
    static CACHE: task_encoder::CacheStaticRef<MirFunctionEncoder> = RefCell::new(Default::default());
}

impl TaskEncoder for MirFunctionEncoder {
    type TaskDescription<'vir> = DefId;

    type OutputRef<'vir> = MirFunctionEncoderOutputRef<'vir>;
    type OutputFullLocal<'vir> = MirFunctionEncoderOutput<'vir>;

    type EncodingError = MirFunctionEncoderError;

    fn with_cache<'vir, F, R>(f: F) -> R
    where
        F: FnOnce(&'vir task_encoder::CacheRef<'vir, MirFunctionEncoder>) -> R,
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
        vir::with_vcx(|vcx| {
            let def_id = *task_key;
            let local_defs = deps.require_local::<crate::encoders::local_def::MirLocalDefEncoder>(
                def_id,
            ).unwrap();

            tracing::debug!("encoding {def_id:?}");

            let function_name = vir::vir_format!(vcx, "f_{}", vcx.tcx.item_name(def_id));
            let args: Vec<_> = (1..=local_defs.arg_count)
                .map(mir::Local::from)
                .map(|def_idx| local_defs.locals[def_idx].snapshot)
                .collect();
            let args = UnknownArity::new(vcx.alloc_slice(&args));
            let function_ref = FunctionIdent::new(function_name, args);
            deps.emit_output_ref::<Self>(def_id, MirFunctionEncoderOutputRef { function_ref });

            let spec = deps.require_local::<crate::encoders::pure::spec::MirSpecEncoder>(
                (def_id, true)
            ).unwrap();

            let func_args: Vec<_> = (1..=local_defs.arg_count).map(mir::Local::from).map(|arg| vcx.alloc(vir::LocalDeclData {
                name: local_defs.locals[arg].local.name,
                ty: local_defs.locals[arg].snapshot,
            })).collect();

            // Encode the body of the function
            let expr = deps
                .require_local::<MirPureEncoder>(MirPureEncoderTask {
                    encoding_depth: 0,
                    parent_def_id: def_id,
                    promoted: None,
                    param_env: vcx.tcx.param_env(def_id),
                    substs: ty::List::identity_for_item(vcx.tcx, def_id),
                })
                .unwrap()
                .expr;
            let expr = expr.reify(vcx, (def_id, &spec.pre_args[1..]));

            tracing::debug!("finished {def_id:?}");

            Ok((
                MirFunctionEncoderOutput {
                    function: vcx.alloc(vir::FunctionData {
                        name: function_name,
                        args: vcx.alloc_slice(&func_args),
                        ret: local_defs.locals[mir::RETURN_PLACE].snapshot,
                        pres: vcx.alloc_slice(&spec.pres),
                        posts: vcx.alloc_slice(&spec.posts),
                        expr: Some(expr),
                    }),
                },
                (),
            ))
        })
    }
}
