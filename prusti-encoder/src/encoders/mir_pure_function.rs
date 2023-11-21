use prusti_rustc_interface::{middle::{mir, ty}, span::def_id::DefId};

use task_encoder::{TaskEncoder, TaskEncoderDependencies};
use vir::{Reify, FunctionIdent, UnknownArity, CallableIdent};
use std::cell::RefCell;

use crate::encoders::{
    MirPureEncoder, MirPureEncoderTask, SpecEncoder, SpecEncoderTask, TypeEncoder, mir_pure::PureKind,
};

use super::TypeEncoderOutputRef;
pub struct MirFunctionEncoder;

#[derive(Clone, Debug)]
pub enum MirFunctionEncoderError {
    Unsupported,
}

#[derive(Clone, Debug)]
pub struct MirFunctionEncoderOutputRef<'vir> {
    pub function_ref: FunctionIdent<'vir, UnknownArity<'vir>>,
    /// Always `TypeData::Domain`.
    pub return_type: &'vir TypeEncoderOutputRef<'vir>,
}
impl<'vir> task_encoder::OutputRefAny for MirFunctionEncoderOutputRef<'vir> {}

#[derive(Clone, Debug)]
pub struct MirFunctionEncoderOutput<'vir> {
    pub function: vir::Function<'vir>,
}

thread_local! {
    static CACHE: task_encoder::CacheStaticRef<MirFunctionEncoder> = RefCell::new(Default::default());
}

impl TaskEncoder for MirFunctionEncoder {
    type TaskDescription<'vir> = (
        DefId, // ID of the function
        ty::GenericArgsRef<'vir>, // ? this should be the "signature", after applying the env/substs
        DefId, // Caller DefID
    );

    type OutputRef<'vir> = MirFunctionEncoderOutputRef<'vir>;
    type OutputFullLocal<'vir> = MirFunctionEncoderOutput<'vir>;

    type EncodingError = MirFunctionEncoderError;

    fn with_cache<'tcx: 'vir, 'vir, F, R>(f: F) -> R
    where
        F: FnOnce(&'vir task_encoder::CacheRef<'tcx, 'vir, MirFunctionEncoder>) -> R,
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
        let (def_id, substs, caller_def_id) = *task_key;
        let trusted = crate::encoders::with_proc_spec(def_id, |def_spec|
            def_spec.trusted.extract_inherit().unwrap_or_default()
        ).unwrap_or_default();

        vir::with_vcx(|vcx| {
            let local_defs = deps.require_local::<crate::encoders::local_def::MirLocalDefEncoder>(
                (def_id, substs, Some(caller_def_id)),
            ).unwrap();

            tracing::debug!("encoding {def_id:?}");

            let extra: String = substs.iter().map(|s| format!("_{s}")).collect();
            let (krate, index) = (caller_def_id.krate, caller_def_id.index.index());
            let function_name = vir::vir_format!(vcx, "f_{}{extra}_CALLER_{krate}_{index}", vcx.tcx.item_name(def_id));
            let args: Vec<_> = (1..=local_defs.arg_count)
                .map(mir::Local::from)
                .map(|def_idx| local_defs.locals[def_idx].ty.snapshot)
                .collect();
            let args = UnknownArity::new(vcx.alloc_slice(&args));
            let function_ref = FunctionIdent::new(function_name, args);
            deps.emit_output_ref::<Self>(*task_key, MirFunctionEncoderOutputRef { function_ref, return_type: local_defs.locals[mir::RETURN_PLACE].ty });

            let spec = deps.require_local::<crate::encoders::pure::spec::MirSpecEncoder>(
                (def_id, substs, Some(caller_def_id), true)
            ).unwrap();

            let func_args: Vec<_> = (1..=local_defs.arg_count).map(mir::Local::from).map(|arg| vcx.alloc(vir::LocalDeclData {
                name: local_defs.locals[arg].local.name,
                ty: local_defs.locals[arg].ty.snapshot,
            })).collect();

            let expr = if trusted {
                None
            } else {
                // Encode the body of the function
                let expr = deps
                    .require_local::<MirPureEncoder>(MirPureEncoderTask {
                        encoding_depth: 0,
                        kind: PureKind::Pure,
                        parent_def_id: def_id,
                        promoted: None,
                        param_env: vcx.tcx.param_env(def_id),
                        substs,
                        caller_def_id,
                    })
                    .unwrap()
                    .expr;

                Some(expr.reify(vcx, (def_id, spec.pre_args)))
            };

            tracing::debug!("finished {def_id:?}");

            Ok((
                MirFunctionEncoderOutput {
                    function: vcx.mk_function(
                        function_name,
                        vcx.alloc_slice(&func_args),
                        local_defs.locals[mir::RETURN_PLACE].ty.snapshot,
                        vcx.alloc_slice(&spec.pres),
                        vcx.alloc_slice(&spec.posts),
                        expr
                    ),
                },
                (),
            ))
        })
    }
}
