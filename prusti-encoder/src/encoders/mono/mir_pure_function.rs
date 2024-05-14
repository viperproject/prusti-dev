use prusti_rustc_interface::{middle::ty::GenericArgs, span::def_id::DefId};
use task_encoder::{TaskEncoder, TaskEncoderDependencies};

use crate::{
    encoder_traits::{function_enc::FunctionEnc, pure_function_enc::{MirFunctionEncOutput, MirFunctionEncOutputRef, PureFunctionEnc}},
    encoders::mir_pure_function::{MirFunctionEnc, MirFunctionEncError},
};

impl FunctionEnc for MirMonoFunctionEnc {
    fn get_def_id(task_key: &Self::TaskKey<'_>) -> DefId {
        task_key.def_id
    }

    fn get_caller_def_id(task_key: &Self::TaskKey<'_>) -> Option<DefId> {
        Some(task_key.caller_def_id)
    }

    fn get_substs<'tcx>(
        _vcx: &vir::VirCtxt<'tcx>,
        task_key: &Self::TaskKey<'tcx>,
    ) -> &'tcx GenericArgs<'tcx> {
        task_key.substs
    }
}

impl PureFunctionEnc for MirMonoFunctionEnc {

    fn mk_function_ident<'vir, 'tcx>(
        vcx: &'vir vir::VirCtxt<'tcx>,
        task_key: &Self::TaskKey<'tcx>,
    ) -> vir::ViperIdent<'vir> {
        task_key.vir_function_ident(vcx)
    }
}

/// Encodes a function definition, monorphised based on the substitutions at the
/// call site. Any parameters that are generic at the call are still generic in
/// the encoded function; the monomorphised function takes as input all generic
/// type arguments at the call site. For example consider the following:
///
/// fn id<T>(x: T) -> T { x }
/// fn g<U, V>(pair: Pair<Option<U>, V>) -> Pair<Option<U>, V> { id(pair) }
///
/// The monomorphised encoding of `id` for the call in `g` would take type
/// parameters `U`, `V`.
pub struct MirMonoFunctionEnc;

impl TaskEncoder for MirMonoFunctionEnc {
    task_encoder::encoder_cache!(MirMonoFunctionEnc);

    type TaskDescription<'vir> = <MirFunctionEnc as TaskEncoder>::TaskDescription<'vir>;

    type OutputRef<'vir> = MirFunctionEncOutputRef<'vir>;
    type OutputFullLocal<'vir> = MirFunctionEncOutput<'vir>;

    type EncodingError = MirFunctionEncError;

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
        Ok((<Self as PureFunctionEnc>::encode(*task_key, deps), ()))
    }
}
