use prusti_rustc_interface::{middle::ty::GenericArgs, span::def_id::DefId};
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};

/// Encodes a Rust function as a Viper method using the monomorphic encoding of generics.
pub struct MirMonoImpureEnc;

use crate::{
    encoder_traits::{
        function_enc::FunctionEnc,
        impure_function_enc::{
            ImpureFunctionEnc, ImpureFunctionEncError, ImpureFunctionEncOutput,
            ImpureFunctionEncOutputRef,
        },
    },
    encoders::FunctionCallTaskDescription,
};

impl FunctionEnc for MirMonoImpureEnc {
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

impl ImpureFunctionEnc for MirMonoImpureEnc {
    fn mk_method_ident<'vir, 'tcx>(
        vcx: &'vir vir::VirCtxt<'tcx>,
        task_key: &Self::TaskKey<'tcx>,
    ) -> vir::ViperIdent<'vir> {
        task_key.vir_method_ident(vcx)
    }
}

impl TaskEncoder for MirMonoImpureEnc {
    task_encoder::encoder_cache!(MirMonoImpureEnc);

    type TaskDescription<'tcx> = FunctionCallTaskDescription<'tcx>;

    type OutputRef<'vir> = ImpureFunctionEncOutputRef<'vir>;
    type OutputFullLocal<'vir> = ImpureFunctionEncOutput<'vir>;

    type EncodingError = ImpureFunctionEncError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        <Self as ImpureFunctionEnc>::encode(*task_key, deps).map(|r| (r, ()))
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for output in Self::all_outputs_local() {
            program.add_method(output.method);
        }
    }
}
