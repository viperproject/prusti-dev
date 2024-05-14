use prusti_rustc_interface::span::def_id::DefId;

use task_encoder::{TaskEncoder, TaskEncoderDependencies, EncodeFullResult};

use crate::encoder_traits::pure_function_enc::{
    MirFunctionEncOutput, MirFunctionEncOutputRef, PureFunctionEnc
};

use super::mono::task_description::FunctionCallTaskDescription;

pub struct MirFunctionEnc;

#[derive(Clone, Debug)]
pub enum MirFunctionEncError {
    Unsupported,
}

impl PureFunctionEnc for MirFunctionEnc {

    fn mk_function_ident<'vir, 'tcx>(
        vcx: &'vir vir::VirCtxt<'tcx>,
        def_id: &Self::TaskKey<'tcx>,
    ) -> vir::ViperIdent<'vir> {
        vir::vir_format_identifier!(vcx, "f_{}", vcx.tcx().def_path_str(*def_id))
    }
}

impl TaskEncoder for MirFunctionEnc {
    task_encoder::encoder_cache!(MirFunctionEnc);

    type TaskDescription<'tcx> = FunctionCallTaskDescription<'tcx>;

    type OutputRef<'vir> = MirFunctionEncOutputRef<'vir>;
    type OutputFullLocal<'vir> = MirFunctionEncOutput<'vir>;
    type TaskKey<'tcx> = DefId;

    type EncodingError = MirFunctionEncError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        task.def_id
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        Ok((<Self as PureFunctionEnc>::encode(*task_key, deps), ()))
    }
}
