use prusti_rustc_interface::{
    middle::ty::{self, GenericArgs},
    span::def_id::DefId,
};

use task_encoder::{TaskEncoder, TaskEncoderDependencies};

use crate::encoder_traits::pure_function_enc::{
    PureFunctionEnc, MirFunctionEncOutput, MirFunctionEncOutputRef,
};

pub struct MirFunctionEnc;

#[derive(Clone, Debug)]
pub enum MirFunctionEncError {
    Unsupported,
}

impl PureFunctionEnc for MirFunctionEnc {
    fn get_substs<'tcx>(
        vcx: &vir::VirCtxt<'tcx>,
        def_id: &Self::TaskKey<'tcx>,
    ) -> &'tcx GenericArgs<'tcx> {
        GenericArgs::identity_for_item(vcx.tcx(), *def_id)
    }

    fn mk_function_ident<'vir, 'tcx>(
        vcx: &'vir vir::VirCtxt<'tcx>,
        def_id: &Self::TaskKey<'tcx>,
    ) -> vir::ViperIdent<'vir> {
        vir::vir_format_identifier!(vcx, "f_{}", vcx.tcx().item_name(*def_id))
    }

    fn get_def_id(task_key: &Self::TaskKey<'_>) -> DefId {
        *task_key
    }

    fn get_caller_def_id(_task_key: &Self::TaskKey<'_>) -> Option<DefId> {
        None
    }
}

impl TaskEncoder for MirFunctionEnc {
    task_encoder::encoder_cache!(MirFunctionEnc);

    type TaskDescription<'vir> = (
        DefId,                    // ID of the function
        ty::GenericArgsRef<'vir>, // ? this should be the "signature", after applying the env/substs
        DefId,                    // Caller DefID
    );

    type OutputRef<'vir> = MirFunctionEncOutputRef<'vir>;
    type OutputFullLocal<'vir> = MirFunctionEncOutput<'vir>;
    type TaskKey<'tcx> = DefId;

    type EncodingError = MirFunctionEncError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        task.0
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
