use prusti_rustc_interface::span::def_id::DefId;
use task_encoder::{TaskEncoder, TaskEncoderDependencies};
use vir::{MethodIdent, UnknownArity};

/// Encodes a Rust function as a Viper method using the polymorphic encoding of generics.
pub struct MirPolyImpureEnc;

#[derive(Clone, Debug)]
pub struct MirImpureEncOutputRef<'vir> {
    pub method_ref: MethodIdent<'vir, UnknownArity<'vir>>,
}
impl<'vir> task_encoder::OutputRefAny for MirImpureEncOutputRef<'vir> {}

#[derive(Clone, Debug)]
pub struct MirImpureEncOutput<'vir> {
    pub method: vir::Method<'vir>,
}

use crate::encoder_traits::impure_function_enc::{
    ImpureFunctionEnc, ImpureFunctionEncError, ImpureFunctionEncOutput, ImpureFunctionEncOutputRef,
};

impl ImpureFunctionEnc for MirPolyImpureEnc {
    fn mk_method_ident<'vir, 'tcx>(
        vcx: &'vir vir::VirCtxt<'tcx>,
        def_id: &Self::TaskKey<'tcx>,
    ) -> vir::ViperIdent<'vir> {
        vir::vir_format_identifier!(vcx, "m_{}", vcx.tcx().def_path_str(*def_id))
    }
}

impl TaskEncoder for MirPolyImpureEnc {
    task_encoder::encoder_cache!(MirPolyImpureEnc);

    type TaskDescription<'tcx> = DefId;

    type TaskKey<'tcx> = DefId;

    type OutputRef<'vir> = ImpureFunctionEncOutputRef<'vir>;
    type OutputFullLocal<'vir> = ImpureFunctionEncOutput<'vir>;

    type EncodingError = ImpureFunctionEncError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'tcx: 'vir, 'vir>(
        def_id: &Self::TaskKey<'tcx>,
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
        Ok((<Self as ImpureFunctionEnc>::encode(*def_id, deps), ()))
    }
}
