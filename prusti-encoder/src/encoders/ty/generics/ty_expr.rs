use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};

use crate::encoders::ty::{RustTyDecomposition, generics::GenericParamsEnc};

/// Encodes a Rust type as a Viper expression.
pub struct TyExprEnc;

impl TaskEncoder for TyExprEnc {
    task_encoder::encoder_cache!(TyExprEnc);
    const ENCODER_NAME: &'static str = "type expression encoder";
    type TaskDescription<'tcx> = RustTyDecomposition<'tcx>;
    type OutputFullDependency<'vir> = vir::ExprTyVal<'vir>;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        let params = deps.require_dep::<GenericParamsEnc>(task_key.args.context)?;
        Ok(((), params.ty_expr(deps, *task_key)?))
    }
}
