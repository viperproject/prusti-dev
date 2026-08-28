use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};

use super::{
    RustParamData, RustTyDecomposition, TySpecifics,
    generics::{GArgsTy, GArgsTyEnc},
    inhabited::{TyInhabitedEnc, TyInhabitedRef},
};

#[derive(Debug, Clone, Copy)]
pub struct TyUseInhabitedRef<'vir> {
    inhabited: TyInhabitedRef<'vir>,
    args: GArgsTy<'vir>,
}

impl<'vir> task_encoder::OutputRefAny for TyUseInhabitedRef<'vir> {}

impl<'vir> TyUseInhabitedRef<'vir> {
    pub fn inhabited<Curr, Next>(&self) -> vir::ExprGenBool<'vir, Curr, Next> {
        self.inhabited.apply(self.args)
    }
}

pub struct TyUseInhabitedEnc;

impl TaskEncoder for TyUseInhabitedEnc {
    task_encoder::encoder_cache!(TyUseInhabitedEnc);
    const ENCODER_NAME: &'static str = "inhabited type use encoder";

    type TaskDescription<'vir> = RustTyDecomposition<'vir>;
    type OutputRef<'vir> = TyUseInhabitedRef<'vir>;
    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        let inhabited = deps.require_ref::<TyInhabitedEnc>(task_key.ty)?;
        let args = deps.require_dep::<GArgsTyEnc>(task_key.args)?;
        let output_ref = TyUseInhabitedRef { inhabited, args };
        deps.emit_output_ref(*task_key, output_ref)?;

        // No axiom should be emitted for fully generic parameters
        if matches!(
            task_key.ty.specifics,
            TySpecifics::Param(RustParamData::Generic)
        ) {
            return Ok(((), ()));
        }

        // Ensure the relevant axioms are emitted for all nested types, e.g., if
        // the input type is `Pair<u32, T>`, this will encode inhabitedness for
        // `u32` and `T` (the latter being a no-op).
        for arg in task_key.args.args().iter().filter_map(|arg| arg.as_type()) {
            let arg = RustTyDecomposition::from_ty(arg, task_key.args.context());
            deps.require_ref::<TyUseInhabitedEnc>(arg)?;
        }

        Ok(((), ()))
    }
}
