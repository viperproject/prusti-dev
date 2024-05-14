use std::collections::HashSet;

use prusti_rustc_interface::middle::ty::{GenericArgsRef, Ty, TyKind};
use task_encoder::TaskEncoder;

use super::{
    generic::LiftedGeneric,
    ty::{EncodeGenericsAsLifted, LiftedTy, LiftedTyEnc},
};

/// Encodes the type parameters to a function application. If we are
/// monomorphizing we must only pass to the function the type parameters that
/// are unknown from the caller's persepective, i.e., all [`ParamTy`]s within
/// the generics Otherwise, we simply encode each argument in the
/// [`GenericArgsRef`]
pub struct LiftedFuncAppTyParamsEnc;

impl TaskEncoder for LiftedFuncAppTyParamsEnc {
    task_encoder::encoder_cache!(LiftedFuncAppTyParamsEnc);
    // 1st: true iff we are monomorphizing
    type TaskDescription<'tcx> = (bool, GenericArgsRef<'tcx>);

    type OutputFullLocal<'vir> = &'vir [LiftedTy<'vir, LiftedGeneric<'vir>>];

    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'tcx: 'vir, 'vir>(
        task_key: &Self::TaskKey<'tcx>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir>,
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
        deps.emit_output_ref::<Self>(*task_key, ());
        vir::with_vcx(|vcx| {
            let (monomorphize, substs) = task_key;
            let tys = substs.iter().filter_map(|arg| arg.as_type());

            let ty_args: Vec<_> = if *monomorphize {
                unique(tys.flat_map(extract_ty_params)).collect()
            } else {
                tys.collect()
            };
            let ty_args = ty_args
                .iter()
                .map(|ty| {
                    deps.require_local::<LiftedTyEnc<EncodeGenericsAsLifted>>(*ty)
                        .unwrap()
                })
                .collect::<Vec<_>>();
            Ok((vcx.alloc_slice(&ty_args), ()))
        })
    }
}

fn unique<'tcx>(iter: impl IntoIterator<Item = Ty<'tcx>>) -> impl Iterator<Item = Ty<'tcx>> {
    let mut seen = HashSet::new();
    iter.into_iter().filter(move |item| seen.insert(*item))
}

fn extract_ty_params(ty: Ty<'_>) -> Vec<Ty<'_>> {
    match ty.kind() {
        TyKind::Param(_) => vec![ty],
        TyKind::Adt(_, args) => args
            .iter()
            .filter_map(|arg| arg.as_type())
            .flat_map(|arg| extract_ty_params(arg))
            .collect(),
        TyKind::Int(_) | TyKind::Uint(_) | TyKind::Float(_) | TyKind::Bool | TyKind::Char => vec![],
        other => todo!("{:?}", other),
    }
}
