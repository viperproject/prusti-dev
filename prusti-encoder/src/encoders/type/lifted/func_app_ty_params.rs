use prusti_rustc_interface::{
    middle::ty::{self, GenericArgsRef},
    span::def_id::DefId,
};
use task_encoder::{EncodeFullResult, Program, TaskEncoder};

use super::{
    generic::LiftedGeneric,
    ty::{EncodeGenericsAsLifted, LiftedTy, LiftedTyEnc, LiftedTyEncTask},
};

/// Encodes the type parameters to a function application. If we are
/// monomorphizing we must only pass to the function the type parameters that
/// are unknown from the caller's persepective, i.e., all [`ParamTy`]s within
/// the generics Otherwise, we simply encode each argument in the
/// [`GenericArgsRef`]
pub struct LiftedFuncAppTyParamsEnc;

impl TaskEncoder for LiftedFuncAppTyParamsEnc {
    task_encoder::encoder_cache!(LiftedFuncAppTyParamsEnc);

    type TaskDescription<'tcx> = (DefId, GenericArgsRef<'tcx>);

    type OutputFullLocal<'vir> = &'vir [LiftedTy<'vir, LiftedGeneric<'vir>>];

    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        vir::with_vcx(|vcx| {
            let (def_id, substs) = task_key;
            let param_env = vcx.tcx().param_env(def_id);
            let tys = substs.iter().filter_map(|arg| arg.as_type());

            // adapted from `ParamConst::find_const_ty_from_env` in rustc
            let mut const_tys = vec![None; substs.len()];
            for clause in param_env.caller_bounds() {
                let ty::ClauseKind::ConstArgHasType(param_ct, ty) = clause.kind().skip_binder() else { continue; };
                let ty::ConstKind::Param(param_ct) = param_ct.kind() else { continue; };
                const_tys[param_ct.index as usize] = Some(ty);
            }

            let ty_args: Vec<_> = tys.collect();
            let ty_args = ty_args
                .iter()
                .map(|ty| deps.require_local::<LiftedTyEnc<EncodeGenericsAsLifted>>(LiftedTyEncTask::Ty(*ty)))
                .collect::<Result<Vec<_>, _>>()?;
            let const_args = substs
                .iter()
                .enumerate()
                .filter_map(|(idx, arg)| Some((idx, arg.as_const()?)))
                .map(|(idx, c)| {
                    let const_ty = const_tys[idx].unwrap();
                    deps.require_local::<LiftedTyEnc<EncodeGenericsAsLifted>>(LiftedTyEncTask::Const(c, const_ty))
                })
                .collect::<Result<Vec<_>, _>>()?;
            let all_args = ty_args.into_iter()
                .chain(const_args)
                .collect::<Vec<_>>();
            Ok((vcx.alloc_slice(&all_args), ()))
        })
    }

    fn emit_outputs<'vir>(_program: &mut Program<'vir>) {
        let _outputs = Self::all_outputs_local_no_errors();
    }
}
