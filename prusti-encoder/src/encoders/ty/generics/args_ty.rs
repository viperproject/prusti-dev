use prusti_rustc_interface::middle::ty;
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};

use crate::encoders::{ConstEnc, r#const::ConstEncTask, ty::RustTyDecomposition};

use super::{GArgs, GenericParamsEnc};

/// Encodes type arguments when calling a function in this context
pub struct GArgsTyEnc;

#[derive(Debug, Clone, Copy)]
pub struct GArgsTy<'vir> {
    ty_args: &'vir [vir::ExprTyVal<'vir>],
    const_args: &'vir [vir::ExprCSnap<'vir>],
}

impl<'vir> GArgsTy<'vir> {
    pub fn get_ty<Curr, Next>(&self) -> &'vir [vir::ExprGenTyVal<'vir, Curr, Next>] {
        let args = self.ty_args as *const [vir::ExprTyVal<'vir>]
            as *const [vir::ExprGenTyVal<'vir, Curr, Next>];
        unsafe { &*args }
    }

    pub fn get_const<Curr, Next>(&self) -> &'vir [vir::ExprGenCSnap<'vir, Curr, Next>] {
        let args = self.const_args as *const [vir::ExprCSnap<'vir>]
            as *const [vir::ExprGenCSnap<'vir, Curr, Next>];
        unsafe { &*args }
    }
}

impl TaskEncoder for GArgsTyEnc {
    task_encoder::encoder_cache!(GArgsTyEnc);
    type TaskDescription<'tcx> = GArgs<'tcx>;
    type OutputFullDependency<'vir> = GArgsTy<'vir>;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        let params = deps.require_dep::<GenericParamsEnc>(task_key.context)?;
        let ty_args = task_key
            .args
            .iter()
            .copied()
            .filter_map(ty::GenericArg::as_type)
            .map(|arg| {
                let decomp = RustTyDecomposition::from_ty(arg, task_key.context);
                params.ty_expr(deps, decomp)
            })
            .collect::<Vec<_>>();
        let const_args = task_key
            .args
            .iter()
            .copied()
            .enumerate()
            .filter_map(|(i, a)| ty::GenericArg::as_const(a).map(|a| (i, a)))
            .map(|(i, const_)| {
                let (_, ty) = task_key.context.expect_const(i);
                let task = ConstEncTask::Ty {
                    const_,
                    ty,
                    context: task_key.context,
                };
                deps.require_dep::<ConstEnc>(task)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let args = vir::with_vcx(|vcx| GArgsTy {
            ty_args: vcx.alloc_slice(&ty_args),
            const_args: vcx.alloc_slice(&const_args),
        });
        Ok(((), args))
    }
}
