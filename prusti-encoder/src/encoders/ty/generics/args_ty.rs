use prusti_rustc_interface::middle::ty;
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};

use crate::encoders::{ConstEnc, r#const::ConstEncTask, ty::RustTyDecomposition};

use super::{GArgs, TyExprEnc};

/// Encodes type arguments when calling a function in this context
pub struct GArgsTyEnc;

#[derive(Debug, Clone, Copy)]
pub struct GArgsTy<'vir> {
    ty_args: &'vir [vir::ExprTyVal<'vir>],
    const_args: &'vir [vir::ExprCSnap<'vir>],
}

impl<'vir> GArgsTy<'vir> {
    /// If possible, use `GArgsTyEnc` instead.
    ///
    /// Builds the type/const arguments directly (e.g. to instantiate a builtin
    /// method with synthetic type parameters that don't have a corresponding
    /// Rust `GArgs`).
    pub fn new(
        ty_args: &'vir [vir::ExprTyVal<'vir>],
        const_args: &'vir [vir::ExprCSnap<'vir>],
    ) -> Self {
        GArgsTy {
            ty_args,
            const_args,
        }
    }

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
    const ENCODER_NAME: &'static str = "generic args type encoder";
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
        let ty_args = task_key
            .args
            .iter()
            .copied()
            .filter_map(ty::GenericArg::as_type)
            .map(|arg| {
                let decomp = RustTyDecomposition::from_ty(arg, task_key.context);
                deps.require_dep::<TyExprEnc>(decomp)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let const_args = task_key
            .args
            .iter()
            .copied()
            .filter_map(ty::GenericArg::as_const)
            .map(|const_| {
                // If the constant is a value, we already know its type.
                // Otherwise, we will look it up in the param environment.
                // TODO: what about the other ConstKind variants?
                let ty = match const_.kind() {
                    ty::ConstKind::Value(v) => v.ty,
                    ty::ConstKind::Param(p) => task_key.context.expect_const(p.index as usize).1,
                    other => unreachable!("unexpected ConstKind: {other:?}"),
                };
                deps.require_dep::<ConstEnc>(ConstEncTask::Ty {
                    const_,
                    ty,
                    context: task_key.context,
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        let args = vir::with_vcx(|vcx| GArgsTy {
            ty_args: vcx.alloc_slice(&ty_args),
            const_args: vcx.alloc_slice(&const_args),
        });
        Ok(((), args))
    }
}
