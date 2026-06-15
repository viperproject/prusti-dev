mod use_casters;
mod params;
mod casters;
mod args_ty;
mod args;
pub mod r#trait;
pub mod trait_fn;
pub mod trait_impls;
mod ty_expr;
pub(super) mod interior_mut;

pub use args::*;
pub use args_ty::*;
pub use params::*;
pub use ty_expr::*;
pub use use_casters::*;

// TODO: where does this belong?
pub(crate) fn ty_identity_expr<'vir, T: task_encoder::TaskEncoder>(
    deps: &mut task_encoder::TaskEncoderDependencies<'vir, T>,
    ty: crate::encoders::ty::RustTyDecomposition<'vir>,
) -> vir::ExprTyVal<'vir> {
    let params = deps.require_dep::<GenericParamsEnc>(ty.ty.params).unwrap();
    params.ty_expr(deps, ty).unwrap()
}
