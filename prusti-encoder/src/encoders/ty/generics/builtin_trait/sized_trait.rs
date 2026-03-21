use crate::encoders::ty::generics::{
    GParams, builtin_trait::BuiltinTraitEnc, trait_impls::TraitImplEnc,
};
use prusti_rustc_interface::middle::{ty, ty::Upcast};
use task_encoder::EncodeFullError;

use prusti_rustc_interface::span::def_id::DefId;
pub struct SizedTrait;

impl super::BuiltinTrait for SizedTrait {
    task_encoder::encoder_cache!(BuiltinTraitEnc<SizedTrait>);

    fn def_id() -> DefId {
        vir::with_vcx(|vcx| vcx.tcx().lang_items().sized_trait().unwrap())
    }

    fn does_impl<'vir>(
        deps: &mut task_encoder::TaskEncoderDependencies<'vir, BuiltinTraitEnc<Self>>,
        ctx: GParams<'vir>,
        ty: ty::Ty<'vir>,
    ) -> Result<Option<vir::ExprBool<'vir>>, EncodeFullError<'vir, BuiltinTraitEnc<Self>>> {
        vir::with_vcx(|vcx| {
            let sizedness = sizedness_for_ty(vcx.tcx(), ty);
            let check = match sizedness {
                Sizedness::Unsized => None,
                Sizedness::Sized => Some(sizedness_check(vcx, deps, ctx, ty, None)?),
                Sizedness::Dependent(dep_ty) => {
                    Some(sizedness_check(vcx, deps, ctx, ty, Some(dep_ty))?)
                }
            };

            Ok(check)
        })
    }
}

fn sizedness_check<'vir>(
    vcx: &'vir vir::VirCtxt<'vir>,
    deps: &mut task_encoder::TaskEncoderDependencies<'vir, BuiltinTraitEnc<SizedTrait>>,
    impl_ctx: GParams<'vir>,
    impl_ty: ty::Ty<'vir>,
    depended_on: Option<ty::Ty<'vir>>,
) -> Result<vir::ExprBool<'vir>, EncodeFullError<'vir, BuiltinTraitEnc<SizedTrait>>> {
    let tcx = vcx.tcx();

    let sized_did = tcx.lang_items().sized_trait().unwrap();

    let impls_sized = ty::TraitRef::new_from_args(
        tcx,
        sized_did,
        tcx.mk_args_trait(impl_ty, std::iter::empty()),
    );

    let param_env = ty::ParamEnv::new(
        tcx.mk_clauses(
            depended_on
                .map(|dep_ty| ty::TraitRef::new(tcx, sized_did, [dep_ty]).upcast(tcx))
                .as_slice(),
        ),
    );

    let impl_ctx = GParams::new(impl_ctx.rust_params(), param_env, false);

    TraitImplEnc::impl_block_check(vcx, deps, impl_ctx, impls_sized)
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum Sizedness<'tcx> {
    /// A type is definitely `Sized`
    Sized,
    /// A type is definitely not `Sized`
    Unsized,
    /// The sizedness of the type depends on the sizedness some other type contained within
    Dependent(ty::Ty<'tcx>),
}

impl<'tcx> Sizedness<'tcx> {
    fn map(self, f: impl FnOnce(ty::Ty<'tcx>) -> ty::Ty<'tcx>) -> Self {
        match self {
            Sizedness::Dependent(ty) => Sizedness::Dependent(f(ty)),
            other => other,
        }
    }
}

/// Modified version of `https://doc.rust-lang.org/nightly/nightly-rustc/rustc_ty_utils/ty/fn.sizedness_constraint_for_ty.html`
fn sizedness_for_ty<'tcx>(tcx: ty::TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> Sizedness<'tcx> {
    match ty.kind() {
        // Always `Sized`
        ty::Bool
        | ty::Char
        | ty::Int(..)
        | ty::Uint(..)
        | ty::Float(..)
        | ty::RawPtr(..)
        | ty::Ref(..)
        | ty::FnDef(..)
        | ty::FnPtr(..)
        | ty::Array(..)
        | ty::Closure(..)
        | ty::CoroutineClosure(..)
        | ty::Coroutine(..)
        | ty::CoroutineWitness(..)
        | ty::Never => Sizedness::Sized,

        ty::Str | ty::Slice(..) | ty::Dynamic(..) => Sizedness::Unsized,

        // Maybe `Sized`
        ty::Param(..) | ty::Alias(..) | ty::Error(_) => Sizedness::Dependent(ty),

        // We cannot instantiate the binder, so just return the *original* type back,
        // but only if the inner type has a sized constraint. Thus we skip the binder,
        // but don't actually use the result from `sizedness_for_ty`.
        ty::UnsafeBinder(inner_ty) => sizedness_for_ty(tcx, inner_ty.skip_binder()).map(|_| ty),

        // Never `Sized`
        ty::Foreign(..) => Sizedness::Unsized,

        // Recursive cases
        ty::Pat(ty, _) => sizedness_for_ty(tcx, *ty),

        // Empty tuple always `Sized`, otherwise sizedness depends on last field
        ty::Tuple(tys) => tys
            .last()
            .map_or(Sizedness::Sized, |last| sizedness_for_ty(tcx, *last)),

        ty::Adt(adt, args) => adt
            .sizedness_constraint(tcx, ty::SizedTraitKind::Sized)
            .map_or(Sizedness::Sized, |intermediate| {
                let ty = intermediate.instantiate(tcx, args);
                sizedness_for_ty(tcx, ty)
            }),

        ty::Placeholder(..) | ty::Bound(..) | ty::Infer(..) => {
            panic!("unexpected type `{ty:?}` in `sizedness_for_ty`")
        }
    }
}
