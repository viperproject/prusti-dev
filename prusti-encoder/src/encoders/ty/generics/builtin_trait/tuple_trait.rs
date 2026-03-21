use crate::encoders::ty::generics::{
    GParams, builtin_trait::BuiltinTraitEnc, trait_impls::TraitImplEnc,
};
use prusti_rustc_interface::{middle::ty, span::def_id::DefId};
use task_encoder::EncodeFullError;

pub struct TupleTrait;

impl super::BuiltinTrait for TupleTrait {
    task_encoder::encoder_cache!(BuiltinTraitEnc<TupleTrait>);

    fn def_id() -> DefId {
        vir::with_vcx(|vcx| vcx.tcx().lang_items().tuple_trait().unwrap())
    }

    fn does_impl<'vir>(
        deps: &mut task_encoder::TaskEncoderDependencies<'vir, BuiltinTraitEnc<Self>>,
        ctx: GParams<'vir>,
        ty: ty::Ty<'vir>,
    ) -> Result<Option<vir::ExprBool<'vir>>, EncodeFullError<'vir, BuiltinTraitEnc<Self>>> {
        vir::with_vcx(|vcx| {
            let tcx = vcx.tcx();

            let tuple_trait_did = tcx.lang_items().tuple_trait().unwrap();

            let check = if matches!(ty.kind(), ty::TyKind::Tuple(..)) {
                let impls_tuple = ty::TraitRef::new_from_args(
                    tcx,
                    tuple_trait_did,
                    tcx.mk_args_trait(ty, std::iter::empty()),
                );
                Some(TraitImplEnc::impl_block_check(vcx, deps, ctx, impls_tuple)?)
            } else {
                None
            };

            Ok(check)
        })
    }
}
