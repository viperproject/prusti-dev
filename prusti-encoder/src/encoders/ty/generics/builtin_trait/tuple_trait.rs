use crate::{
    TaskEncoder,
    encoders::ty::{RustTy, generics::trait_impls::TraitImplEnc},
};
use prusti_rustc_interface::middle::ty;

struct TupleTrait;

impl super::BuiltinTrait for TupleTrait {
    const NAME: &'static str = "Tuple";
    const ARGS: <(vir::ManyTyVal, vir::ManyCSnap) as vir::Arity>::Tys<'static> =
        (&[vir::TYPE_TYVAL], &[]);
    type Encoder = TupleTraitEnc;
}

pub struct TupleTraitEnc;

impl TaskEncoder for TupleTraitEnc {
    task_encoder::encoder_cache!(TupleTraitEnc);
    type TaskDescription<'vir> = RustTy<'vir>;

    type OutputFullLocal<'vir> = Option<vir::ExprBool<'vir>>;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir, Self>,
    ) -> task_encoder::EncodeFullResult<'vir, Self> {
        assert!(!task_key.specifics.is_param());
        deps.emit_output_ref(*task_key, ())?;

        vir::with_vcx(|vcx| {
            let tcx = vcx.tcx();
            let ty = task_key.erased_ty_for_sizedness();

            let tuple_trait_did = tcx.lang_items().tuple_trait().unwrap();

            let check = if matches!(ty.kind(), ty::TyKind::Tuple(..)) {
                let impls_tuple = ty::TraitRef::new_from_args(
                    tcx,
                    tuple_trait_did,
                    tcx.mk_args_trait(ty, std::iter::empty()),
                );
                Some(TraitImplEnc::impl_block_check(
                    vcx,
                    deps,
                    task_key.params,
                    impls_tuple,
                )?)
            } else {
                None
            };

            Ok((check, ()))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        super::emit_builtin_trait_outputs::<TupleTrait>(program);
    }
}
