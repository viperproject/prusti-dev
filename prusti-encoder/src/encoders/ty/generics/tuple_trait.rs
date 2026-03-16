use crate::{
    TaskEncoder,
    encoders::ty::{
        RustTy,
        generics::{r#trait::TraitEnc, trait_impls::TraitImplEnc},
        lifted::TyConstructorEnc,
    },
};
use prusti_rustc_interface::middle::ty;

pub struct TupleTraitEnc;

const TUPLE_TRAIT_NAME: &str = "Tuple";
const TUPLE_TRAIT_ARGS: <(vir::ManyTyVal, vir::ManyCSnap) as vir::Arity>::Tys<'static> =
    (&[vir::TYPE_TYVAL], &[]);

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
        vir::with_vcx(|vcx| {
            let mut checks: Vec<_> = Self::all_outputs_local_no_errors()
                .into_iter()
                .flatten()
                .collect();

            let tuple_impl_idn = TraitEnc::trait_impl_idn(vcx, TUPLE_TRAIT_NAME, TUPLE_TRAIT_ARGS);
            let tuple_impl_unknown_idn =
                TraitEnc::trait_unknown_impl_idn(vcx, TUPLE_TRAIT_NAME, TUPLE_TRAIT_ARGS);

            let self_decl = Self::tuple_self_decl(vcx);
            let self_expr = vcx.mk_local_ex(self_decl);

            let unknown_check = {
                let is_unknown =
                    vcx.mk_adt_discriminator_expr(self_expr, TyConstructorEnc::UNKNOWN_TYPE_NAME);
                let unknown_id = TyConstructorEnc::unknown_type_id_accessor(vcx).call()(self_expr);

                let unknown_impls = tuple_impl_unknown_idn.call()(unknown_id, &[], &[]);

                vir::expr! {vcx; (is_unknown) && (unknown_impls) }
            };

            checks.push(unknown_check);

            let ensures = vcx.mk_eq_expr(vcx.mk_result(vir::TYPE_BOOL), vcx.mk_disj(&checks));

            let tuple_impl_idn = vcx.mk_function(
                tuple_impl_idn,
                (&[self_decl], &[]),
                &[],
                vcx.alloc_slice(&[ensures]),
                Some(&vir::DecreasesGenData::Star),
                None,
            );
            program.add_function(tuple_impl_idn);

            let tuple_impl_unknown_fun =
                vcx.mk_domain_function(tuple_impl_unknown_idn, false, None);

            let sized_domain = vcx.mk_domain(
                TraitEnc::trait_domain_idn(vcx, TUPLE_TRAIT_NAME),
                &[],
                &[],
                vcx.alloc_slice(&[tuple_impl_unknown_fun]),
                None,
            );
            program.add_domain(sized_domain);
        });
    }
}

impl TupleTraitEnc {
    fn tuple_self_decl<'vir>(vcx: &'vir vir::VirCtxt<'vir>) -> vir::LocalDecl<'vir, vir::TyVal> {
        vcx.mk_local_decl("Self$0_trait", vir::TYPE_TYVAL)
    }
}
