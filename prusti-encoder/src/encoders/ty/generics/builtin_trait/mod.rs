use crate::encoders::ty::{generics::r#trait::TraitEnc, lifted::TyConstructorEnc};

use task_encoder::TaskEncoder;
pub mod sized_trait;
pub mod tuple_trait;

trait BuiltinTrait {
    const NAME: &'static str;
    const ARGS: <(vir::ManyTyVal, vir::ManyCSnap) as vir::Arity>::Tys<'static>;
    type Encoder: for<'vir> TaskEncoder<OutputFullLocal<'vir> = Option<vir::ExprBool<'vir>>>;
}

fn emit_builtin_trait_outputs<'vir, T>(program: &mut task_encoder::Program<'vir>)
where
    T: BuiltinTrait,
    T::Encoder: 'vir,
{
    vir::with_vcx(|vcx| {
        let mut checks: Vec<_> = T::Encoder::all_outputs_local_no_errors()
            .into_iter()
            .flatten()
            .collect();

        let impl_idn = TraitEnc::trait_impl_idn(vcx, T::NAME, T::ARGS);
        let impl_unknown_idn = TraitEnc::trait_unknown_impl_idn(vcx, T::NAME, T::ARGS);

        let self_decl = vcx.mk_local_decl("Self$0_trait", vir::TYPE_TYVAL);

        let self_expr = vcx.mk_local_ex(self_decl);

        let unknown_check = {
            let is_unknown =
                vcx.mk_adt_discriminator_expr(self_expr, TyConstructorEnc::UNKNOWN_TYPE_NAME);
            let unknown_id = TyConstructorEnc::unknown_type_id_accessor(vcx).call()(self_expr);

            let unknown_impls = impl_unknown_idn.call()(unknown_id, &[], &[]);

            vir::expr! {vcx; (is_unknown) && (unknown_impls) }
        };

        checks.push(unknown_check);

        let ensures = vcx.mk_eq_expr(vcx.mk_result(vir::TYPE_BOOL), vcx.mk_disj(&checks));

        let impl_fun = vcx.mk_function(
            impl_idn,
            (&[self_decl], &[]),
            &[],
            vcx.alloc_slice(&[ensures]),
            Some(&vir::DecreasesGenData::Star),
            None,
        );
        program.add_function(impl_fun);

        let impl_unknown_fun = vcx.mk_domain_function(impl_unknown_idn, false, None);

        let domain = vcx.mk_domain(
            TraitEnc::trait_domain_idn(vcx, T::NAME),
            &[],
            &[],
            vcx.alloc_slice(&[impl_unknown_fun]),
            None,
        );
        program.add_domain(domain);
    });
}
