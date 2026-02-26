use crate::{
    TaskEncoder,
    encoders::ty::{
        Sizedness,
        generics::{
            GArgs, GArgsTyEnc, GParams, GenericParamsEnc,
            traits::{TraitEnc, trait_impl_fun_idn, trait_unknown_impl_fun_idn},
        },
        lifted::ty_constructor::{unknown_type_discriminator, unknown_type_id_accessor},
    },
};
use prusti_rustc_interface::middle::ty;

pub struct SizedTraitEnc;

const SIZED_TRAIT_NAME: &str = "Sized";

#[derive(Copy, Debug, Clone, Hash, Eq, PartialEq)]
pub struct SizedTraitEncTask<'vir> {
    pub sizedness: Sizedness<'vir>,
    pub discriminator: &'vir str,
    pub ty_accessors: &'vir [vir::AdtDestructor<'vir, vir::TyVal, vir::TyVal>],
    pub const_accessors: &'vir [vir::AdtDestructor<'vir, vir::TyVal, vir::CSnap>],
    pub ty_ctx: GParams<'vir>,
}

impl TaskEncoder for SizedTraitEnc {
    task_encoder::encoder_cache!(SizedTraitEnc);
    type TaskDescription<'vir> = SizedTraitEncTask<'vir>;

    type OutputFullLocal<'vir> = Option<vir::ExprBool<'vir>>;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir, Self>,
    ) -> task_encoder::EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        let &Self::TaskKey {
            sizedness,
            discriminator,
            ty_accessors,
            const_accessors,
            ty_ctx,
        } = task_key;
        vir::with_vcx(|vcx| {
            let self_expr = vcx.mk_local_ex(sized_self_decl(vcx));

            let is_this_type = vcx.mk_adt_discriminator_expr(self_expr, discriminator);

            let sized_impl_fun_idn =
                trait_impl_fun_idn(vcx, SIZED_TRAIT_NAME, (&[vir::TYPE_TYVAL], &[]));
            let check = match sizedness {
                Sizedness::Sized => Some(is_this_type),
                Sizedness::Unsized => None,
                Sizedness::Dependent(ty) => match ty.kind() {
                    ty::TyKind::Param(param) => {
                        let accessor = ty_accessors[param.index as usize];
                        let param_ty = accessor.call()(self_expr);
                        // We know that in reality `Sized` only has the `Self` type parameter
                        let inner_sized_check = sized_impl_fun_idn.call()(&[param_ty], &[]);
                        Some(vir::expr! { vcx; (is_this_type) && (inner_sized_check) })
                    }
                    ty::TyKind::Alias(ty::AliasTyKind::Projection, alias_ty) => {
                        let alias_did = alias_ty.def_id;
                        let trait_def = alias_ty.trait_def_id(vcx.tcx());
                        let trait_ = deps.require_ref::<TraitEnc>(trait_def)?;
                        let projection_fun = trait_.funs.assoc_types[&alias_did];

                        let ty_params = deps.require_dep::<GenericParamsEnc>(ty_ctx)?;
                        let args =
                            deps.require_dep::<GArgsTyEnc>(GArgs::new(ty_ctx, alias_ty.args))?;

                        let projection = projection_fun(args.get_ty(), args.get_const());
                        let inner_sized_check = sized_impl_fun_idn.call()(&[projection], &[]);

                        let inner_expr = vir::expr! { vcx;
                            (is_this_type) && (inner_sized_check)
                        };

                        // Introduce let-bindings for the generics of the type
                        // NOTE: There won't be any name collisions as user defined ADTs cannot
                        // have a generic called `Self`
                        let with_consts_bound = ty_params.const_decls().iter().enumerate().rfold(
                            inner_expr,
                            |expr, (i, decl)| {
                                let accessor = const_accessors[i];
                                vcx.mk_let_expr(decl, accessor.call()(self_expr), expr)
                            },
                        );
                        let with_tys_bound = ty_params.ty_decls().iter().enumerate().rfold(
                            with_consts_bound,
                            |expr, (i, decl)| {
                                let accessor = ty_accessors[i];
                                vcx.mk_let_expr(decl, accessor.call()(self_expr), expr)
                            },
                        );
                        Some(with_tys_bound)
                    }
                    _ => panic!("Unsupported dependent sizedness for {ty:?}"),
                },
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

            let sized_impl_fun_idn =
                trait_impl_fun_idn(vcx, SIZED_TRAIT_NAME, (&[vir::TYPE_TYVAL], &[]));
            let sized_impl_unknown_fun_idn =
                trait_unknown_impl_fun_idn(vcx, SIZED_TRAIT_NAME, (&[vir::TYPE_TYVAL], &[]));

            let self_decl = sized_self_decl(vcx);
            let self_expr = vcx.mk_local_ex(self_decl);

            let unknown_check = {
                let is_unknown =
                    vcx.mk_adt_discriminator_expr(self_expr, unknown_type_discriminator());
                let unknown_id = unknown_type_id_accessor(vcx).call()(self_expr);

                let unknown_impls = sized_impl_unknown_fun_idn.call()(unknown_id, &[], &[]);

                vir::expr! {vcx; (is_unknown) && (unknown_impls) }
            };

            checks.push(unknown_check);

            let sized_impl_fun = vcx.mk_function(
                sized_impl_fun_idn,
                (&[self_decl], &[]),
                &[],
                &[],
                None,
                Some(vcx.mk_disj(&checks)),
            );
            program.add_function(sized_impl_fun);

            let sized_impl_unknown_fun = vcx.mk_function(
                sized_impl_unknown_fun_idn,
                (vcx.mk_local_decl("id", vir::TYPE_INT), &[], &[]),
                &[],
                &[],
                None,
                None,
            );

            program.add_function(sized_impl_unknown_fun);
        });
    }
}

fn sized_self_decl<'vir>(vcx: &'vir vir::VirCtxt<'vir>) -> vir::LocalDecl<'vir, vir::TyVal> {
    vcx.mk_local_decl("Self$0", vir::TYPE_TYVAL)
}
