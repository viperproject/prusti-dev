use crate::{
    TaskEncoder,
    encoders::ty::{
        RustTy, Sizedness,
        generics::{GArgs, GArgsTyEnc, GParams, GenericParamsEnc, traits::TraitEnc},
        lifted::{TyConstructorEnc, ty_constructor::TyConstructorEncOutputRef},
    },
};
use prusti_rustc_interface::middle::ty;
use vir::CallableIdn;

pub struct SizedTraitEnc;

const SIZED_TRAIT_NAME: &str = "Sized";
const SIZED_ARGS: <(vir::ManyTyVal, vir::ManyCSnap) as vir::Arity>::Tys<'static> =
    (&[vir::TYPE_TYVAL], &[]);

impl TaskEncoder for SizedTraitEnc {
    task_encoder::encoder_cache!(SizedTraitEnc);
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

        let vpr_type = deps.require_ref::<TyConstructorEnc>(*task_key)?;
        let discriminator = vpr_type.ty_constructor.name().to_str();

        vir::with_vcx(|vcx| {
            let self_expr = vcx.mk_local_ex(Self::sized_self_decl(vcx));

            let is_this_type = vcx.mk_adt_discriminator_expr(self_expr, discriminator);

            let sized_impl_idn = TraitEnc::trait_impl_idn(vcx, SIZED_TRAIT_NAME, SIZED_ARGS);

            let check = match task_key.sizedness {
                Sizedness::Sized => Some(is_this_type),
                Sizedness::Unsized => None,
                Sizedness::Dependent(dep_ty) => Some(
                    Self::sizedness_for_dependent(
                        vcx,
                        deps,
                        sized_impl_idn,
                        vpr_type,
                        task_key.params,
                        self_expr,
                        dep_ty,
                    )
                    .map_or(
                        is_this_type,
                        |extra_check| vir::expr! {vcx; (is_this_type) && (extra_check) },
                    ),
                ),
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

            let sized_impl_idn = TraitEnc::trait_impl_idn(vcx, SIZED_TRAIT_NAME, SIZED_ARGS);
            let sized_impl_unknown_idn =
                TraitEnc::trait_unknown_impl_idn(vcx, SIZED_TRAIT_NAME, SIZED_ARGS);

            let self_decl = Self::sized_self_decl(vcx);
            let self_expr = vcx.mk_local_ex(self_decl);

            let unknown_check = {
                let is_unknown =
                    vcx.mk_adt_discriminator_expr(self_expr, TyConstructorEnc::UNKNOWN_TYPE_NAME);
                let unknown_id = TyConstructorEnc::unknown_type_id_accessor(vcx).call()(self_expr);

                let unknown_impls = sized_impl_unknown_idn.call()(unknown_id, &[], &[]);

                vir::expr! {vcx; (is_unknown) && (unknown_impls) }
            };

            checks.push(unknown_check);

            let sized_impl_fun = vcx.mk_function(
                sized_impl_idn,
                (&[self_decl], &[]),
                &[],
                &[],
                None,
                Some(vcx.mk_disj(&checks)),
            );
            program.add_function(sized_impl_fun);

            let sized_impl_unknown_fun =
                vcx.mk_domain_function(sized_impl_unknown_idn, false, None);

            let sized_domain = vcx.mk_domain(
                TraitEnc::trait_domain_idn(vcx, SIZED_TRAIT_NAME),
                &[],
                &[],
                vcx.alloc_slice(&[sized_impl_unknown_fun]),
                None,
            );
            program.add_domain(sized_domain);
        });
    }
}

impl SizedTraitEnc {
    fn sized_self_decl<'vir>(vcx: &'vir vir::VirCtxt<'vir>) -> vir::LocalDecl<'vir, vir::TyVal> {
        vcx.mk_local_decl("Self$0", vir::TYPE_TYVAL)
    }

    /// Check if we need an extra sizedness check as a result of the sizedness dependency
    fn sizedness_for_dependent<'vir>(
        vcx: &'vir vir::VirCtxt<'vir>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir, SizedTraitEnc>,
        sized_impl_idn: vir::FunctionIdn<'vir, (vir::ManyTyVal, vir::ManyCSnap), vir::Bool>,
        vpr_type: TyConstructorEncOutputRef<'vir>,
        ty_ctx: GParams<'vir>,
        self_expr: vir::Expr<'vir, vir::TyVal>,
        depneded_on: ty::Ty<'vir>,
    ) -> Option<vir::ExprBool<'vir>> {
        match depneded_on.kind() {
            ty::TyKind::Param(param) => {
                let accessor = vpr_type.ty_param_accessors[param.index as usize];
                let param_ty = accessor.call()(self_expr);
                // We know that in reality `Sized` only has the `Self` type parameter
                let inner_sized_check = sized_impl_idn.call()(&[param_ty], &[]);
                Some(inner_sized_check)
            }
            ty::TyKind::Alias(ty::AliasTyKind::Projection, alias_ty) => {
                let tcx = vcx.tcx();

                let is_forced_sized = tcx.item_bounds(alias_ty.def_id)
                            .instantiate_identity()
                            .iter()
                            .any(|clause| {
                                matches!(clause.kind().skip_binder(),
                                    ty::ClauseKind::Trait(p) if Some(p.def_id()) == tcx.lang_items().sized_trait()
                                )
                            });

                if is_forced_sized {
                    // This projection is forced to be `Sized` by its own bounds, so we don't need an
                    // extra check
                    return None;
                }

                let trait_def = alias_ty.trait_def_id(tcx);
                let trait_ = deps.require_ref::<TraitEnc>(trait_def).unwrap();
                let projection_fun = trait_.fns.assoc_types[&alias_ty.def_id];

                let ty_params = deps.require_dep::<GenericParamsEnc>(ty_ctx).unwrap();
                let args = deps
                    .require_dep::<GArgsTyEnc>(GArgs::new(ty_ctx, alias_ty.args))
                    .unwrap();

                let projection = projection_fun(args.get_ty(), args.get_const());

                let inner_sized_check = sized_impl_idn.call()(&[projection], &[]);

                // Introduce let-bindings for the generics of the type
                // NOTE: There won't be any name collisions as user defined ADTs cannot
                // have a generic called `Self`
                let with_consts_bound = ty_params.const_decls().iter().enumerate().rfold(
                    inner_sized_check,
                    |expr, (i, decl)| {
                        let accessor = vpr_type.const_param_accessors[i];
                        vcx.mk_let_expr(decl, accessor.call()(self_expr), expr)
                    },
                );
                let with_tys_bound = ty_params.ty_decls().iter().enumerate().rfold(
                    with_consts_bound,
                    |expr, (i, decl)| {
                        let accessor = vpr_type.ty_param_accessors[i];
                        vcx.mk_let_expr(decl, accessor.call()(self_expr), expr)
                    },
                );

                Some(with_tys_bound)
            }
            _ => panic!("Unsupported dependent sizedness for {depneded_on:?}"),
        }
    }
}
