use crate::{
    TaskEncoder,
    encoders::ty::{
        RustTy,
        generics::{
            GParams, GenericParams, GenericParamsEnc, r#trait::TraitEnc, trait_impls::TraitImplEnc,
        },
        lifted::TyConstructorEnc,
    },
};
use prusti_rustc_interface::middle::{ty, ty::Upcast};
use task_encoder::EncodeFullError;
use vir::vir_format_identifier;

pub struct SizedTraitEnc;

impl TaskEncoder for SizedTraitEnc {
    task_encoder::encoder_cache!(SizedTraitEnc);
    type TaskDescription<'vir> = RustTy<'vir>;

    type OutputFullLocal<'vir> = (
        // This will be unfortunately copied with every type that the `Sized` encoder is called
        // with
        <TraitEnc as TaskEncoder>::OutputRef<'vir>,
        GenericParams<'vir>,
        Option<vir::ExprBool<'vir>>,
    );

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
            let sized_did = vcx.tcx().lang_items().sized_trait().unwrap();
            let sized_trait = deps.require_ref::<TraitEnc>(sized_did)?;

            let trait_generics = {
                let params = TraitEnc::trait_params(sized_did);
                deps.require_dep::<GenericParamsEnc>(params)?
            };

            let ty = task_key.erased_ty_for_special_traits();
            let sizedness = sizedness_for_ty(vcx.tcx(), ty);
            let check = match sizedness {
                Sizedness::Unsized => None,
                Sizedness::Sized => {
                    Some(Self::sizedness_check(vcx, deps, task_key.params, ty, None)?)
                }
                Sizedness::Dependent(dep_ty) => Some(Self::sizedness_check(
                    vcx,
                    deps,
                    task_key.params,
                    ty,
                    Some(dep_ty),
                )?),
            };

            Ok(((sized_trait, trait_generics, check), ()))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        let outputs = Self::all_outputs_local_no_errors();
        let Some((sized_trait, sized_generics, _)) = outputs.first() else {
            return;
        };
        vir::with_vcx(|vcx| {
            let mut checks: Vec<_> = Self::all_outputs_local_no_errors()
                .into_iter()
                .filter_map(|(.., check)| check)
                .collect();

            let sized_impl_fun = sized_trait.impl_fun;
            let sized_impl_for_unknown_fun = sized_trait.impl_for_unknown_fun;

            let unknown_type_check = {
                let self_expr = sized_generics.ty_exprs()[0];

                let is_unknown =
                    vcx.mk_adt_discriminator_expr(self_expr, TyConstructorEnc::UNKNOWN_TYPE_NAME);
                let extracted_id =
                    TyConstructorEnc::unknown_type_id_accessor(vcx).call()(self_expr);

                let unknown_impls = sized_impl_for_unknown_fun.call()(
                    extracted_id,
                    &sized_generics.ty_exprs()[1..],
                    sized_generics.const_exprs(),
                );

                vir::expr! {vcx; (is_unknown) && (unknown_impls) }
            };

            checks.push(unknown_type_check);

            let ensures = vcx.mk_eq_expr(vcx.mk_result(vir::TYPE_BOOL), vcx.mk_disj(&checks));

            let sized_impl_fun = vcx.mk_function(
                sized_impl_fun,
                (sized_generics.ty_decls(), sized_generics.const_decls()),
                &[],
                vcx.alloc_slice(&[ensures]),
                Some(&vir::DecreasesGenData::Star),
                None,
            );

            program.add_function(sized_impl_fun);

            let sized_impl_unknown_fun =
                vcx.mk_domain_function(sized_impl_for_unknown_fun, false, None);

            let sized_domain = vcx.mk_domain(
                vir_format_identifier!(vcx, "trait_{}", sized_trait.trait_name),
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
    fn sizedness_check<'vir>(
        vcx: &'vir vir::VirCtxt<'vir>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir, SizedTraitEnc>,
        impl_ctx: GParams<'vir>,
        impl_ty: ty::Ty<'vir>,
        depended_on: Option<ty::Ty<'vir>>,
    ) -> Result<vir::ExprBool<'vir>, EncodeFullError<'vir, SizedTraitEnc>> {
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
