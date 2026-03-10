use crate::{
    TaskEncoder,
    encoders::ty::{
        RustTy,
        generics::{GParams, r#trait::TraitEnc, trait_impls::TraitImplEnc},
        lifted::TyConstructorEnc,
    },
};
use prusti_rustc_interface::middle::{ty, ty::Upcast};

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
        assert!(task_key.erased_ty.is_some());
        deps.emit_output_ref(*task_key, ())?;

        if task_key.erased_ty.is_none() {}

        vir::with_vcx(|vcx| {
            let sizedness = sizedness_for_ty(vcx.tcx(), task_key.erased_ty.unwrap());
            let check = match sizedness {
                Sizedness::Unsized => None,
                Sizedness::Sized => Some(Self::sizedness_check(
                    vcx,
                    deps,
                    task_key.params,
                    task_key.erased_ty.unwrap(),
                    None,
                )),
                Sizedness::Dependent(dep_ty) => Some(Self::sizedness_check(
                    vcx,
                    deps,
                    task_key.params,
                    task_key.erased_ty.unwrap(),
                    Some(dep_ty),
                )),
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
        vcx.mk_local_decl("Self$0_trait", vir::TYPE_TYVAL)
    }

    fn sizedness_check<'vir>(
        vcx: &'vir vir::VirCtxt<'vir>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir, SizedTraitEnc>,
        impl_ctx: GParams<'vir>,
        impl_ty: ty::Ty<'vir>,
        depended_on: Option<ty::Ty<'vir>>,
    ) -> vir::ExprBool<'vir> {
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
