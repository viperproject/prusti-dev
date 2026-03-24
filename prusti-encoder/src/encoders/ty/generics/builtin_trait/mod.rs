use crate::encoders::ty::{
    RustTy,
    generics::{GParams, GenericParams, GenericParamsEnc, r#trait::TraitEnc},
    lifted::TyConstructorEnc,
};
use prusti_rustc_interface::{middle::ty, span::def_id::DefId};

use task_encoder::{CacheRef, EncodeFullError, TaskEncoder};
use vir::vir_format_identifier;

pub mod sized_trait;
pub mod tuple_trait;

pub type SizedTraitEnc = BuiltinTraitEnc<sized_trait::SizedTrait>;
pub type TupleTraitEnc = BuiltinTraitEnc<tuple_trait::TupleTrait>;

/// Trait that must be implemented by all builtin trait markers.
///
/// This trait defines the interface that marker types must implement to work with
/// `SpecialTraitEnc<T>`. The marker types should be zero-sized structs that are `'static`.
trait BuiltinTrait: 'static {
    /// Returns the DefId of this builtin trait.
    fn def_id() -> DefId;

    /// Returns the expression representing whether the given type implements this trait.
    ///
    /// # Returns
    ///
    /// - `Ok(Some(expr))` - The type implements the trait; `expr` is a boolean expression
    ///   that evaluates to true when the trait is implemented
    /// - `Ok(None)` - The type definitely does not implement this trait
    /// - `Err(_)` - An error occurred during encoding
    fn does_impl<'vir>(
        deps: &mut task_encoder::TaskEncoderDependencies<'vir, BuiltinTraitEnc<Self>>,
        ctx: GParams<'vir>,
        ty: ty::Ty<'vir>,
    ) -> Result<Option<vir::ExprBool<'vir>>, EncodeFullError<'vir, BuiltinTraitEnc<Self>>>
    where
        Self: Sized;

    /// Provides access to the encoder cache for this builtin trait.
    ///
    /// This should be implemented using the `task_encoder::encoder_cache!` macro.
    fn with_cache<'vir, F, R>(f: F) -> R
    where
        Self: Sized,
        F: FnOnce(&'vir CacheRef<'vir, BuiltinTraitEnc<Self>>) -> R;
}

/// Generic wrapper for encoding builtin traits.
///
/// This struct wraps a marker type `T` that implements `BuiltinTrait` and provides
/// a `TaskEncoder` implementation for it. The wrapper handles the common encoding
/// logic while delegating trait-specific decisions to the marker type.
pub struct BuiltinTraitEnc<T>(std::marker::PhantomData<T>);

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash)]
pub enum BuiltinTraitEncTask<'a> {
    Activate,
    Encode(RustTy<'a>),
}

#[derive(Clone, Debug)]
pub struct TraitData<'a> {
    trait_: <TraitEnc as TaskEncoder>::OutputRef<'a>,
    trait_generics: GenericParams<'a>,
}
impl<'a> TraitData<'a> {
    fn new(
        trait_: <TraitEnc as TaskEncoder>::OutputRef<'a>,
        trait_generics: GenericParams<'a>,
    ) -> Box<Self> {
        Box::new(Self {
            trait_,
            trait_generics,
        })
    }
}

#[derive(Clone, Debug)]
pub enum BuiltinTraitEncOutput<'a> {
    Activated(Box<TraitData<'a>>),
    TypeCheck(Option<vir::ExprBool<'a>>),
}

impl<T: BuiltinTrait> TaskEncoder for BuiltinTraitEnc<T> {
    const ENCODER_NAME: &'static str = "builtin trait encoder";
    // Need to delegate to the `BuiltinTrait` to implement the `with_cache` due to issues
    // described in `task_encoder::encoder_cache!`
    fn with_cache<'vir, F, R>(f: F) -> R
    where
        F: FnOnce(&'vir task_encoder::CacheRef<'vir, Self>) -> R,
        T: 'vir,
    {
        T::with_cache(f)
    }

    type TaskDescription<'vir> = BuiltinTraitEncTask<'vir>;
    type OutputFullLocal<'vir> = BuiltinTraitEncOutput<'vir>;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir, Self>,
    ) -> task_encoder::EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        match task_key {
            BuiltinTraitEncTask::Activate => {
                let trait_did = T::def_id();
                let trait_ = deps.require_ref::<TraitEnc>(trait_did)?;

                let trait_generics = {
                    let params = TraitEnc::trait_params(trait_did);
                    deps.require_dep::<GenericParamsEnc>(params)?
                };
                Ok((
                    (BuiltinTraitEncOutput::Activated(TraitData::new(trait_, trait_generics))),
                    (),
                ))
            }
            BuiltinTraitEncTask::Encode(rust_ty) => {
                assert!(!rust_ty.specifics.is_param());

                let ty = rust_ty.erased_ty_for_buitin_traits();

                let check = T::does_impl(deps, rust_ty.params, ty)?;

                Ok(((BuiltinTraitEncOutput::TypeCheck(check)), ()))
            }
        }
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        let outputs = Self::all_outputs_local_no_errors(program);

        let mut trait_info = None;
        let mut checks = Vec::new();

        for output in outputs {
            match output {
                BuiltinTraitEncOutput::Activated(box data) => {
                    trait_info = Some((data.trait_, data.trait_generics));
                }
                BuiltinTraitEncOutput::TypeCheck(Some(check)) => {
                    checks.push(check);
                }
                _ => {}
            }
        }
        let Some((trait_, trait_generics)) = trait_info else {
            return;
        };

        vir::with_vcx(|vcx| {
            let trait_impl_fun = trait_.impl_fun;
            let trait_impl_for_unknown_fun = trait_.impl_for_unknown_fun;

            let unknown_type_check = {
                let self_expr = trait_generics.ty_exprs()[0];

                let is_unknown =
                    vcx.mk_adt_discriminator_expr(self_expr, TyConstructorEnc::UNKNOWN_TYPE_NAME);
                let extracted_id =
                    TyConstructorEnc::unknown_type_id_accessor(vcx).call()(self_expr);

                let unknown_impls = trait_impl_for_unknown_fun.call()(
                    extracted_id,
                    &trait_generics.ty_exprs()[1..],
                    trait_generics.const_exprs(),
                );

                vir::expr! {vcx; (is_unknown) && (unknown_impls) }
            };

            checks.push(unknown_type_check);

            let ensures = vcx.mk_eq_expr(vcx.mk_result(vir::TYPE_BOOL), vcx.mk_disj(&checks));

            let trait_impl_fun = vcx.mk_function(
                trait_impl_fun,
                (trait_generics.ty_decls(), trait_generics.const_decls()),
                &[],
                vcx.alloc_slice(&[ensures]),
                Some(&vir::DecreasesGenData::Star),
                None,
            );

            program.add_function(trait_impl_fun);

            let trait_impl_unknown_fun =
                vcx.mk_domain_function(trait_impl_for_unknown_fun, false, None);

            let trait_domain = vcx.mk_domain(
                vir_format_identifier!(vcx, "trait_{}", trait_.trait_name),
                &[],
                &[],
                vcx.alloc_slice(&[trait_impl_unknown_fun]),
                None,
            );
            program.add_domain(trait_domain);
        });
    }
}
