use std::marker::PhantomData;

use prusti_rustc_interface::middle::ty;
use task_encoder::{TaskEncoder, TaskEncoderError, EncodeFullResult};
use vir::with_vcx;

use crate::encoders::most_generic_ty::{extract_type_params, MostGenericTy};

use super::{
    cast::Cast,
    casters::{
        CastFunctionsOutputRef, CastMethodsOutputRef, CastType, CastTypeImpure, CastTypePure,
        Casters, CastersEnc, ImpureCastStmts, MakeGenericCastFunction,
    },
    generic::LiftedGeneric,
    ty::{EncodeGenericsAsLifted, LiftedTy, LiftedTyEnc},
};

/// Generates Viper functions to cast between generic and non-generic Viper
/// representations of a Rust value. See [`CastersEnc`] for more details. The
/// type parameter `T` indicates the cast type, it should be either
/// [`CastTypePure`] or [`CastTypeImpure`].
pub struct RustTyCastersEnc<T>(PhantomData<T>);

#[derive(Clone)]
pub struct RustTyGenericCastEncOutput<'vir, T> {
    pub cast: T,
    // Type arguments required by the cast function
    pub ty_args: &'vir [LiftedTy<'vir, LiftedGeneric<'vir>>],
}

impl<'vir> RustTyGenericCastEncOutput<'vir, CastFunctionsOutputRef<'vir>> {
    /// Returns the data to facilitate a cast from the concrete representation to
    /// the generic representation, if the input type wasn't already a generic.
    pub fn to_generic_cast(&self) -> Option<Cast<'vir, MakeGenericCastFunction<'vir>>> {
        self.cast.generic_option().map(|f| Cast::new(f, &[]))
    }
}

impl<'vir> RustTyGenericCastEncOutput<'vir, CastMethodsOutputRef<'vir>> {
    pub fn cast_to_concrete_if_possible<'tcx, Curr, Next>(
        &self,
        vcx: &'vir vir::VirCtxt<'tcx>,
        snap: vir::ExprGen<'vir, Curr, Next>,
    ) -> Option<ImpureCastStmts<'vir, Curr, Next>> {
        CastTypeImpure::cast_to_concrete_if_possible(&self.cast, vcx, snap, self.ty_args)
    }
}

impl<'vir> RustTyGenericCastEncOutput<'vir, CastFunctionsOutputRef<'vir>> {
    pub fn cast_to_concrete_if_possible<'tcx, Curr, Next>(
        &self,
        vcx: &'vir vir::VirCtxt<'tcx>,
        snap: vir::ExprGen<'vir, Curr, Next>,
    ) -> vir::ExprGen<'vir, Curr, Next> {
        CastTypePure::cast_to_concrete_if_possible(&self.cast, vcx, snap, self.ty_args)
    }

    pub fn cast_to_generic_if_necessary<'tcx, Curr, Next>(
        &self,
        vcx: &'vir vir::VirCtxt<'tcx>,
        snap: vir::ExprGen<'vir, Curr, Next>,
    ) -> vir::ExprGen<'vir, Curr, Next> {
        CastTypePure::cast_to_generic_if_necessary(&self.cast, vcx, snap, self.ty_args)
    }
}

impl<'vir, T> task_encoder::OutputRefAny for RustTyGenericCastEncOutput<'vir, T> {}

impl<T: CastType + 'static> RustTyCastersEnc<T>
where
    Self: TaskEncoder,
    CastersEnc<T>: for<'vir> TaskEncoder<
        TaskDescription<'vir> = MostGenericTy<'vir>,
        OutputRef<'vir> = Casters<'vir, T>,
    >,
    TaskEncoderError<CastersEnc<T>>: Sized,
{
    fn encode<'vir>(
        task_key: &ty::Ty<'vir>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir, Self>,
    ) -> RustTyGenericCastEncOutput<'vir, Casters<'vir, T>> {
        with_vcx(|vcx| {
            let (generic_ty, args) = extract_type_params(vcx.tcx(), *task_key);
            let cast = deps.require_ref::<CastersEnc<T>>(generic_ty).unwrap();
            let ty_args = args
                .iter()
                .map(|a| {
                    deps.require_local::<LiftedTyEnc<EncodeGenericsAsLifted>>(*a)
                        .unwrap()
                })
                .collect::<Vec<_>>();
            RustTyGenericCastEncOutput {
                cast,
                ty_args: vcx.alloc_slice(&ty_args),
            }
        })
    }
}

impl TaskEncoder for RustTyCastersEnc<CastTypePure> {
    task_encoder::encoder_cache!(RustTyCastersEnc<CastTypePure>);

    type TaskDescription<'vir> = ty::Ty<'vir>;

    type OutputFullLocal<'vir> = RustTyGenericCastEncOutput<'vir, CastFunctionsOutputRef<'vir>>;

    type TaskKey<'tcx> = Self::TaskDescription<'tcx>;

    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        Ok((Self::encode(task_key, deps), ()))
    }
}

impl TaskEncoder for RustTyCastersEnc<CastTypeImpure> {
    task_encoder::encoder_cache!(RustTyCastersEnc<CastTypeImpure>);

    type TaskDescription<'vir> = ty::Ty<'vir>;

    type OutputFullLocal<'vir> = RustTyGenericCastEncOutput<'vir, CastMethodsOutputRef<'vir>>;

    type TaskKey<'tcx> = Self::TaskDescription<'tcx>;

    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        Ok((Self::encode(task_key, deps), ()))
    }
}
