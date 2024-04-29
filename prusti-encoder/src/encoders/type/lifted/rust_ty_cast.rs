use prusti_rustc_interface::middle::ty;
use task_encoder::TaskEncoder;
use vir::with_vcx;

use crate::encoders::most_generic_ty::extract_type_params;

use super::{cast::PureCast, cast_functions::{CastFunctionsEnc, CastFunctionsOutputRef}, generic::LiftedGeneric, ty::{EncodeGenericsAsLifted, LiftedTy, LiftedTyEnc}};

/// Generates Viper functions to cast between generic and non-generic Viper
/// representations of a Rust value. See [`CastFunctionsEnc`] for more details.
pub struct RustTyGenericCastEnc;

#[derive(Clone)]
pub struct RustTyGenericCastEncOutput<'vir> {
    pub cast: CastFunctionsOutputRef<'vir>,
    // Type arguments required by the cast function
    pub ty_args: &'vir [LiftedTy<'vir, LiftedGeneric<'vir>>],
}

impl<'vir> RustTyGenericCastEncOutput<'vir> {
    /// Returns the data to facilitate a cast from the concrete representation to
    /// the generic representation, if the input type wasn't already a generic.
    pub fn to_generic_cast(&self) -> Option<PureCast<'vir>> {
        self.cast
            .generic_option()
            .map(|f| PureCast::new(f.as_unknown_arity(), &[]))
    }

    /// See [`CastFunctionsOutputRef::cast_to_concrete_if_possible`].
    pub fn cast_to_concrete_if_possible<'tcx, Curr, Next>(
        &self,
        vcx: &'vir vir::VirCtxt<'tcx>,
        snap: vir::ExprGen<'vir, Curr, Next>,
    ) -> vir::ExprGen<'vir, Curr, Next> {
        self.cast
            .cast_to_concrete_if_possible(vcx, snap, self.ty_args)
    }

    /// See `GenericCastOutputRef::cast_to_generic_if_necessary`.
    pub fn cast_to_generic_if_necessary<'tcx, Curr, Next>(
        &self,
        vcx: &'vir vir::VirCtxt<'tcx>,
        snap: vir::ExprGen<'vir, Curr, Next>,
    ) -> vir::ExprGen<'vir, Curr, Next> {
        self.cast.cast_to_generic_if_necessary(vcx, snap)
    }
}

impl<'vir> task_encoder::OutputRefAny for RustTyGenericCastEncOutput<'vir> {}

impl TaskEncoder for RustTyGenericCastEnc {
    task_encoder::encoder_cache!(RustTyGenericCastEnc);

    type TaskDescription<'vir> = ty::Ty<'vir>;

    type OutputFullLocal<'vir> = RustTyGenericCastEncOutput<'vir>;

    type TaskKey<'tcx> = Self::TaskDescription<'tcx>;

    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'tcx: 'vir, 'vir>(
        task_key: &Self::TaskKey<'tcx>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir>,
    ) -> Result<
        (
            Self::OutputFullLocal<'vir>,
            Self::OutputFullDependency<'vir>,
        ),
        (
            Self::EncodingError,
            Option<Self::OutputFullDependency<'vir>>,
        ),
    > {
        with_vcx(|vcx| {
            deps.emit_output_ref::<RustTyGenericCastEnc>(*task_key, ());
            let (generic_ty, args) = extract_type_params(vcx.tcx(), *task_key);
            let cast = deps.require_ref::<CastFunctionsEnc>(generic_ty).unwrap();
            let ty_args = args
                .iter()
                .map(|a| {
                    deps.require_local::<LiftedTyEnc<EncodeGenericsAsLifted>>(*a)
                        .unwrap()
                })
                .collect::<Vec<_>>();
            Ok((
                RustTyGenericCastEncOutput {
                    cast,
                    ty_args: vcx.alloc_slice(&ty_args),
                },
                (),
            ))
        })
    }
}
