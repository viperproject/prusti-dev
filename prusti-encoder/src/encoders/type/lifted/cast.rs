use prusti_rustc_interface::middle::ty;
use task_encoder::{TaskEncoder, TaskEncoderDependencies, TaskEncoderError, EncodeFullResult};
use vir::{FunctionIdent, MethodIdent, StmtGen, UnknownArity, VirCtxt};

use super::{
    casters::{
        CastType, CastTypeImpure, CastTypePure, Casters, CastersEncOutputRef,
    },
    generic::LiftedGeneric,
    rust_ty_cast::{RustTyCastersEnc, RustTyGenericCastEncOutput},
    ty::LiftedTy,
};

#[derive(Copy, Hash, PartialEq, Eq, Clone, Debug)]
pub struct CastArgs<'tcx> {
    /// The argument expected by a function or data constructor signature
    pub expected: ty::Ty<'tcx>,
    /// The type of the expression passed to the function or data constructor
    pub actual: ty::Ty<'tcx>,
}

impl<'tcx> CastArgs<'tcx> {
    pub fn reversed(&self) -> CastArgs<'tcx> {
        CastArgs {
            expected: self.actual,
            actual: self.expected,
        }
    }
}

/// Holds the necessary information to cast to a generic or concrete
/// version.
#[derive(Copy, Clone)]
pub struct Cast<'vir, T> {
    /// Either a function or method identifier that can be applied to perform
    /// the cast
    cast_applicator: T,

    /// Type arguments that will be passed to the cast applicator
    ty_args: &'vir [LiftedTy<'vir, LiftedGeneric<'vir>>],
}

pub type PureCast<'vir> = Cast<'vir, FunctionIdent<'vir, UnknownArity<'vir>>>;

impl<'vir, T> Cast<'vir, T> {
    pub fn new(
        cast_applicator: T,
        ty_args: &'vir [LiftedTy<'vir, LiftedGeneric<'vir>>],
    ) -> Cast<'vir, T> {
        Cast {
            cast_applicator,
            ty_args,
        }
    }

    pub fn map_applicator<U>(self, f: impl FnOnce(T) -> U) -> Cast<'vir, U> {
        Cast {
            cast_applicator: f(self.cast_applicator),
            ty_args: self.ty_args,
        }
    }
}

impl<'vir> Cast<'vir, FunctionIdent<'vir, UnknownArity<'vir>>> {
    /// Returns the result of the cast
    pub fn apply<Curr: 'vir, Next: 'vir>(
        &self,
        vcx: &'vir VirCtxt,
        expr: vir::ExprGen<'vir, Curr, Next>,
    ) -> vir::ExprGen<'vir, Curr, Next> {
        self.cast_applicator.apply(
            vcx,
            &std::iter::once(expr)
                .chain(self.ty_args.iter().map(|t| t.expr(vcx)))
                .collect::<Vec<_>>(),
        )
    }
}

#[derive(Clone)]
pub enum GenericCastOutputRef<'vir, T> {
    NoCast,
    Cast(Cast<'vir, T>),
}

impl<'vir> GenericCastOutputRef<'vir, FunctionIdent<'vir, UnknownArity<'vir>>> {
    pub fn apply_cast_if_necessary<Curr: 'vir, Next: 'vir>(
        &self,
        vcx: &'vir VirCtxt<'_>,
        expr: vir::ExprGen<'vir, Curr, Next>,
    ) -> vir::ExprGen<'vir, Curr, Next> {
        match self {
            GenericCastOutputRef::NoCast => expr,
            GenericCastOutputRef::Cast(Cast {
                cast_applicator,
                ty_args,
            }) => cast_applicator.apply(
                vcx,
                &std::iter::once(expr)
                    .chain(ty_args.iter().map(|t| t.expr(vcx)))
                    .collect::<Vec<_>>(),
            ),
        }
    }
}

impl<'vir> GenericCastOutputRef<'vir, MethodIdent<'vir, UnknownArity<'vir>>> {
    pub fn apply_cast_if_necessary<Curr: 'vir, Next: 'vir>(
        &self,
        vcx: &'vir VirCtxt<'_>,
        expr: vir::ExprGen<'vir, Curr, Next>,
    ) -> Option<StmtGen<'vir, Curr, Next>> {
        match self {
            GenericCastOutputRef::NoCast => None,
            GenericCastOutputRef::Cast(Cast {
                cast_applicator,
                ty_args,
            }) => Some(
                vcx.alloc(
                    cast_applicator.apply(
                        vcx,
                        &std::iter::once(expr)
                            .chain(ty_args.iter().map(|t| t.expr(vcx)))
                            .collect::<Vec<_>>(),
                    ),
                ),
            ),
        }
    }
}

impl<'vir, T: Copy> GenericCastOutputRef<'vir, T> {
    pub fn cast_function(&self) -> Option<Cast<'vir, T>> {
        match self {
            GenericCastOutputRef::NoCast => None,
            GenericCastOutputRef::Cast(f) => Some(*f),
        }
    }
}

impl<'vir, T> task_encoder::OutputRefAny for GenericCastOutputRef<'vir, T> {}

/// Returns necessary data to support casting the generic Viper representation
/// of a Rust expression to its concrete type, or vice versa, for function
/// applications. It takes as input a [`CastArgs`] struct, which contains the
/// parameter type a function expects, and the type of the argument. If the
/// function expects the concrete version of the type and the argument is
/// generic, it returns a function to casts the generic expression to its
/// concrete version. Likewise, if the function expects the generic version of
/// the type and the argument is concrete, it returns a function to cast the
/// concrete expression to its generic version. Otherwise, no cast is necessary
/// and it returns [`PureGenericCastOutputRef::NoCast`].
///
/// The type parameter `T` is used to choose whether a pure or impure cast
/// should be encoded, it should be instantiated with either [`CastTypePure`] or
/// [`CastTypeImpure`].
pub struct CastToEnc<T>(std::marker::PhantomData<T>);

impl<T: CastType + 'static> CastToEnc<T>
where
    Self: TaskEncoder,
    RustTyCastersEnc<T>: for<'vir> TaskEncoder<
        TaskDescription<'vir> = ty::Ty<'vir>,
        OutputFullLocal<'vir> = RustTyGenericCastEncOutput<'vir, Casters<'vir, T>>,
    >,
    TaskEncoderError<RustTyCastersEnc<T>>: Sized,
{
    fn encode_cast<'vir>(
        task_key: CastArgs<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> GenericCastOutputRef<'vir, T::CastApplicator<'vir>> {
        let expected_is_param = matches!(task_key.expected.kind(), ty::Param(_));
        let actual_is_param = matches!(task_key.actual.kind(), ty::Param(_));
        if expected_is_param == actual_is_param {
            GenericCastOutputRef::NoCast
        } else if actual_is_param {
            // expected is concrete type, `actual` should be concretized
            let generic_cast = deps
                .require_local::<RustTyCastersEnc<T>>(task_key.expected)
                .unwrap();
            if let CastersEncOutputRef::Casters { make_concrete, .. } = generic_cast.cast {
                GenericCastOutputRef::Cast(Cast::new(
                    T::to_concrete_applicator(make_concrete),
                    generic_cast.ty_args,
                ))
            } else {
                unreachable!()
            }
        } else {
            // expected is generic type, `actual` should be be made generic
            let generic_cast = deps
                .require_local::<RustTyCastersEnc<T>>(task_key.actual)
                .unwrap();
            if let CastersEncOutputRef::Casters { make_generic, .. } = generic_cast.cast {
                GenericCastOutputRef::Cast(Cast::new(T::to_generic_applicator(make_generic), generic_cast.ty_args))
            } else {
                unreachable!()
            }
        }
    }
}

impl TaskEncoder for CastToEnc<CastTypePure> {
    task_encoder::encoder_cache!(CastToEnc<CastTypePure>);
    type TaskDescription<'tcx> = CastArgs<'tcx>;
    type OutputRef<'vir> = GenericCastOutputRef<'vir, FunctionIdent<'vir, UnknownArity<'vir>>>;
    type OutputFullLocal<'vir> = ();
    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        let output_ref = Self::encode_cast(*task_key, deps);
        deps.emit_output_ref(*task_key, output_ref)?;
        Ok(((), ()))
    }
}

impl TaskEncoder for CastToEnc<CastTypeImpure> {
    task_encoder::encoder_cache!(CastToEnc<CastTypeImpure>);
    type TaskDescription<'tcx> = CastArgs<'tcx>;
    type OutputRef<'vir> = GenericCastOutputRef<'vir, MethodIdent<'vir, UnknownArity<'vir>>>;
    type OutputFullLocal<'vir> = ();
    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        let output_ref = Self::encode_cast(*task_key, deps);
        deps.emit_output_ref(*task_key, output_ref)?;
        Ok(((), ()))
    }
}
