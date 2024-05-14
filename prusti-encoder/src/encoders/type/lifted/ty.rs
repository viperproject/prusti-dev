use std::marker::PhantomData;

use prusti_rustc_interface::middle::ty::{self, ParamTy, TyKind};
use task_encoder::{TaskEncoder, EncodeFullResult};
use vir::{with_vcx, FunctionIdent, UnknownArity};

use crate::encoders::{
    lifted::{
        generic::{LiftedGeneric, LiftedGenericEnc},
        ty_constructor::TyConstructorEnc,
    },
    most_generic_ty::extract_type_params,
};

/// Representation of a Rust type as a Viper expression. Generics are
/// represented with values of type `T`. In the usual case `T` should be
/// [`LiftedGeneric`], but in some cases alternative types are useful (see
/// usages in [`crate::encoders::domain::DomainEnc`])
#[derive(Clone, Copy, Debug)]
pub enum LiftedTy<'vir, T> {
    /// Uninstantiated generic type parameter
    Generic(T),

    /// Non-generic type
    Instantiated {
        /// Type constructor function e.g. corresponding to `Option`, `Result`, etc
        ty_constructor: FunctionIdent<'vir, UnknownArity<'vir>>,

        /// Arguments to the type constructor e.g. `T` in `Option<T>`
        args: &'vir [LiftedTy<'vir, T>],
    },
}

impl<'vir, 'tcx, T: Copy> LiftedTy<'vir, T> {
    pub fn map<U: Copy>(
        &self,
        vcx: &'vir vir::VirCtxt<'tcx>,
        f: &mut dyn FnMut(T) -> U,
    ) -> LiftedTy<'vir, U> {
        match self {
            LiftedTy::Instantiated {
                ty_constructor,
                args,
            } => {
                let args: Vec<LiftedTy<'vir, U>> =
                    args.iter().map(|a| a.map(vcx, f)).collect::<Vec<_>>();
                LiftedTy::Instantiated {
                    ty_constructor: *ty_constructor,
                    args: vcx.alloc_slice(&args),
                }
            }
            LiftedTy::Generic(g) => LiftedTy::Generic(f(*g)),
        }
    }

    pub fn expect_generic(&self) -> T {
        match self {
            LiftedTy::Generic(g) => *g,
            _ => panic!("Expected generic type"),
        }
    }
}

impl<'vir, 'tcx, Curr, Next> LiftedTy<'vir, vir::ExprGen<'vir, Curr, Next>> {
    pub fn arg_exprs(&self, vcx: &'vir vir::VirCtxt<'tcx>) -> Vec<vir::ExprGen<'vir, Curr, Next>> {
        match self {
            LiftedTy::Generic(g) => vec![*g],
            LiftedTy::Instantiated { args, .. } => args.iter().map(|a| a.expr(vcx)).collect(),
        }
    }

    pub fn expr(&self, vcx: &'vir vir::VirCtxt<'tcx>) -> vir::ExprGen<'vir, Curr, Next> {
        match self {
            LiftedTy::Generic(g) => g,
            LiftedTy::Instantiated {
                ty_constructor,
                args,
            } => ty_constructor.apply(vcx, &args.iter().map(|a| a.expr(vcx)).collect::<Vec<_>>()),
        }
    }
}

impl<'vir, 'tcx> LiftedTy<'vir, LiftedGeneric<'vir>> {
    pub fn arg_exprs<Curr, Next>(
        &self,
        vcx: &'vir vir::VirCtxt<'tcx>,
    ) -> Vec<vir::ExprGen<'vir, Curr, Next>> {
        self.map(vcx, &mut |g| g.expr(vcx)).arg_exprs(vcx)
    }

    pub fn expr<Curr, Next>(
        &self,
        vcx: &'vir vir::VirCtxt<'tcx>,
    ) -> vir::ExprGen<'vir, Curr, Next> {
        self.map(vcx, &mut |g| g.expr(vcx)).expr(vcx)
    }
}

pub struct EncodeGenericsAsLifted;
pub struct EncodeGenericsAsParamTy;

/// Encodes the Viper representation of a Rust type ([`LiftedTy`]). The type
/// parameter `T` determines how Rust generic types are encoded; different
/// encoder implementations are used for different types of generic types. The
/// type parameter enables different implementations to also differ in their
/// result types.
pub struct LiftedTyEnc<T>(PhantomData<T>);

/// This encoder represents Rust generics as [`LiftedGeneric`] values. This is
/// suitable for cases where the generic is represented in Viper as an argument
/// of type `Type` (the usual case).
impl TaskEncoder for LiftedTyEnc<EncodeGenericsAsLifted> {
    task_encoder::encoder_cache!(LiftedTyEnc<EncodeGenericsAsLifted>);

    type TaskDescription<'tcx> = ty::Ty<'tcx>;

    type TaskKey<'tcx> = Self::TaskDescription<'tcx>;

    type OutputFullLocal<'vir> = LiftedTy<'vir, LiftedGeneric<'vir>>;

    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        with_vcx(|vcx| {
            let result = deps
                .require_local::<LiftedTyEnc<EncodeGenericsAsParamTy>>(*task_key)?;
            let result = result.map(vcx, &mut |g| {
                deps.require_ref::<LiftedGenericEnc>(g).unwrap()
            });
            Ok((result, ()))
        })
    }
}

/// Generics are represented using  Rust [`ParamTy`] values. This allows for
/// deferring the encoding of the generic type to a later point.
impl TaskEncoder for LiftedTyEnc<EncodeGenericsAsParamTy> {
    task_encoder::encoder_cache!(LiftedTyEnc<EncodeGenericsAsParamTy>);

    type TaskDescription<'tcx> = ty::Ty<'tcx>;

    type TaskKey<'tcx> = Self::TaskDescription<'tcx>;

    type OutputFullLocal<'vir> = LiftedTy<'vir, ParamTy>;

    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        with_vcx(|vcx| {
            if let TyKind::Param(p) = task_key.kind() {
                return Ok((LiftedTy::Generic(*p), ()));
            }
            let (ty_constructor, args) = extract_type_params(vcx.tcx(), *task_key);
            let ty_constructor = deps
                .require_ref::<TyConstructorEnc>(ty_constructor)?
                .ty_constructor;
            let args = args
                .into_iter()
                .map(|ty| deps.require_local::<Self>(ty).unwrap())
                .collect::<Vec<_>>();
            let result = LiftedTy::Instantiated {
                ty_constructor,
                args: vcx.alloc_slice(&args),
            };
            Ok((result, ()))
        })
    }
}
