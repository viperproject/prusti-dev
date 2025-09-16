use std::marker::PhantomData;

use prusti_rustc_interface::middle::ty::{self, ParamTy, TyKind};
use task_encoder::{EncodeFullResult, TaskEncoder};
use vir::{with_vcx, FunctionIdn, CastType};

use crate::encoders::{
    ConstEnc, r#const::ConstEncTask, lifted::{
        LiftedConstEnc, generic::{LiftedGeneric, LiftedGenericEnc}, ty_constructor::TyConstructorEnc
    }, most_generic_ty::MostGenericTyEnc,
};

use super::generic::LiftedGenericEncTask;

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
        ty_constructor: FunctionIdn<'vir, vir::ManyTyVal, vir::TyVal>,

        /// Arguments to the type constructor e.g. `T` in `Option<T>`
        args: &'vir [LiftedTy<'vir, T>],
    },

    /// An arbitrary expression, used to represent const generics.
    Expr(vir::ExprTyVal<'vir>),
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
            LiftedTy::Expr(e) => LiftedTy::Expr(e),
        }
    }

    pub fn expect_generic(&self) -> T {
        match self {
            LiftedTy::Generic(g) => *g,
            _ => panic!("Expected generic type"),
        }
    }
}

impl<'vir, 'tcx, Curr, Next> LiftedTy<'vir, vir::ExprGenTyVal<'vir, Curr, Next>> {
    pub fn arg_exprs(
        &self,
        vcx: &'vir vir::VirCtxt<'tcx>,
    ) -> Vec<vir::ExprGenTyVal<'vir, Curr, Next>> {
        match self {
            LiftedTy::Generic(g) => vec![*g],
            LiftedTy::Instantiated { args, .. } => args.iter().map(|a| a.expr(vcx)).collect(),
            LiftedTy::Expr(..) => Vec::new(),
        }
    }

    pub fn expr(&self, vcx: &'vir vir::VirCtxt<'tcx>) -> vir::ExprGenTyVal<'vir, Curr, Next> {
        match self {
            LiftedTy::Generic(g) => g,
            LiftedTy::Instantiated {
                ty_constructor,
                args,
            } => ty_constructor.call()(&args.iter().map(|a| a.expr(vcx)).collect::<Vec<_>>()),
            LiftedTy::Expr(e) => unsafe { std::mem::transmute(e.lift::<!>()) }, // TODO: should not need a transmute for this (the problem is that we don't know whether `Curr` in this context is or isn't `!`)
        }
    }
}

impl<'vir, 'tcx> LiftedTy<'vir, LiftedGeneric<'vir>> {
    pub fn arg_exprs<Curr, Next>(
        &self,
        vcx: &'vir vir::VirCtxt<'tcx>,
    ) -> Vec<vir::ExprGenTyVal<'vir, Curr, Next>> {
        self.map(vcx, &mut |g| g.expr(vcx)).arg_exprs(vcx)
    }

    pub fn expr<Curr, Next>(
        &self,
        vcx: &'vir vir::VirCtxt<'tcx>,
    ) -> vir::ExprGenTyVal<'vir, Curr, Next> {
        self.map(vcx, &mut |g| g.expr(vcx)).expr(vcx)
    }
}

pub struct EncodeGenericsAsLifted;
pub struct EncodeGenericsAsParamTy;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum LiftedTyEncTask<'vir> {
    Ty(ty::Ty<'vir>),
    Const(ty::Const<'vir>, ty::Ty<'vir>),
}

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

    type TaskDescription<'tcx> = LiftedTyEncTask<'tcx>;

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
            let result = deps.require_local::<LiftedTyEnc<EncodeGenericsAsParamTy>>(*task_key)?;
            let result = result.map(vcx, &mut |g| {
                deps.require_ref::<LiftedGenericEnc>(LiftedGenericEncTask::Param(g)).unwrap()
            });
            Ok((result, ()))
        })
    }
}

/// Generics are represented using  Rust [`ParamTy`] values. This allows for
/// deferring the encoding of the generic type to a later point.
impl TaskEncoder for LiftedTyEnc<EncodeGenericsAsParamTy> {
    task_encoder::encoder_cache!(LiftedTyEnc<EncodeGenericsAsParamTy>);

    type TaskDescription<'tcx> = LiftedTyEncTask<'tcx>;

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
        with_vcx(|vcx| match task_key {
            LiftedTyEncTask::Ty(ty) => {
                if let TyKind::Param(p) = ty.kind() {
                    return Ok((LiftedTy::Generic(*p), ()));
                }
                let (generic_ty, args) = deps.require_local::<MostGenericTyEnc>(*ty)?;
                let ty_constructor = deps
                    .require_ref::<TyConstructorEnc>(generic_ty)?
                    .ty_constructor;
                let args = args
                    .into_iter()
                    .map(|ty| deps.require_local::<Self>(LiftedTyEncTask::Ty(ty)).unwrap())
                    .collect::<Vec<_>>();
                Ok((LiftedTy::Instantiated {
                    ty_constructor,
                    args: vcx.alloc_slice(&args),
                }, ()))
            }
            LiftedTyEncTask::Const(const_, ty) => {
                let snap = deps.require_local::<ConstEnc>(ConstEncTask::Ty {
                    const_: *const_,
                    ty: *ty,
                })?;
                let lifted_const = deps.require_ref::<LiftedConstEnc>(*ty)?;
                Ok((LiftedTy::Expr((lifted_const.const_type_function)(snap.upcast_ty())), ()))
            }
        })
    }
}
