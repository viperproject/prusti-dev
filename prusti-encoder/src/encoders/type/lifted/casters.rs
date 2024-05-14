use std::marker::PhantomData;

use task_encoder::{TaskEncoder, TaskEncoderDependencies, EncodeFullResult};
use vir::{Arity, CallableIdent, FunctionIdent, MethodIdent, TypeData, UnaryArity, UnknownArity};

use crate::encoders::{
    domain::DomainEnc, lifted::ty_constructor::TyConstructorEnc, most_generic_ty::MostGenericTy,
    GenericEnc, PredicateEnc,
};

use super::{
    generic::{LiftedGeneric, LiftedGenericEnc},
    ty::LiftedTy,
};

pub struct CastTypePure;

impl CastTypePure {
    pub fn cast_to_generic_if_necessary<'vir, Curr, Next>(
        casters: &Casters<'vir, Self>,
        vcx: &'vir vir::VirCtxt<'_>,
        snap: vir::ExprGen<'vir, Curr, Next>,
    ) -> vir::ExprGen<'vir, Curr, Next> {
        match casters {
            CastFunctionsOutputRef::AlreadyGeneric => snap,
            CastFunctionsOutputRef::Casters { make_generic, .. } => make_generic.apply(vcx, [snap]),
        }
    }
}

impl CastType for CastTypePure {
    type CastOutput<'vir, Curr: 'vir, Next: 'vir> = vir::ExprGen<'vir, Curr, Next>;
    type ToGeneric<'vir> = MakeGenericCastFunction<'vir>;
    type ToConcrete<'vir> = MakeConcreteCastFunction<'vir>;
    type CastApplicator<'vir> = vir::FunctionIdent<'vir, UnknownArity<'vir>>;

    fn cast_to_concrete_if_possible<'vir, Curr, Next>(
        casters: &Casters<'vir, Self>,
        vcx: &'vir vir::VirCtxt<'_>,
        snap: vir::ExprGen<'vir, Curr, Next>,
        ty_args: &'vir [LiftedTy<'vir, LiftedGeneric<'vir>>],
    ) -> Self::CastOutput<'vir, Curr, Next> {
        match casters {
            CastFunctionsOutputRef::AlreadyGeneric => snap,
            CastFunctionsOutputRef::Casters { make_concrete, .. } => make_concrete.apply(
                vcx,
                &std::iter::once(snap)
                    .chain(ty_args.iter().map(|t| t.expr(vcx)))
                    .collect::<Vec<_>>(),
            ),
        }
    }

    fn to_concrete_applicator(to_concrete: Self::ToConcrete<'_>) -> Self::CastApplicator<'_> {
        to_concrete
    }

    fn to_generic_applicator(to_generic: Self::ToGeneric<'_>) -> Self::CastApplicator<'_> {
        to_generic.as_unknown_arity()
    }
}

pub struct CastTypeImpure;

pub struct ImpureCastStmts<'vir, Curr, Next> {
    pub apply_cast_stmt: vir::StmtGen<'vir, Curr, Next>,
    pub unapply_cast_stmt: vir::StmtGen<'vir, Curr, Next>,
}

impl<'vir, Curr, Next> ImpureCastStmts<'vir, Curr, Next> {
    fn new(
        apply_cast_stmt: vir::StmtGen<'vir, Curr, Next>,
        unapply_cast_stmt: vir::StmtGen<'vir, Curr, Next>,
    ) -> Self {
        ImpureCastStmts {
            apply_cast_stmt,
            unapply_cast_stmt,
        }
    }
}

impl CastType for CastTypeImpure {
    type CastOutput<'vir, Curr: 'vir, Next: 'vir> = Option<ImpureCastStmts<'vir, Curr, Next>>;

    type ToGeneric<'vir> = vir::MethodIdent<'vir, UnknownArity<'vir>>;

    type ToConcrete<'vir> = vir::MethodIdent<'vir, UnknownArity<'vir>>;

    type CastApplicator<'vir> = vir::MethodIdent<'vir, UnknownArity<'vir>>;

    fn cast_to_concrete_if_possible<'vir, Curr, Next>(
        casters: &CastersEncOutputRef<Self::ToGeneric<'vir>, Self::ToConcrete<'vir>>,
        vcx: &'vir vir::VirCtxt<'_>,
        snap: vir::ExprGen<'vir, Curr, Next>,
        ty_args: &'vir [LiftedTy<'vir, LiftedGeneric<'vir>>],
    ) -> Self::CastOutput<'vir, Curr, Next> {
        match casters {
            CastersEncOutputRef::AlreadyGeneric => None,
            CastersEncOutputRef::Casters {
                make_concrete,
                make_generic,
            } => {
                let args = vcx.alloc_slice(
                    &std::iter::once(snap)
                        .chain(ty_args.iter().map(|t| t.expr(vcx)))
                        .collect::<Vec<_>>(),
                );
                Some(ImpureCastStmts::new(
                    vcx.alloc(make_concrete.apply(vcx, args)),
                    vcx.alloc(make_generic.apply(vcx, args)),
                ))
            }
        }
    }

    fn to_concrete_applicator(to_concrete: Self::ToConcrete<'_>) -> Self::CastApplicator<'_> {
        to_concrete
    }

    fn to_generic_applicator(to_generic: Self::ToGeneric<'_>) -> Self::CastApplicator<'_> {
        to_generic
    }
}
pub trait CastType
where
    Self: Sized,
{
    /// The shape of an applied cast, either an expression (for a pure cast)
    /// or a statement (for an impure cast)
    type CastOutput<'vir, Curr: 'vir, Next: 'vir>;

    /// The type of the VIR construct (either a function or method identifier)
    /// that can be applied to perform a cast from the concrete to the generic
    /// version
    type ToGeneric<'vir>;

    /// The type of the VIR construct (either a function or method identifier)
    /// that can be applied to perform a cast from the generic to the concrete
    /// version
    type ToConcrete<'vir>;

    /// The type of the VIR construct (either a function or method identifier)
    /// that can be applied to perform a cast in either direction. Effectively
    /// this is type that subsumes both`ToGeneric` and `ToConcrete`.
    type CastApplicator<'vir>;

    fn to_concrete_applicator(to_concrete: Self::ToConcrete<'_>) -> Self::CastApplicator<'_>;

    fn to_generic_applicator(to_generic: Self::ToGeneric<'_>) -> Self::CastApplicator<'_>;

    fn cast_to_concrete_if_possible<'vir, Curr, Next>(
        casters: &Casters<'vir, Self>,
        vcx: &'vir vir::VirCtxt<'_>,
        snap: vir::ExprGen<'vir, Curr, Next>,
        ty_args: &'vir [LiftedTy<'vir, LiftedGeneric<'vir>>],
    ) -> Self::CastOutput<'vir, Curr, Next>;
}

#[allow(type_alias_bounds)]
pub type Casters<'vir, T: CastType> = CastersEncOutputRef<T::ToGeneric<'vir>, T::ToConcrete<'vir>>;

#[derive(Clone)]
pub enum CastersEncOutputRef<G, C> {
    Casters { make_generic: G, make_concrete: C },
    AlreadyGeneric,
}

impl<G: Copy, C: Copy> CastersEncOutputRef<G, C> {
    pub fn expect_casters(&self) -> (G, C) {
        match self {
            CastersEncOutputRef::AlreadyGeneric => panic!(),
            CastersEncOutputRef::Casters {
                make_generic,
                make_concrete,
            } => (*make_generic, *make_concrete),
        }
    }
}

pub type CastFunctionsOutputRef<'vir> =
    CastersEncOutputRef<MakeGenericCastFunction<'vir>, MakeConcreteCastFunction<'vir>>;

pub type CastMethodsOutputRef<'vir> = CastersEncOutputRef<
    MethodIdent<'vir, UnknownArity<'vir>>,
    MethodIdent<'vir, UnknownArity<'vir>>,
>;

impl<G: Copy, C> CastersEncOutputRef<G, C> {
    pub fn generic_option(&self) -> Option<G> {
        match self {
            CastersEncOutputRef::AlreadyGeneric => None,
            CastersEncOutputRef::Casters { make_generic, .. } => Some(*make_generic),
        }
    }
}

pub type MakeGenericCastFunction<'vir> = FunctionIdent<'vir, UnaryArity<'vir>>;
pub type MakeConcreteCastFunction<'vir> = FunctionIdent<'vir, UnknownArity<'vir>>;

/// Takes as input the most generic version (c.f. [`MostGenericTy`]) of a Rust
/// type, and generates functions to convert the generic Viper representation of
/// a Rust expression with that type to its concrete representation, and
/// vice-versa. If the provided type is generic, it does nothing, returning
/// [`CastFunctionsOutputRef::AlreadyGeneric`].
pub struct CastersEnc<T>(PhantomData<T>);

impl<C, G> task_encoder::OutputRefAny for CastersEncOutputRef<C, G> {}

/// The list of cast functions, if any
type GenericCastOutput<'vir> = &'vir [vir::Function<'vir>];

impl TaskEncoder for CastersEnc<CastTypePure> {
    task_encoder::encoder_cache!(CastersEnc<CastTypePure>);

    type TaskDescription<'vir> = MostGenericTy<'vir>;
    type OutputRef<'vir> = CastFunctionsOutputRef<'vir>;
    type OutputFullLocal<'vir> = GenericCastOutput<'vir>;
    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        ty: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        if ty.is_generic() {
            deps.emit_output_ref(*ty, CastFunctionsOutputRef::AlreadyGeneric);
            return Ok((&[], ()));
        }
        vir::with_vcx(|vcx| {
            let domain_ref = deps.require_ref::<DomainEnc>(*ty).unwrap();
            let generic_ref = deps.require_ref::<GenericEnc>(()).unwrap();
            let self_ty = domain_ref.domain.apply(vcx, []);
            let base_name = &domain_ref.base_name;
            let ty_constructor = deps
                .require_ref::<TyConstructorEnc>(*ty)
                .unwrap()
                .ty_constructor;

            let make_generic_arg_tys = [self_ty];
            let make_generic_ident = FunctionIdent::new(
                vir::vir_format_identifier!(vcx, "make_generic_s_{base_name}"),
                UnaryArity::new(vcx.alloc(make_generic_arg_tys)),
                generic_ref.param_snapshot,
            );

            let make_concrete_ty_params = ty
                .generics()
                .into_iter()
                .map(|g| deps.require_ref::<LiftedGenericEnc>(*g).unwrap())
                .collect::<Vec<_>>();

            let make_concrete_arg_tys = std::iter::once(generic_ref.param_snapshot)
                .chain(make_concrete_ty_params.iter().map(|t| t.ty()))
                .collect::<Vec<_>>();

            let make_concrete_ident = FunctionIdent::new(
                vir::vir_format_identifier!(vcx, "make_concrete_s_{base_name}"),
                UnknownArity::new(vcx.alloc(make_concrete_arg_tys)),
                self_ty,
            );

            deps.emit_output_ref(
                *ty,
                CastFunctionsOutputRef::Casters {
                    make_generic: make_generic_ident,
                    make_concrete: make_concrete_ident,
                },
            );
            let make_generic_arg = vcx.mk_local_decl("self", self_ty);
            let make_generic_expr = vcx.mk_local_ex(make_generic_arg.name, make_generic_arg.ty);

            let make_generic_arg_decls = vcx.alloc_slice(&[make_generic_arg]);

            let make_concrete_ty_param_exprs = make_concrete_ty_params
                .iter()
                .map(|t| t.expr(vcx))
                .collect::<Vec<_>>();

            let make_generic_result = vcx.mk_result(generic_ref.param_snapshot);

            // Type parameters obtained from the snapshot-encoded value of the type,
            let ty_params_from_snap = ty
                .generics()
                .iter()
                .enumerate()
                .map(|(idx, _)| domain_ref.ty_param_from_snap(vcx, idx, make_generic_expr))
                .collect::<Vec<_>>();

            // Asserts that the type of `param` is equal to the ty constructor
            // applied to type arguments `args`
            let mk_type_spec = |param, args| {
                let lifted_param_snap_ty = generic_ref.param_type_function.apply(vcx, [param]);
                vcx.mk_eq_expr(lifted_param_snap_ty, ty_constructor.apply(vcx, args))
            };

            let make_generic = vcx.mk_function(
                make_generic_ident.name_str(),
                make_generic_arg_decls,
                generic_ref.param_snapshot,
                &[],
                vcx.alloc_slice(&[
                    mk_type_spec(make_generic_result, &ty_params_from_snap),
                    vcx.mk_eq_expr(
                        make_concrete_ident.apply(
                            vcx,
                            &std::iter::once(make_generic_result)
                                .chain(ty_params_from_snap.iter().copied())
                                .collect::<Vec<_>>(),
                        ),
                        make_generic_expr,
                    ),
                ]),
                None,
            );

            let make_concrete_snap_arg_decl = vcx.mk_local_decl("snap", generic_ref.param_snapshot);
            let make_concrete_arg_decls = vcx.alloc_slice(
                &std::iter::once(make_concrete_snap_arg_decl)
                    .chain(make_concrete_ty_params.iter().map(|t| t.decl()))
                    .collect::<Vec<_>>(),
            );

            let make_concrete_pre = mk_type_spec(
                vcx.mk_local_ex(
                    make_concrete_snap_arg_decl.name,
                    make_concrete_snap_arg_decl.ty,
                ),
                &make_concrete_ty_param_exprs,
            );

            let make_concrete_post = vcx.mk_eq_expr(
                make_generic_ident.apply(vcx, [vcx.mk_result(self_ty)]),
                vcx.mk_local_ex(
                    make_concrete_snap_arg_decl.name,
                    make_concrete_snap_arg_decl.ty,
                ),
            );

            let make_concrete = vcx.mk_function(
                make_concrete_ident.name_str(),
                make_concrete_arg_decls,
                self_ty,
                vcx.alloc_slice(&[make_concrete_pre]),
                vcx.alloc_slice(&[make_concrete_post]),
                None,
            );

            Ok((vcx.alloc_slice(&[make_generic, make_concrete]), ()))
        })
    }
}

impl TaskEncoder for CastersEnc<CastTypeImpure> {
    task_encoder::encoder_cache!(CastersEnc<CastTypeImpure>);

    type TaskDescription<'vir> = MostGenericTy<'vir>;
    type OutputRef<'vir> = CastMethodsOutputRef<'vir>;
    type OutputFullLocal<'vir> = &'vir [vir::Method<'vir>];
    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        ty: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        if ty.is_generic() {
            deps.emit_output_ref(*ty, CastMethodsOutputRef::AlreadyGeneric);
            return Ok((&[], ()));
        }
        vir::with_vcx(|vcx| {
            let predicate_ref = deps.require_ref::<PredicateEnc>(*ty).unwrap();
            let generic_ref = deps.require_ref::<GenericEnc>(()).unwrap();
            let base_name = predicate_ref.ref_to_pred.name();
            let ty_constructor = deps.require_ref::<TyConstructorEnc>(*ty).unwrap();

            let arg_tys = vcx.alloc_slice(
                &std::iter::once(&TypeData::Ref)
                    .chain(ty_constructor.arity().args().iter().copied())
                    .collect::<Vec<_>>(),
            );

            let make_generic_ident = MethodIdent::new(
                vir::vir_format_identifier!(vcx, "make_generic_{base_name}"),
                UnknownArity::new(arg_tys),
            );

            let make_concrete_ident = MethodIdent::new(
                vir::vir_format_identifier!(vcx, "make_concrete_{base_name}"),
                UnknownArity::new(arg_tys),
            );

            deps.emit_output_ref(
                *ty,
                CastMethodsOutputRef::Casters {
                    make_generic: make_generic_ident,
                    make_concrete: make_concrete_ident,
                },
            );
            let (make_generic_pure, _) = deps
                .require_ref::<CastersEnc<CastTypePure>>(*ty)
                .unwrap()
                .expect_casters();
            let self_decl = vcx.mk_local_decl("self", &TypeData::Ref);
            let self_expr = vcx.mk_local_ex(self_decl.name, self_decl.ty);
            let arg_ty_decls = ty_constructor
                .arity()
                .args()
                .iter()
                .enumerate()
                .map(|(idx, ty)| vcx.mk_local_decl(vcx.alloc_str(&format!("T{}", idx)), ty))
                .collect::<Vec<_>>();
            let arg_ty_exprs = arg_ty_decls
                .iter()
                .map(|decl| vcx.mk_local_ex(decl.name, decl.ty))
                .collect::<Vec<_>>();
            let decls = vcx.alloc_slice(
                &[self_decl]
                    .into_iter()
                    .chain(arg_ty_decls)
                    .collect::<Vec<_>>(),
            );

            let concrete_predicate_args = &std::iter::once(self_expr)
                .chain(arg_ty_exprs.iter().copied())
                .collect::<Vec<_>>();

            let concrete_predicate =
                predicate_ref
                    .ref_to_pred
                    .apply(vcx, concrete_predicate_args, None);

            let concrete_snap = predicate_ref
                .ref_to_snap
                .apply(vcx, concrete_predicate_args);

            let concrete_predicate = vcx.mk_predicate_app_expr(concrete_predicate);

            let lifted_ty_expr = ty_constructor.ty_constructor.apply(vcx, &arg_ty_exprs);

            let generic_predicate =
                generic_ref
                    .ref_to_pred
                    .apply(vcx, [self_expr, lifted_ty_expr], None);

            let generic_snap = generic_ref
                .ref_to_snap
                .apply(vcx, [self_expr, lifted_ty_expr]);

            let generic_predicate = vcx.mk_predicate_app_expr(generic_predicate);

            let make_generic_same_snap = vcx.mk_eq_expr(
                vcx.mk_old_expr(make_generic_pure.apply(vcx, [concrete_snap])),
                generic_snap,
            );

            let make_concrete_same_snap = vcx.mk_eq_expr(
                vcx.mk_old_expr(generic_snap),
                make_generic_pure.apply(vcx, [concrete_snap]),
            );

            let make_generic = vcx.mk_method(
                make_generic_ident,
                decls,
                &[],
                vcx.alloc_slice(&[concrete_predicate]),
                vcx.alloc_slice(&[generic_predicate, make_generic_same_snap]),
                None,
            );

            let make_concrete = vcx.mk_method(
                make_concrete_ident,
                decls,
                &[],
                vcx.alloc_slice(&[generic_predicate]),
                vcx.alloc_slice(&[concrete_predicate, make_concrete_same_snap]),
                None,
            );
            Ok((vcx.alloc_slice(&[make_generic, make_concrete]), ()))
        })
    }
}
