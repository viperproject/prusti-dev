use std::marker::PhantomData;

use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{CallableIdn, FunctionIdn, MethodIdn};

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
        snap: vir::ExprGenSnap<'vir, Curr, Next>,
        ty_args: &'vir [LiftedTy<'vir, LiftedGeneric<'vir>>],
    ) -> vir::ExprGenPSnap<'vir, Curr, Next> {
        use vir::CastType;
        match casters {
            CastFunctionsOutputRef::AlreadyGeneric => snap.downcast_ty(),
            CastFunctionsOutputRef::Casters { make_generic, .. } => make_generic.call()(
                snap.downcast_ty(),
                &ty_args.iter().map(|t| t.expr(vcx)).collect::<Vec<_>>(),
            ),
        }
    }
}

impl CastType for CastTypePure {
    type CastArgs<'vir, Curr: 'vir, Next: 'vir> = vir::ExprGenSnap<'vir, Curr, Next>;
    type CastOutput<'vir, Curr: 'vir, Next: 'vir> = vir::ExprGenSnap<'vir, Curr, Next>;
    type ToGeneric<'vir> = MakeGenericCastFunction<'vir>;
    type ToConcrete<'vir> = MakeConcreteCastFunction<'vir>;
    type CastApplicator<'vir> = FunctionIdn<'vir, (vir::Snap, vir::ManyTyVal), vir::Snap>;

    fn cast_to_concrete_if_possible<'vir, Curr, Next>(
        casters: &Casters<'vir, Self>,
        vcx: &'vir vir::VirCtxt<'_>,
        snap: Self::CastArgs<'vir, Curr, Next>,
        ty_args: &'vir [LiftedTy<'vir, LiftedGeneric<'vir>>],
    ) -> Self::CastOutput<'vir, Curr, Next> {
        use vir::CastType;
        match casters {
            CastFunctionsOutputRef::AlreadyGeneric => snap,
            CastFunctionsOutputRef::Casters { make_concrete, .. } => make_concrete.call()(
                snap.downcast_ty(),
                &ty_args.iter().map(|t| t.expr(vcx)).collect::<Vec<_>>(),
            ).upcast_ty(),
        }
    }

    fn to_concrete_applicator(to_concrete: Self::ToConcrete<'_>) -> Self::CastApplicator<'_> {
        use vir::CastType;
        let (a, b) = to_concrete.arity();
        to_concrete.cast_ty((a.upcast_ty(), b))
    }

    fn to_generic_applicator(to_generic: Self::ToGeneric<'_>) -> Self::CastApplicator<'_> {
        use vir::CastType;
        let (a, b) = to_generic.arity();
        to_generic.cast_ty((a.upcast_ty(), b))
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
    type CastArgs<'vir, Curr: 'vir, Next: 'vir> = vir::ExprGenRef<'vir, Curr, Next>;

    type CastOutput<'vir, Curr: 'vir, Next: 'vir> = Option<ImpureCastStmts<'vir, Curr, Next>>;

    type ToGeneric<'vir> = vir::MethodIdn<'vir, (vir::Ref, vir::ManyTyVal)>;

    type ToConcrete<'vir> = vir::MethodIdn<'vir, (vir::Ref, vir::ManyTyVal)>;

    type CastApplicator<'vir> = vir::MethodIdn<'vir, (vir::Ref, vir::ManyTyVal)>;

    fn cast_to_concrete_if_possible<'vir, Curr, Next>(
        casters: &CastersEncOutputRef<Self::ToGeneric<'vir>, Self::ToConcrete<'vir>>,
        vcx: &'vir vir::VirCtxt<'_>,
        snap: Self::CastArgs<'vir, Curr, Next>,
        ty_args: &'vir [LiftedTy<'vir, LiftedGeneric<'vir>>],
    ) -> Self::CastOutput<'vir, Curr, Next> {
        match casters {
            CastersEncOutputRef::AlreadyGeneric => None,
            CastersEncOutputRef::Casters {
                make_concrete,
                make_generic,
            } => {
                let args = ty_args.iter().map(|t| t.expr(vcx)).collect::<Vec<_>>();
                Some(ImpureCastStmts::new(
                    vcx.alloc(vir::StmtGenData::new(
                        vcx.alloc(make_concrete.call()(snap, &args)),
                    )),
                    vcx.alloc(vir::StmtGenData::new(
                        vcx.alloc(make_generic.call()(snap, &args)),
                    )),
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
    type CastArgs<'vir, Curr: 'vir, Next: 'vir>;

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
        args: Self::CastArgs<'vir, Curr, Next>,
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
    MethodIdn<'vir, (vir::Ref, vir::ManyTyVal)>,
    MethodIdn<'vir, (vir::Ref, vir::ManyTyVal)>,
>;

impl<G: Copy, C> CastersEncOutputRef<G, C> {
    pub fn generic_option(&self) -> Option<G> {
        match self {
            CastersEncOutputRef::AlreadyGeneric => None,
            CastersEncOutputRef::Casters { make_generic, .. } => Some(*make_generic),
        }
    }
}

pub type MakeGenericCastFunction<'vir> =
    FunctionIdn<'vir, (vir::CSnap, vir::ManyTyVal), vir::PSnap>;
pub type MakeConcreteCastFunction<'vir> =
    FunctionIdn<'vir, (vir::PSnap, vir::ManyTyVal), vir::CSnap>;

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
            deps.emit_output_ref(*ty, CastFunctionsOutputRef::AlreadyGeneric)?;
            return Ok((&[], ()));
        }
        vir::with_vcx(|vcx| {
            use vir::CastType;
            let domain_ref = deps.require_ref::<DomainEnc>(*ty)?;
            let generic_ref = deps.require_ref::<GenericEnc>(())?;
            let self_ty = (domain_ref.domain)().downcast_ty();
            let base_name = &domain_ref.base_name;
            let ty_constructor = deps.require_ref::<TyConstructorEnc>(*ty)?;

            let ty_params = ty
                .generics()
                .into_iter()
                .map(|g| deps.require_ref::<LiftedGenericEnc>(*g))
                .collect::<Result<Vec<_>, _>>()?;

            let arg_tys = ty_params.iter().map(|t| t.ty()).collect::<Vec<_>>();
            let arg_tys = vcx.alloc_slice(&arg_tys);
            let make_generic_ident = FunctionIdn::new(
                vir::vir_format_identifier!(vcx, "make_generic_s_{base_name}"),
                (self_ty, arg_tys),
                generic_ref.param_snapshot,
            );

            let make_concrete_ident = FunctionIdn::new(
                vir::vir_format_identifier!(vcx, "make_concrete_s_{base_name}"),
                (generic_ref.param_snapshot, arg_tys),
                self_ty,
            );

            deps.emit_output_ref(
                *ty,
                CastFunctionsOutputRef::Casters {
                    make_generic: make_generic_ident,
                    make_concrete: make_concrete_ident,
                },
            )?;
            let make_generic_arg = vcx.mk_local_decl("self", self_ty);
            let make_generic_expr = vcx.mk_local_ex(make_generic_arg.name, make_generic_arg.ty);

            let ty_params_vec = ty_params.iter().map(|t| t.decl()).collect::<Vec<_>>();

            let make_concrete_ty_param_exprs =
                ty_params.iter().map(|t| t.expr(vcx)).collect::<Vec<_>>();

            let make_generic_result = vcx.mk_result(generic_ref.param_snapshot);

            // Type parameters obtained from the snapshot-encoded value of the type,
            let ty_params_from_snap = ty
                .generics()
                .iter()
                .enumerate()
                .map(|(idx, _)| ty_constructor.ty_param_from_snap(vcx, idx, make_generic_expr))
                .collect::<Vec<_>>();

            // Asserts that the type of `param` is equal to the ty constructor
            // applied to type arguments `args`
            let mk_type_spec = |param, args| {
                let lifted_param_snap_ty = (generic_ref.param_type_function)(param);
                vcx.mk_eq_expr(lifted_param_snap_ty, (ty_constructor.ty_constructor)(args))
            };

            let make_generic = vcx.mk_function(
                make_generic_ident,
                (make_generic_arg, &ty_params_vec),
                &[],
                vcx.alloc_slice(&[
                    mk_type_spec(make_generic_result, &ty_params_from_snap),
                    vcx.mk_eq_expr(
                        make_concrete_ident(make_generic_result, &ty_params_from_snap),
                        make_generic_expr,
                    ),
                ]),
                None,
                None,
            );

            let make_concrete_snap_arg_decl = vcx.mk_local_decl("snap", generic_ref.param_snapshot);
            let make_concrete_snap_arg_expr = vcx.mk_local_ex(
                make_concrete_snap_arg_decl.name,
                make_concrete_snap_arg_decl.ty,
            );

            let make_concrete_pre =
                mk_type_spec(make_concrete_snap_arg_expr, &make_concrete_ty_param_exprs);

            let arg_ty_exprs = ty_params
                .iter()
                .map(|t| vcx.mk_local_ex(t.decl().name, t.decl().ty))
                .collect::<Vec<_>>();
            let make_concrete_post = vcx.mk_eq_expr(
                make_generic_ident(vcx.mk_result(self_ty), &arg_ty_exprs),
                make_concrete_snap_arg_expr,
            );

            let make_concrete = vcx.mk_function(
                make_concrete_ident,
                (make_concrete_snap_arg_decl, &ty_params_vec),
                vcx.alloc_slice(&[make_concrete_pre]),
                vcx.alloc_slice(&[make_concrete_post]),
                None,
                None,
            );

            Ok((vcx.alloc_slice(&[make_generic, make_concrete]), ()))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for output in Self::all_outputs_local() {
            for function in output {
                program.add_function(function);
            }
        }
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
            deps.emit_output_ref(*ty, CastMethodsOutputRef::AlreadyGeneric)?;
            return Ok((&[], ()));
        }
        vir::with_vcx(|vcx| {
            use vir::CastType;
            let predicate_ref = deps.require_ref::<PredicateEnc>(*ty)?;
            let generic_ref = deps.require_ref::<GenericEnc>(())?;
            let base_name = predicate_ref.ref_to_pred.name();
            let ty_constructor = deps.require_ref::<TyConstructorEnc>(*ty)?;

            let arg_tys = vcx.alloc_slice(&ty_constructor.args().collect::<Vec<_>>());

            let make_generic_ident = MethodIdn::new(
                vir::vir_format_identifier!(vcx, "make_generic_{base_name}"),
                (vir::TYPE_REF, arg_tys),
            );

            let make_concrete_ident = MethodIdn::new(
                vir::vir_format_identifier!(vcx, "make_concrete_{base_name}"),
                (vir::TYPE_REF, arg_tys),
            );

            deps.emit_output_ref(
                *ty,
                CastMethodsOutputRef::Casters {
                    make_generic: make_generic_ident,
                    make_concrete: make_concrete_ident,
                },
            )?;
            let (make_generic_pure, _) = deps
                .require_ref::<CastersEnc<CastTypePure>>(*ty)?
                .expect_casters();
            let self_decl = vcx.mk_local_decl("self", vir::TYPE_REF);
            let self_expr = vcx.mk_local_ex(self_decl.name, self_decl.ty);
            let arg_ty_decls = ty_constructor
                .args()
                .enumerate()
                .map(|(idx, ty)| vcx.mk_local_decl(vcx.alloc_str(&format!("T{}", idx)), ty))
                .collect::<Vec<_>>();
            let arg_ty_exprs = arg_ty_decls
                .iter()
                .map(|decl| vcx.mk_local_ex(decl.name, decl.ty))
                .collect::<Vec<_>>();
            let decls = (self_decl, arg_ty_decls.as_slice());

            let concrete_predicate = (predicate_ref.ref_to_pred)(self_expr, &arg_ty_exprs)(None);

            let concrete_snap = (predicate_ref.ref_to_snap)(self_expr, &arg_ty_exprs).downcast_ty();

            let concrete_predicate = vcx.mk_predicate_app_expr(concrete_predicate);

            let lifted_ty_expr = (ty_constructor.ty_constructor)(&arg_ty_exprs);

            let generic_predicate = (generic_ref.ref_to_pred)(self_expr, lifted_ty_expr)(None);

            let generic_snap = (generic_ref.ref_to_snap)(self_expr, lifted_ty_expr);

            let generic_predicate = vcx.mk_predicate_app_expr(generic_predicate);

            let make_generic_same_snap = vcx.mk_eq_expr(
                vcx.mk_old_expr(make_generic_pure(concrete_snap, &arg_ty_exprs)),
                generic_snap,
            );

            let make_concrete_same_snap = vcx.mk_eq_expr(
                vcx.mk_old_expr(generic_snap),
                make_generic_pure(concrete_snap, &arg_ty_exprs),
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

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for output in Self::all_outputs_local() {
            for method in output {
                program.add_method(method);
            }
        }
    }
}
