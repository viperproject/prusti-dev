use std::{fmt::Debug, marker::PhantomData};

use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{CallableIdn, FunctionIdn, MethodIdn};

use crate::encoders::{
    Impure, Pure, Purity,
    ty::{RustTy, impure::TyImpureEnc, lifted::ty_constructor::TyConstructorEnc, pure::TyPureEnc},
};

use super::GenericParamsEnc;

#[derive(Debug, Clone, Copy)]
pub(super) struct GArgCasters<'vir, P: PurityCasters> {
    pub(super) make_generic: P::MakeGeneric<'vir>,
    pub(super) make_concrete: P::MakeConcrete<'vir>,
}

/// Takes as input the most generic version (c.f. [`MostGenericTy`]) of a Rust
/// type, and generates functions to convert the generic Viper representation of
/// a Rust expression with that type to its concrete representation, and
/// vice-versa. If the provided type is generic, it does nothing, returning
/// [`CastFunctions::AlreadyGeneric`].
///
/// In the pure case, each pair becomes one variant of the `s_Param` adt (see
/// [`CastersEnc::<Pure>::emit_outputs`]): `make_generic` is the variant's
/// constructor (the concrete snapshot and the type/const arguments are its
/// fields) and `make_concrete` is the value field's destructor.
pub(super) struct CastersEnc<T>(PhantomData<T>);

pub trait PurityCasters: Purity {
    type MakeGeneric<'vir>: Debug + Clone + Copy;
    type MakeConcrete<'vir>: Debug + Clone + Copy;
}

impl PurityCasters for Pure {
    type MakeGeneric<'vir> =
        FunctionIdn<'vir, (vir::CSnap, vir::ManyTyVal, vir::ManyCSnap), vir::PSnap>;
    type MakeConcrete<'vir> = vir::AdtDestructor<'vir, vir::PSnap, vir::CSnap>;
}

impl PurityCasters for Impure {
    type MakeGeneric<'vir> = MethodIdn<'vir, (vir::Ref, vir::ManyTyVal, vir::ManyCSnap)>;
    type MakeConcrete<'vir> = MethodIdn<'vir, (vir::Ref, vir::ManyTyVal, vir::ManyCSnap)>;
}

impl<'vir, P: PurityCasters> task_encoder::OutputRefAny for GArgCasters<'vir, P> {}

/// Per-pair data for [`CastersEnc::<Pure>::emit_outputs`]: the variant
/// constructor plus what the `s_Param_typ` axioms need.
#[derive(Clone)]
pub(super) struct PureCaster<'vir> {
    constructor: vir::AdtConstructor<'vir>,
    make_generic: <Pure as PurityCasters>::MakeGeneric<'vir>,
    self_ty: vir::TypeCSnap<'vir>,
    ty_constructor: FunctionIdn<'vir, (vir::ManyTyVal, vir::ManyCSnap), vir::TyVal>,
    ty_decls: Vec<vir::LocalDeclTyVal<'vir>>,
    const_decls: Vec<vir::LocalDeclCSnap<'vir>>,
}

impl TaskEncoder for CastersEnc<Pure> {
    task_encoder::encoder_cache!(CastersEnc<Pure>);
    const ENCODER_NAME: &'static str = "pure casters encoder";

    type TaskDescription<'vir> = (RustTy<'vir>, RustTy<'vir>);
    type OutputRef<'vir> = GArgCasters<'vir, Pure>;
    type OutputFullLocal<'vir> = PureCaster<'vir>;
    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        let (param, concrete) = task_key;
        assert!(param.specifics.is_param() && !concrete.specifics.is_param());
        vir::with_vcx(|vcx| {
            use vir::CastType;
            let domain_ref = deps.require_ref::<TyPureEnc>(concrete)?;
            let generic_snap = vir::TYPE_PSNAP;
            let self_ty = domain_ref.snapshot.downcast_ty();
            let base_name = concrete.name();
            let ty_constructor = deps.require_ref::<TyConstructorEnc>(concrete)?;
            let generics = deps.require_dep::<GenericParamsEnc>(concrete.params)?;

            let make_generic_ident = FunctionIdn::new(
                vir::vir_format_identifier!(vcx, "make_generic_s_{base_name}"),
                (self_ty, generics.ty_args(), generics.const_args()),
                generic_snap,
            );

            let make_concrete_destr = vcx.mk_adt_destructor(
                vir::vir_format!(vcx, "make_concrete_s_{base_name}"),
                generic_snap,
                self_ty,
            );

            deps.emit_output_ref(
                *task_key,
                GArgCasters {
                    make_generic: make_generic_ident,
                    make_concrete: make_concrete_destr,
                },
            )?;

            // The variant's fields: the concrete value (whose destructor is
            // `make_concrete`), then the type and const arguments. The latter
            // make `s_Param_typ` definable on instantiated generics.
            let fields = std::iter::once(
                vcx.mk_local_decl(make_concrete_destr.name, self_ty)
                    .as_dyn(),
            )
            .chain(generics.ty_decls().iter().map(|d| {
                vcx.mk_local_decl(
                    vir::vir_format!(vcx, "make_generic_s_{base_name}_typaram_{}", d.name),
                    vir::TYPE_TYVAL,
                )
                .as_dyn()
            }))
            .chain(generics.const_decls().iter().map(|d| {
                vcx.mk_local_decl(
                    vir::vir_format!(vcx, "make_generic_s_{base_name}_constparam_{}", d.name),
                    d.ty,
                )
                .as_dyn()
            }))
            .collect::<Vec<vir::LocalDeclDyn<'vir>>>();
            let constructor = vcx
                .mk_adt_constructor(make_generic_ident.name().to_str(), vcx.alloc_slice(&fields));

            Ok((
                PureCaster {
                    constructor,
                    make_generic: make_generic_ident,
                    self_ty,
                    ty_constructor: ty_constructor.ty_constructor,
                    ty_decls: generics.ty_decls().to_vec(),
                    const_decls: generics.const_decls().to_vec(),
                },
                (),
            ))
        })
    }

    /// Emits the `s_Param` adt: one variant per generic cast pair, plus the
    /// fallback variant for values of types without a cast pair in this
    /// program (mirroring `Unknown_type` in the `Type` adt). Also emits the
    /// `s_Param_typ` function with two axioms per pair: the definition
    /// `s_Param_typ(make_generic_T(x, ts..)) == T_type(ts..)` and the variant
    /// bridge `s_Param_typ(p).isT_type ==> p.ismake_generic_T`. Together they
    /// make the reconstruction `make_generic_T(make_concrete_T(p), ..) == p`
    /// derivable wherever a param's type is known.
    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        let outputs = Self::all_outputs_local_no_errors(program);
        vir::with_vcx(|vcx| {
            use vir::CastType;
            let typ_idn: FunctionIdn<'_, vir::PSnap, vir::TyVal> = FunctionIdn::new(
                vir::ViperIdent::new(Self::TYP_NAME),
                vir::TYPE_PSNAP,
                vir::TYPE_TYVAL,
            );
            let typ_fn = vcx.mk_domain_function(typ_idn, false, None);
            let mut constructors = Vec::new();
            let mut axioms = Vec::new();
            for pc in outputs {
                constructors.push(pc.constructor);

                let x_decl = vcx.mk_local_decl("x", pc.self_ty);
                let tys = pc
                    .ty_decls
                    .iter()
                    .map(|d| vcx.mk_local_ex(*d))
                    .collect::<Vec<_>>();
                let consts = pc
                    .const_decls
                    .iter()
                    .map(|d| vcx.mk_local_ex(*d))
                    .collect::<Vec<_>>();
                let mg_app = (pc.make_generic)(vcx.mk_local_ex(x_decl), &tys, &consts);
                let qvars = std::iter::once(x_decl.as_dyn())
                    .chain(pc.ty_decls.iter().map(|d| d.as_dyn()))
                    .chain(pc.const_decls.iter().map(|d| d.as_dyn()))
                    .collect::<Vec<vir::LocalDeclDyn<'vir>>>();
                let def = vcx.mk_forall_expr(
                    vcx.alloc_slice(&qvars),
                    vcx.alloc_slice(&[vcx.mk_trigger(&[mg_app])]),
                    vcx.mk_eq_expr(typ_idn(mg_app), (pc.ty_constructor)(&tys, &consts)),
                );
                axioms.push(vcx.mk_domain_axiom(
                    vir::vir_format_identifier!(
                        vcx,
                        "{}_def_{}",
                        Self::TYP_NAME,
                        pc.constructor.name
                    ),
                    def,
                ));

                let p_decl = vcx.mk_local_decl("p", vir::TYPE_PSNAP);
                let typ_p = typ_idn(vcx.mk_local_ex(p_decl));
                let bridge = vcx.mk_forall_expr(
                    vcx.alloc_slice(&[p_decl]),
                    vcx.alloc_slice(&[vcx.mk_trigger(&[typ_p])]),
                    vcx.mk_bin_op_expr(
                        vir::BinOpKind::Implies,
                        vcx.mk_adt_discriminator_expr(typ_p, pc.ty_constructor.name().to_str()),
                        vcx.mk_adt_discriminator_expr(vcx.mk_local_ex(p_decl), pc.constructor.name),
                    )
                    .downcast_ty(),
                );
                axioms.push(vcx.mk_domain_axiom(
                    vir::vir_format_identifier!(
                        vcx,
                        "{}_variant_{}",
                        Self::TYP_NAME,
                        pc.constructor.name
                    ),
                    bridge,
                ));
            }
            let unknown_args =
                vcx.alloc_array(&[vcx.mk_local_decl(Self::UNKNOWN_PARAM_ID, vir::TYPE_INT)]);
            constructors.push(vcx.mk_adt_constructor(Self::UNKNOWN_PARAM_NAME, unknown_args));
            let vir::TypeKind::Domain(param_adt_name, _) = **vir::TYPE_PSNAP else {
                unreachable!()
            };
            program.add_adt(vcx.mk_adt(
                vir::ViperIdent::new(param_adt_name),
                &[],
                vcx.alloc_slice(&constructors),
            ));
            program.add_domain(vcx.mk_domain(
                vir::ViperIdent::new("ParamTyp"),
                &[],
                vcx.alloc_slice(&axioms),
                vcx.alloc_slice(&[typ_fn]),
                None,
            ));
        })
    }
}

impl CastersEnc<Pure> {
    /// The name of the fallback variant of the `s_Param` adt.
    pub const UNKNOWN_PARAM_NAME: &str = "s_Param_Unknown";
    const UNKNOWN_PARAM_ID: &str = "s_Param_Unknown_id";
    /// The name of the function mapping a generic snapshot to its type.
    pub const TYP_NAME: &str = "s_Param_typ";
}

impl TaskEncoder for CastersEnc<Impure> {
    task_encoder::encoder_cache!(CastersEnc<Impure>);
    const ENCODER_NAME: &'static str = "impure casters encoder";

    type TaskDescription<'vir> = (RustTy<'vir>, RustTy<'vir>);
    type OutputRef<'vir> = GArgCasters<'vir, Impure>;
    type OutputFullLocal<'vir> = Vec<vir::Method<'vir>>;
    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        let (param, concrete) = task_key;
        assert!(param.specifics.is_param() && !concrete.specifics.is_param());
        vir::with_vcx(|vcx| {
            use vir::CastType;
            let base_name = concrete.name();
            let ty_constructor = deps.require_ref::<TyConstructorEnc>(concrete)?;
            let generics = deps.require_dep::<GenericParamsEnc>(concrete.params)?;

            let make_generic_ident = MethodIdn::new(
                vir::vir_format_identifier!(vcx, "make_generic_{base_name}"),
                (vir::TYPE_REF, generics.ty_args(), generics.const_args()),
            );

            let make_concrete_ident = MethodIdn::new(
                vir::vir_format_identifier!(vcx, "make_concrete_{base_name}"),
                (vir::TYPE_REF, generics.ty_args(), generics.const_args()),
            );

            deps.emit_output_ref(
                *task_key,
                GArgCasters {
                    make_generic: make_generic_ident,
                    make_concrete: make_concrete_ident,
                },
            )?;
            let make_generic_pure = deps
                .require_ref::<CastersEnc<Pure>>(*task_key)?
                .make_generic;
            let self_decl = vcx.mk_local_decl("self", vir::TYPE_REF);
            let self_expr = vcx.mk_local_ex(self_decl);
            let decls = (self_decl, generics.ty_decls(), generics.const_decls());

            let predicate_ref = deps.require_ref::<TyImpureEnc>(concrete)?;
            let generic_ref = deps.require_ref::<TyImpureEnc>(param)?;

            let concrete_predicate = (predicate_ref.ref_to_pred)(
                self_expr,
                generics.ty_exprs(),
                generics.const_exprs(),
            )(None);

            let concrete_snap =
                (predicate_ref.ref_to_snap)(self_expr, generics.ty_exprs(), generics.const_exprs())
                    .downcast_ty();

            let concrete_predicate = vcx.mk_predicate_app_expr(concrete_predicate);

            let lifted_ty_expr =
                (ty_constructor.ty_constructor)(generics.ty_exprs(), generics.const_exprs());

            let generic_predicate =
                (generic_ref.ref_to_pred)(self_expr, &[lifted_ty_expr], &[])(None);

            let generic_snap = (generic_ref.ref_to_snap)(self_expr, &[lifted_ty_expr], &[])
                .downcast_ty::<vir::PSnap>();

            let generic_predicate = vcx.mk_predicate_app_expr(generic_predicate);

            let make_generic_same_snap = vcx.mk_eq_expr(
                vcx.mk_old_expr(make_generic_pure(
                    concrete_snap,
                    generics.ty_exprs(),
                    generics.const_exprs(),
                )),
                generic_snap,
            );

            let make_concrete_same_snap = vcx.mk_eq_expr(
                vcx.mk_old_expr(generic_snap),
                make_generic_pure(concrete_snap, generics.ty_exprs(), generics.const_exprs()),
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
            Ok((vec![make_generic, make_concrete], ()))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for output in Self::all_outputs_local_no_errors(program) {
            for method in output {
                program.add_method(method);
            }
        }
    }
}
