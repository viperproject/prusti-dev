use std::{fmt::Debug, marker::PhantomData};

use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{FunctionIdn, MethodIdn};

use crate::encoders::{
    Impure, Pure, Purity,
    ty::{
        RustTy,
        impure::TyImpureEnc,
        lifted::{TypeOfEnc, ty_constructor::TyConstructorEnc},
        pure::TyPureEnc,
    },
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
pub(super) struct CastersEnc<T>(PhantomData<T>);

pub trait PurityCasters: Purity {
    type MakeGeneric<'vir>: Debug + Clone + Copy;
    type MakeConcrete<'vir>: Debug + Clone + Copy;
}

impl PurityCasters for Pure {
    type MakeGeneric<'vir> =
        FunctionIdn<'vir, (vir::CSnap, vir::ManyTyVal, vir::ManyCSnap), vir::PSnap>;
    type MakeConcrete<'vir> =
        FunctionIdn<'vir, (vir::PSnap, vir::ManyTyVal, vir::ManyCSnap), vir::CSnap>;
}

impl PurityCasters for Impure {
    type MakeGeneric<'vir> = MethodIdn<'vir, (vir::Ref, vir::ManyTyVal, vir::ManyCSnap)>;
    type MakeConcrete<'vir> = MethodIdn<'vir, (vir::Ref, vir::ManyTyVal, vir::ManyCSnap)>;
}

impl<'vir, P: PurityCasters> task_encoder::OutputRefAny for GArgCasters<'vir, P> {}

impl TaskEncoder for CastersEnc<Pure> {
    task_encoder::encoder_cache!(CastersEnc<Pure>);

    type TaskDescription<'vir> = (RustTy<'vir>, RustTy<'vir>);
    type OutputRef<'vir> = GArgCasters<'vir, Pure>;
    type OutputFullLocal<'vir> = Vec<vir::Function<'vir>>;
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
            let generic_typeof = deps.require_ref::<TypeOfEnc>(param)?.typeof_function;
            let self_ty = (domain_ref.domain)().downcast_ty();
            let base_name = concrete.name();
            let ty_constructor = deps.require_ref::<TyConstructorEnc>(concrete)?;
            let generics = deps.require_dep::<GenericParamsEnc>(concrete.params)?;

            let make_generic_ident = FunctionIdn::new(
                vir::vir_format_identifier!(vcx, "make_generic_s_{base_name}"),
                (self_ty, generics.ty_args(), generics.const_args()),
                generic_snap,
            );

            let make_concrete_ident = FunctionIdn::new(
                vir::vir_format_identifier!(vcx, "make_concrete_s_{base_name}"),
                (generic_snap, generics.ty_args(), generics.const_args()),
                self_ty,
            );

            deps.emit_output_ref(
                *task_key,
                GArgCasters {
                    make_generic: make_generic_ident,
                    make_concrete: make_concrete_ident,
                },
            )?;
            let make_generic_arg = vcx.mk_local_decl("self", self_ty);
            let make_generic_expr = vcx.mk_local_ex(make_generic_arg);

            let make_generic_result = vcx.mk_result(generic_snap);

            // Type parameters obtained from the snapshot-encoded value of the type,
            let ty_params_from_snap = generics
                .ty_decls()
                .iter()
                .enumerate()
                .map(|(idx, _)| ty_constructor.ty_param_from_snap(idx, make_generic_expr))
                .collect::<Vec<_>>();

            let const_params_from_snap = generics
                .const_decls()
                .iter()
                .enumerate()
                .map(|(idx, _)| ty_constructor.const_param_from_snap(idx, make_generic_expr))
                .collect::<Vec<_>>();

            // Asserts that the type of `param` is equal to the ty constructor
            // applied to type arguments `args`
            let mk_type_spec = |param: vir::ExprPSnap<'vir>, ty_args, const_args| {
                let lifted_param_snap_ty = generic_typeof(param.upcast_ty());
                vcx.mk_eq_expr(
                    lifted_param_snap_ty,
                    (ty_constructor.ty_constructor)(ty_args, const_args),
                )
            };

            let make_generic = vcx.mk_function(
                make_generic_ident,
                (
                    make_generic_arg,
                    generics.ty_decls(),
                    generics.const_decls(),
                ),
                &[],
                vcx.alloc_slice(&[
                    mk_type_spec(
                        make_generic_result,
                        &ty_params_from_snap,
                        &const_params_from_snap,
                    ),
                    vcx.mk_eq_expr(
                        make_concrete_ident(
                            make_generic_result,
                            &ty_params_from_snap,
                            &const_params_from_snap,
                        ),
                        make_generic_expr,
                    ),
                ]),
                None,
                None,
            );

            let make_concrete_snap_arg_decl = vcx.mk_local_decl("snap", generic_snap);
            let make_concrete_snap_arg_expr = vcx.mk_local_ex(make_concrete_snap_arg_decl);

            let _make_concrete_pre = mk_type_spec(
                make_concrete_snap_arg_expr,
                generics.ty_exprs(),
                generics.const_exprs(),
            );

            let make_concrete_post = vcx.mk_eq_expr(
                make_generic_ident(
                    vcx.mk_result(self_ty),
                    generics.ty_exprs(),
                    generics.const_exprs(),
                ),
                make_concrete_snap_arg_expr,
            );

            let make_concrete = vcx.mk_function(
                make_concrete_ident,
                (
                    make_concrete_snap_arg_decl,
                    generics.ty_decls(),
                    generics.const_decls(),
                ),
                // TODO: type preconditions do not currently work
                // vcx.alloc_slice(&[make_concrete_pre]),
                &[],
                vcx.alloc_slice(&[make_concrete_post]),
                None,
                None,
            );

            Ok((vec![make_generic, make_concrete], ()))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for output in Self::all_outputs_local_no_errors() {
            for function in output {
                program.add_function(function);
            }
        }
    }
}

impl TaskEncoder for CastersEnc<Impure> {
    task_encoder::encoder_cache!(CastersEnc<Impure>);

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
        for output in Self::all_outputs_local_no_errors() {
            for method in output {
                program.add_method(method);
            }
        }
    }
}
