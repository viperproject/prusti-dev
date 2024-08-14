use prusti_rustc_interface::{
    hir,
    middle::{
        mir,
        ty::{self, GenericArgs},
    },
    span::def_id::DefId,
};
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{Method, MethodIdent, UnknownArity};

use super::suspension_points::SuspensionPointAnalysis;
use crate::encoders::{
    lifted::{
        casters::CastTypePure, func_def_ty_params::LiftedTyParamsEnc,
        rust_ty_cast::RustTyCastersEnc,
    },
    r#type::rust_ty_predicates::RustTyPredicatesEnc,
    MirLocalDefEnc, MirSpecEnc,
};

/// Encodes a poll call stub for an async item
pub struct AsyncPollStubEnc;

#[derive(Clone, Debug)]
pub struct AsyncPollStubEncOutputRef<'vir> {
    pub method_ref: MethodIdent<'vir, UnknownArity<'vir>>,
    pub return_ty: ty::Ty<'vir>,
    pub arg_tys: Vec<ty::Ty<'vir>>,
}
impl<'vir> task_encoder::OutputRefAny for AsyncPollStubEncOutputRef<'vir> {}

#[derive(Clone, Debug)]
pub struct AsyncPollStubEncOutput<'vir> {
    pub method: Method<'vir>,
}

#[derive(Clone, Debug)]
pub struct AsyncPollStubEncError;

impl TaskEncoder for AsyncPollStubEnc {
    task_encoder::encoder_cache!(AsyncPollStubEnc);

    type TaskDescription<'vir> = DefId;

    type OutputRef<'vir> = AsyncPollStubEncOutputRef<'vir>;
    type OutputFullLocal<'vir> = AsyncPollStubEncOutput<'vir>;

    type EncodingError = AsyncPollStubEncError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        // TODO: for now this is a generic encoding, check whether and how this needs to be adapted
        // for a monomorphic encoding
        let def_id = *task;
        vir::with_vcx(|vcx| {
            // get generator type
            let gen_ty = vcx.tcx().type_of(def_id).skip_binder();
            let ty::TyKind::Generator(_def_id, gen_args, _) = gen_ty.kind() else {
                panic!("expected type of async fn to be Generator");
            };
            assert_eq!(def_id, *_def_id);
            // construct the receiver type (std::pin::Pin<&mut Self>)
            let ref_ty = vcx.tcx().mk_ty_from_kind(ty::TyKind::Ref(
                ty::Region::new_from_kind(vcx.tcx(), ty::RegionKind::ReErased),
                gen_ty,
                mir::Mutability::Mut,
            ));
            let recv_ty = {
                let pin_def_id = vcx.tcx().require_lang_item(hir::LangItem::Pin, None);
                vcx.tcx().mk_ty_from_kind(ty::TyKind::Adt(
                    vcx.tcx().adt_def(pin_def_id),
                    vcx.tcx().mk_args(&[ref_ty.into()]),
                ))
            };
            let enc_recv_ty = deps.require_ref::<RustTyPredicatesEnc>(recv_ty)?;
            // construct the second argument type (std::task::Context)
            let cx_ty = {
                let cx_def_id = vcx.tcx().require_lang_item(hir::LangItem::Context, None);
                let cx_ty = vcx.tcx().mk_ty_from_kind(ty::TyKind::Adt(
                    vcx.tcx().adt_def(cx_def_id),
                    ty::List::empty(),
                ));
                vcx.tcx().mk_ty_from_kind(ty::TyKind::Ref(
                    ty::Region::new_from_kind(vcx.tcx(), ty::RegionKind::ReErased),
                    cx_ty,
                    mir::Mutability::Mut,
                ))
            };
            let enc_cx_ty = deps.require_ref::<RustTyPredicatesEnc>(cx_ty)?;
            // construct the return type (std::poll::Poll<return_ty>)
            let ret_ty = {
                let poll_def_id = vcx.tcx().require_lang_item(hir::LangItem::Poll, None);
                vcx.tcx().mk_ty_from_kind(ty::TyKind::Adt(
                    vcx.tcx().adt_def(poll_def_id),
                    vcx.tcx()
                        .mk_args(&[gen_args.as_generator().return_ty().into()]),
                ))
            };
            let enc_ret_ty = deps.require_ref::<RustTyPredicatesEnc>(ret_ty)?;

            // construct the stub's signature
            let substs = GenericArgs::identity_for_item(vcx.tcx(), def_id);
            let local_defs = deps.require_local::<MirLocalDefEnc>((def_id, substs, None))?;
            let method_name =
                vir::vir_format_identifier!(vcx, "m_poll_{}", vcx.tcx().def_path_str(def_id));
            let arg_count = local_defs.arg_count + 1;
            assert_eq!(arg_count, 3);
            let param_ty_decls = deps
                .require_local::<LiftedTyParamsEnc>(substs)?
                .iter()
                .map(|g| g.decl())
                .collect::<Vec<_>>();
            let method_ref = {
                let mut args = vec![&vir::TypeData::Ref; arg_count];
                args.extend(param_ty_decls.iter().map(|decl| decl.ty));
                let args = UnknownArity::new(vcx.alloc_slice(&args));
                MethodIdent::new(method_name, args)
            };
            deps.emit_output_ref(
                *task,
                AsyncPollStubEncOutputRef {
                    method_ref,
                    return_ty: ret_ty,
                    arg_tys: vec![recv_ty, cx_ty],
                },
            )?;

            let upvar_tys = gen_args.as_generator().upvar_tys().to_vec();
            let n_upvars = upvar_tys.len();

            // read the generator snapshot from the generator argument
            let gen_snap = {
                let pin_snap =
                    enc_recv_ty.ref_to_snap(vcx, local_defs.locals[1_u32.into()].local_ex);
                let ref_snap = {
                    let fields = enc_recv_ty
                        .generic_predicate
                        .expect_structlike()
                        .snap_data
                        .field_access;
                    assert_eq!(fields.len(), 1, "expected pin domain to have 1 field");
                    let ref_snap = fields[0].read.apply(vcx, [pin_snap]);
                    let caster = deps.require_local::<RustTyCastersEnc<CastTypePure>>(ref_ty)?;
                    caster.cast_to_concrete_if_possible(vcx, ref_snap)
                };
                let enc_ref_ty = deps.require_ref::<RustTyPredicatesEnc>(ref_ty)?;
                let fields = enc_ref_ty
                    .generic_predicate
                    .expect_ref()
                    .snap_data
                    .field_access;
                assert_eq!(fields.len(), 1, "expected ref domain to have 1 field");
                let gen_snap = fields[0].read.apply(vcx, [ref_snap]);
                let caster = deps.require_local::<RustTyCastersEnc<CastTypePure>>(gen_ty)?;
                caster.cast_to_concrete_if_possible(vcx, gen_snap)
            };
            // and read the generator's fields
            let gen_fields = {
                let gen_ty = deps.require_ref::<RustTyPredicatesEnc>(gen_ty)?;
                let gen_domain_data = gen_ty.generic_predicate.expect_structlike();
                let fields = gen_domain_data.snap_data.field_access;
                fields
                    .iter()
                    .map(|field| field.read.apply(vcx, [gen_snap]))
                    .collect::<Vec<_>>()
            };
            assert_eq!(gen_fields.len(), 2 * n_upvars + 1);

            // viper function to take snapshot of u32, will be used for state values
            let u32_snap_fn = deps
                .require_ref::<RustTyPredicatesEnc>(
                    vcx.tcx().mk_ty_from_kind(ty::TyKind::Uint(ty::UintTy::U32)),
                )?
                .generic_predicate
                .expect_prim()
                .prim_to_snap;
            let mk_u32_snap = |x: u32| {
                let vir_cnst = vcx.mk_const_expr(vir::ConstData::Int(x.into()));
                u32_snap_fn.apply(vcx, [vir_cnst])
            };

            let suspension_points = deps
                .require_local::<SuspensionPointAnalysis>(def_id)
                .unwrap()
                .0;

            // encode the stub's specification
            let spec = deps.require_local::<MirSpecEnc>((def_id, substs, None, false, true))?;

            // encode the method's on_exit/on_entry conditions as post-/preconditions
            let (on_exit_posts, on_entry_pres) = {
                let state_field = gen_fields[2 * n_upvars];
                let to_bool = deps
                    .require_ref::<RustTyPredicatesEnc>(vcx.tcx().types.bool)
                    .unwrap()
                    .generic_predicate
                    .expect_prim()
                    .snap_to_prim;
                // create reference snapshots to the generator's fields
                let field_refs = {
                    let fields = &gen_fields[..n_upvars];
                    upvar_tys
                        .iter()
                        .zip(fields)
                        .map(|(ty, field)| {
                            let caster = deps
                                .require_local::<RustTyCastersEnc<CastTypePure>>(*ty)
                                .unwrap();
                            let ref_ty = vcx.tcx().mk_ty_from_kind(ty::TyKind::Ref(
                                ty::Region::new_from_kind(vcx.tcx(), ty::RegionKind::ReErased),
                                *ty,
                                mir::Mutability::Not,
                            ));
                            let ref_cons = deps
                                .require_ref::<RustTyPredicatesEnc>(ref_ty)
                                .unwrap()
                                .generic_predicate
                                .expect_ref()
                                .snap_data
                                .field_snaps_to_snap;
                            ref_cons.apply(vcx, &[caster.cast_to_generic_if_necessary(vcx, field)])
                        })
                        .collect::<Vec<_>>()
                };

                let mut encode_condition = |cond_def_id: &DefId| {
                    // Note that all of these conditions are obtained by encoding their closure's body,
                    // which takes a reference to the closure as the only parameter and captured values
                    // (i.e. the generator fields referred to inside the condition) are accessed as
                    // fields of that closure.
                    // Hence, we first need to construct a reference to such a closure in order to
                    // reify the encoded expression
                    let closure_ty = vcx.tcx().type_of(*cond_def_id).skip_binder();
                    let closure_snap = {
                        let closure_ty =
                            deps.require_ref::<RustTyPredicatesEnc>(closure_ty).unwrap();
                        let closure_cons = closure_ty
                            .generic_predicate
                            .expect_structlike()
                            .snap_data
                            .field_snaps_to_snap;
                        closure_cons.apply(vcx, &field_refs)
                    };
                    let closure_ref = {
                        let caster = deps
                            .require_local::<RustTyCastersEnc<CastTypePure>>(closure_ty)
                            .unwrap();
                        let ref_ty = vcx.tcx().mk_ty_from_kind(ty::TyKind::Ref(
                            ty::Region::new_from_kind(vcx.tcx(), ty::RegionKind::ReErased),
                            closure_ty,
                            mir::Mutability::Not,
                        ));
                        let ref_ty = deps.require_ref::<RustTyPredicatesEnc>(ref_ty).unwrap();
                        let ref_cons = ref_ty
                            .generic_predicate
                            .expect_ref()
                            .snap_data
                            .field_snaps_to_snap;
                        ref_cons.apply(
                            vcx,
                            &[caster.cast_to_generic_if_necessary(vcx, closure_snap)],
                        )
                    };
                    // given that reference, we can now encode the closure body and reify using
                    // that reference
                    let expr = deps
                        .require_local::<crate::encoders::MirPureEnc>(
                            crate::encoders::MirPureEncTask {
                                encoding_depth: 0,
                                kind: crate::encoders::PureKind::Closure,
                                parent_def_id: *cond_def_id,
                                param_env: vcx.tcx().param_env(cond_def_id),
                                substs,
                                // TODO: should this be `def_id` or `cond_def_id`
                                caller_def_id: Some(*cond_def_id),
                            },
                        )
                        .unwrap()
                        .expr;
                    use vir::Reify;
                    let expr = expr.reify(vcx, (*cond_def_id, vcx.alloc_slice(&[closure_ref])));
                    to_bool.apply(vcx, [expr])
                };

                let mut on_exit_posts: Vec<&'vir vir::ExprGenData<'_, !, !>> = Vec::new();
                let mut on_entry_pres: Vec<&'vir vir::ExprGenData<'_, !, !>> = Vec::new();

                for sp in &suspension_points {
                    let is_in_state = vcx.mk_bin_op_expr(
                        vir::BinOpKind::CmpEq,
                        state_field,
                        mk_u32_snap(sp.label),
                    );
                    let on_exits = sp.on_exit_closures.iter().map(|cond_def_id| {
                        vcx.mk_bin_op_expr(
                            vir::BinOpKind::Implies,
                            is_in_state,
                            encode_condition(cond_def_id),
                        )
                    });
                    on_exit_posts.extend(on_exits);
                    let on_entries = sp.on_entry_closures.iter().map(|cond_def_id| {
                        vcx.mk_bin_op_expr(
                            vir::BinOpKind::Implies,
                            is_in_state,
                            encode_condition(cond_def_id),
                        )
                    });
                    on_entry_pres.extend(on_entries);
                }

                (on_exit_posts, on_entry_pres)
            };

            // add arguments and preconditions about their types
            // note that the signature is (self: std::pin::Pin<&mut Self>, cx: &mut Context)
            // and not the signature of the generator
            // TODO: fix capacity here
            let mut pres = Vec::with_capacity(arg_count + spec.async_invariants.len() - 1);
            let mut args = Vec::with_capacity(
                arg_count + substs.len() + n_upvars + spec.async_invariants.len() + 1,
            );
            for arg_idx in 0..arg_count {
                let name = local_defs.locals[arg_idx.into()].local.name;
                args.push(vir::vir_local_decl! { vcx; [name] : Ref });
            }
            pres.push(enc_recv_ty.ref_to_pred(vcx, local_defs.locals[1_u32.into()].local_ex, None));
            pres.push(enc_cx_ty.ref_to_pred(vcx, local_defs.locals[2_u32.into()].local_ex, None));
            // add type parameters (and their typing preconditions)
            args.extend(param_ty_decls.iter());
            pres.extend(spec.pres);

            // constrain possible state values to the suspension-point labels as well as 0
            let state_value_constraint = {
                let state_field = gen_fields[2 * n_upvars];
                let state_values = suspension_points
                    .iter()
                    .map(|sp| vcx.mk_const_expr(vir::ConstData::Int(sp.label.into())))
                    .chain(std::iter::once(vcx.mk_uint::<0>()))
                    .map(|lbl| u32_snap_fn.apply(vcx, [lbl]));
                state_values
                    .map(|v| vcx.mk_bin_op_expr(vir::BinOpKind::CmpEq, state_field, v))
                    .reduce(|l, r| vcx.mk_bin_op_expr(vir::BinOpKind::Or, l, r))
                    .unwrap()
            };
            pres.push(state_value_constraint);

            // add preconditions corresponding to on_entry conditions
            pres.extend(on_entry_pres);

            // add invariants as preconditions
            for inv in &spec.async_invariants {
                pres.push(*inv);
            }

            // add postconditions for the return type as well as user-annotated ones
            // we also add a postcondition on the generator type after the call and the requirement
            // about its state values
            // TODO: fix capacities here
            let mut posts = Vec::with_capacity(spec.async_stub_posts.len() + 2);
            posts.push(enc_ret_ty.ref_to_pred(
                vcx,
                local_defs.locals[mir::RETURN_PLACE].local_ex,
                None,
            ));
            posts.push(enc_recv_ty.ref_to_pred(
                vcx,
                local_defs.locals[1_u32.into()].local_ex,
                None,
            ));
            posts.push(state_value_constraint);
            posts.extend(spec.async_stub_posts);

            // add postconditions corresponding to on_exit conditions
            posts.extend(on_exit_posts);

            // add postconditions that polling the future does not change the ghost fields
            // so they still capture the initial state of the async fn's arguments
            // read the generator from the pinned mutable ref
            for ghost_field in gen_fields[n_upvars..2 * n_upvars].iter() {
                let old_ghost_field = vcx.mk_old_expr(ghost_field);
                posts.push(vcx.mk_bin_op_expr(vir::BinOpKind::CmpEq, ghost_field, old_ghost_field));
            }

            // add invariants as postconditions
            for inv in &spec.async_invariants {
                posts.push(*inv);
            }

            let method = vcx.mk_method(
                method_ref,
                vcx.alloc_slice(&args),
                &[],
                vcx.alloc_slice(&pres),
                vcx.alloc_slice(&posts),
                None,
            );
            Ok((AsyncPollStubEncOutput { method }, ()))
        })
    }
}
