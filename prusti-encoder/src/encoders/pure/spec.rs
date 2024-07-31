use prusti_rustc_interface::{
    hir,
    middle::{mir, ty},
    span::{def_id::DefId, Symbol},
};

use task_encoder::{TaskEncoder, TaskEncoderDependencies, EncodeFullResult};
use vir::Reify;

use crate::encoders::{
    predicate,
    mir_pure::PureKind,
    rust_ty_predicates::RustTyPredicatesEnc,
    MirPureEnc,
    most_generic_ty,
    lifted::{rust_ty_cast::RustTyCastersEnc, casters::CastTypePure},
};
pub struct MirSpecEnc;

#[derive(Clone)]
pub struct MirSpecEncOutput<'vir> {
    pub pres: Vec<vir::Expr<'vir>>,
    pub posts: Vec<vir::Expr<'vir>>,
    pub async_stub_posts: Vec<vir::Expr<'vir>>,
    pub async_invariants: Vec<vir::Expr<'vir>>,
    pub pre_args: &'vir [vir::Expr<'vir>],
    pub post_args: &'vir [vir::Expr<'vir>],
}

impl TaskEncoder for MirSpecEnc {
    task_encoder::encoder_cache!(MirSpecEnc);

    type TaskDescription<'tcx> = (
        DefId,                    // The function annotated with specs
        ty::GenericArgsRef<'tcx>, // ? this should be the "signature", after applying the env/substs
        Option<DefId>,            // ID of the caller function, if any
        bool,                     // If to encode as pure or not
        bool,                     // whether to encode for an async poll stub or not
    );

    type OutputFullLocal<'vir> = MirSpecEncOutput<'vir>;

    type EncodingError = <MirPureEnc as TaskEncoder>::EncodingError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        let (def_id, substs, caller_def_id, pure, is_poll_stub) = *task_key;
        deps.emit_output_ref(*task_key, ())?;

        let local_defs = deps
            .require_local::<crate::encoders::local_def::MirLocalDefEnc>((
                def_id,
                substs,
                caller_def_id,
            ))?;
        let specs = deps
            .require_local::<crate::encoders::SpecEnc>(crate::encoders::SpecEncTask { def_id })?;

        vir::with_vcx(|vcx| {
            let local_iter = (1..=local_defs.arg_count).map(mir::Local::from);
            let all_args: Vec<_> = if pure {
                let result_ty = local_defs.locals[mir::RETURN_PLACE].ty;
                local_iter
                    .map(|local| {
                        vcx.mk_local_ex(
                            local_defs.locals[local].local.name,
                            local_defs.locals[local].ty.snapshot,
                        )
                    })
                    .chain([vcx.mk_result(result_ty.snapshot)])
                    .collect()
            } else {
                local_iter
                    .map(|local| local_defs.locals[local].impure_snap)
                    .collect()
            };
            let all_args = vcx.alloc_slice(&all_args);
            let pre_args = if pure {
                &all_args[..all_args.len() - 1]
            } else {
                all_args
            };

            let to_bool = deps
                .require_ref::<RustTyPredicatesEnc>(vcx.tcx().types.bool)?
                .generic_predicate
                .expect_prim()
                .snap_to_prim;

            let pres = specs
                .pres
                .iter()
                .map(|spec_def_id| {
                    let expr = deps
                        .require_local::<crate::encoders::MirPureEnc>(
                            crate::encoders::MirPureEncTask {
                                encoding_depth: 0,
                                kind: PureKind::Spec,
                                parent_def_id: *spec_def_id,
                                param_env: vcx.tcx().param_env(spec_def_id),
                                substs,
                                // TODO: should this be `def_id` or `caller_def_id`
                                caller_def_id: Some(def_id),
                            },
                        )
                        .unwrap()
                        .expr;
                    let expr = expr.reify(vcx, (*spec_def_id, pre_args));
                    to_bool.apply(vcx, [expr])
                })
                .collect::<Vec<vir::Expr<'_>>>();

            let is_async = vcx.tcx().generator_is_async(def_id);
            if !is_async && is_poll_stub {
                panic!("cannot set is_poll_stub for non-async bodies");
            }

            // on async functions, there is a mismatch between the signature of the declared
            // async fn (and thus the spec function) and its body on the MIR level, whose
            // parameters are the return place, the future, and the `ResumeTy`
            // hence, instead of directly accessing function arguments, we need to read them
            // from the generator's ghost fields
            let async_generator_ghost_fields = if !is_async {
                    None
            } else {
                let generator_snap = if !is_poll_stub {
                    // the async body simply takes the generator as argument and returns the result
                    local_defs.locals[1_u32.into()].impure_snap
                } else {
                    // the poll stub, however, (which does not have a `DefId` and thus a signature
                    // we can see) takes a pinned mutable reference to the generator and returns
                    // the result wrapped in a `Poll`.
                    // hence, we first need to read the generator from the pinned reference and fix
                    // the typing of the return value (note that the postcondition itself is
                    // already wrapped in `Poll` by the `prusti_contracts` macros)
                    let gen_ty = vcx.tcx().type_of(def_id).skip_binder();
                    let gen_snap = {
                        // construct the receiver type
                        let ref_ty = vcx.tcx().mk_ty_from_kind(ty::TyKind::Ref(
                            ty::Region::new_from_kind(vcx.tcx(), ty::RegionKind::ReErased),
                            gen_ty,
                            mir::Mutability::Mut,
                        ));
                        let pin_ty = {
                            let pin_def_id = vcx.tcx().require_lang_item(hir::LangItem::Pin, None);
                            vcx.tcx().mk_ty_from_kind(ty::TyKind::Adt(
                                vcx.tcx().adt_def(pin_def_id),
                                vcx.tcx().mk_args(&[ref_ty.into()]),
                            ))
                        };
                        // and gradually read the generator snapshot from the argument
                        let ref_snap = {
                            let pin_ty = deps.require_ref::<RustTyPredicatesEnc>(pin_ty)?;
                            // note that we cannot use the `LocalDef`'s `impure_snap`, as its type is the
                            // generator itself due to the `DefId` belonging to the generator body
                            let pin_snap = pin_ty.ref_to_snap(vcx, local_defs.locals[1_u32.into()].local_ex);
                            let fields = pin_ty.generic_predicate.expect_structlike().snap_data.field_access;
                            assert_eq!(fields.len(), 1, "expected pin domain to have 1 field");
                            let ref_snap = fields[0].read.apply(vcx, [pin_snap]);
                            let caster = deps.require_local::<RustTyCastersEnc<CastTypePure>>(ref_ty).unwrap();
                            caster.cast_to_concrete_if_possible(vcx, ref_snap)
                        };
                        let ref_ty = deps.require_ref::<RustTyPredicatesEnc>(ref_ty)?;
                        let fields = ref_ty.generic_predicate.expect_ref().snap_data.field_access;
                        assert_eq!(fields.len(), 1, "expected ref domain to have 1 field");
                        let gen_snap = fields[0].read.apply(vcx, [ref_snap]);
                        let caster = deps.require_local::<RustTyCastersEnc<CastTypePure>>(gen_ty).unwrap();
                        caster.cast_to_concrete_if_possible(vcx, gen_snap)
                    };
                    gen_snap
                };
                let ghost_fields = {
                    let generator_ty = local_defs.locals[mir::Local::from(1_u32)].ty;
                    let predicate::PredicateEncData::StructLike(gen_domain_data) = generator_ty.specifics else {
                        panic!("expected generator domain to be struct-like");
                    };
                    let fields = gen_domain_data.snap_data.field_access;
                    let n_fields = fields.len();
                    assert!(n_fields % 2 == 0);
                    fields[n_fields / 2 ..].iter()
                };
                let ghost_field_reads = ghost_fields
                    .map(
                        |field| field.read.apply(vcx, [generator_snap])
                    )
                    .collect::<Vec<_>>();
                Some(ghost_field_reads)
            };

            // TODO: check what happens for a pure async fn
            let post_args = if pure {
                all_args
            } else if !is_async {
                let post_args: Vec<_> = pre_args
                    .iter()
                    .map(|arg| vcx.mk_old_expr(arg))
                    .chain([local_defs.locals[mir::RETURN_PLACE].impure_snap])
                    .collect();
                vcx.alloc_slice(&post_args)
            } else {
                // set the arguments available to the postcondition to be old-expressions (as the
                // generator is consumed by the function) of the ghost fields as well as the return value
                let return_expr = if !is_poll_stub {
                    local_defs.locals[mir::RETURN_PLACE].impure_snap
                } else {
                    // construct the return type
                    let ret_ty = {
                        let gen_ty = vcx.tcx().type_of(def_id).skip_binder();
                        let ty::TyKind::Generator(_, args, _) = gen_ty.kind() else {
                            panic!("expected async fn type to be Generator");
                        };
                        let ret_ty = args.as_generator().return_ty();
                        let poll_def_id = vcx.tcx().require_lang_item(hir::LangItem::Poll, None);
                        vcx.tcx().mk_ty_from_kind(ty::TyKind::Adt(
                            vcx.tcx().adt_def(poll_def_id),
                            vcx.tcx().mk_args(&[ret_ty.into()]),
                        ))
                    };
                    // and build an expression for the return value with that type
                    let ret_ty = deps.require_ref::<RustTyPredicatesEnc>(ret_ty)?;
                    ret_ty.ref_to_snap(vcx, local_defs.locals[0_u32.into()].local_ex)
                };
                let post_args = async_generator_ghost_fields
                    .as_ref()
                    .unwrap()
                    .iter()
                    .map(|ghost_field| vcx.mk_old_expr(ghost_field))
                    .chain(std::iter::once(return_expr))
                    .collect::<Vec<_>>();
                vcx.alloc_slice(&post_args)
            };

            let mut mk_post_spec_expr = |spec_def_id: &DefId| {
                let expr = deps
                    .require_local::<crate::encoders::MirPureEnc>(
                        crate::encoders::MirPureEncTask {
                            encoding_depth: 0,
                            kind: PureKind::Spec,
                            parent_def_id: *spec_def_id,
                            param_env: vcx.tcx().param_env(spec_def_id),
                            substs,
                            // TODO: should this be `def_id` or `caller_def_id`
                            caller_def_id: Some(def_id),
                        },
                    )
                    .unwrap()
                    .expr;
                let expr = expr.reify(vcx, (*spec_def_id, post_args));
                to_bool.apply(vcx, [expr])
            };

            let posts = specs
                .posts
                .iter()
                .map(&mut mk_post_spec_expr)
                .collect::<Vec<vir::Expr<'_>>>();

            // we also encode the wrapped postconditions for async poll stubs
            // using the same arguments available to standard postconditions
            // for non-async items, this will just be empty
            let async_stub_posts = specs
                .async_stub_posts
                .iter()
                .map(mk_post_spec_expr)
                .collect::<Vec<vir::Expr<'_>>>();

            // async invariants are encoded using the same arguments as postconditions
            // except for `result`, which cannot be used in async invariants
            // async invariants also need to be encoded using the generator's ghost fields
            // instead of the function arguments
            // Note that they are *not* encoded using old-expressions of the ghsot fields,
            // so they cannot be used as a postcondition on the generator's body (as the body
            // consumes the generator). For the poll stub, there is no such restriction.
            let async_invariants = if !is_async {
                Vec::new()
            } else {
                let inv_args = vcx.alloc_slice(&async_generator_ghost_fields.unwrap());
                specs
                    .async_invariants
                    .iter()
                    .map(|spec_def_id| {
                        let expr = deps
                            .require_local::<crate::encoders::MirPureEnc>(
                                crate::encoders::MirPureEncTask {
                                    encoding_depth: 0,
                                    kind: PureKind::Spec,
                                    parent_def_id: *spec_def_id,
                                    param_env: vcx.tcx().param_env(spec_def_id),
                                    substs,
                                    // TODO: should this be `def_id` or `caller_def_id`
                                    caller_def_id: Some(def_id),
                                }
                            )
                            .unwrap()
                            .expr;
                        let expr = expr.reify(vcx, (*spec_def_id, inv_args));
                        to_bool.apply(vcx, [expr])
                    })
                .collect::<Vec<vir::Expr<'_>>>()
            };

            let data = MirSpecEncOutput {
                pres,
                posts,
                async_stub_posts,
                async_invariants,
                pre_args,
                post_args,
            };
            Ok((data, ()))
        })
    }
}
