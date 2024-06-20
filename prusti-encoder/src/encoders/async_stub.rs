use prusti_rustc_interface::{
    ast, hir,
    middle::{
        mir,
        ty::{self, GenericArgs},
    },
    span::def_id::DefId,
};
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{Method, MethodIdent, UnknownArity};

use crate::encoders::{
    lifted::func_def_ty_params::LiftedTyParamsEnc, r#type::rust_ty_predicates::RustTyPredicatesEnc,
    MirLocalDefEnc, MirSpecEnc,
};

/// Encodes a poll call stub for an async item
pub struct AsyncStubEnc;

#[derive(Clone, Debug)]
pub struct AsyncStubEncOutputRef<'vir> {
    pub method_ref: MethodIdent<'vir, UnknownArity<'vir>>,
    pub return_ty: ty::Ty<'vir>,
    pub arg_tys: Vec<ty::Ty<'vir>>, 
}
impl<'vir> task_encoder::OutputRefAny for AsyncStubEncOutputRef<'vir> {}

#[derive(Clone, Debug)]
pub struct AsyncStubEncOutput<'vir> {
    pub method: Method<'vir>,
}

#[derive(Clone, Debug)]
pub struct AsyncStubEncError;

impl TaskEncoder for AsyncStubEnc {
    task_encoder::encoder_cache!(AsyncStubEnc);

    type TaskDescription<'vir> = DefId;

    type OutputRef<'vir> = AsyncStubEncOutputRef<'vir>;
    type OutputFullLocal<'vir> = AsyncStubEncOutput<'vir>;

    type EncodingError = AsyncStubEncError;

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
        let trusted = crate::encoders::with_proc_spec(def_id, |def_spec| {
            def_spec.trusted.extract_inherit().unwrap_or_default()
        })
        .unwrap_or_default();
        vir::with_vcx(|vcx| {
            // get generator type
            let gen_ty = vcx.tcx().type_of(def_id).skip_binder();
            let ty::TyKind::Generator(_def_id, gen_args, _) = gen_ty.kind() else {
                panic!("expected type of async fn to be Generator");
            };
            assert_eq!(def_id, *_def_id);
            // construct the receiver type (std::pin::Pin<&mut Self>)
            let recv_ty = {
                let ref_ty = vcx.tcx().mk_ty_from_kind(ty::TyKind::Ref(
                    ty::Region::new_from_kind(vcx.tcx(), ty::RegionKind::ReErased),
                    gen_ty,
                    mir::Mutability::Mut,
                ));
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
                vcx.tcx().mk_ty_from_kind(ty::TyKind::Adt(
                    vcx.tcx().adt_def(cx_def_id),
                    ty::List::empty(),
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
                AsyncStubEncOutputRef {
                    method_ref,
                    return_ty: ret_ty,
                    arg_tys: vec![recv_ty, cx_ty],
                },
            );

            // encode the stub's specification
            let spec = deps.require_local::<MirSpecEnc>((def_id, substs, None, false, true))?;
            let (spec_pres, spec_posts) = (spec.pres, spec.async_stub_posts);

            // add arguments and preconditions about their types
            // note that the signature is (self: std::pin::Pin<&mut Self>, cx: &mut Context)
            // and not the signature of the generator
            let mut pres = Vec::with_capacity(arg_count - 1);
            let mut args = Vec::with_capacity(arg_count + substs.len());
            for arg_idx in 0..arg_count {
                let name = local_defs.locals[arg_idx.into()].local.name;
                args.push(vir::vir_local_decl! { vcx; [name] : Ref });
                // if arg_idx != 0 {
                //     pres.push(local_defs.locals[arg_idx.into()].impure_pred);
                // }
            }
            pres.push(enc_recv_ty.ref_to_pred(vcx, local_defs.locals[1_u32.into()].local_ex, None));
            // add type parameters (and their typing preconditions)
            args.extend(param_ty_decls.iter());
            pres.extend(spec_pres);

            // add postconditions for the return type and user-annotated ones
            let mut posts = Vec::with_capacity(spec_posts.len() + 1);
            // posts.push(local_defs.locals[mir::RETURN_PLACE].impure_pred);
            posts.push(enc_ret_ty.ref_to_pred(
                vcx,
                local_defs.locals[mir::RETURN_PLACE].local_ex,
                None,
            ));
            posts.extend(spec_posts);

            let method = vcx.mk_method(
                method_ref,
                vcx.alloc_slice(&args),
                &[],
                vcx.alloc_slice(&pres),
                vcx.alloc_slice(&posts),
                None,
            );
            Ok((AsyncStubEncOutput { method }, ()))
        })
    }
}
