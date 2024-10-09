use prusti_rustc_interface::{
    index::IndexVec,
    middle::{mir, ty},
    span::def_id::DefId
};

use task_encoder::{TaskEncoder, TaskEncoderDependencies, EncodeFullResult};

use crate::encoders::{
    rust_ty_predicates::{RustTyPredicatesEnc, RustTyPredicatesEncOutputRef},
    PredicateEncOutputRef,
};

pub struct MirLocalDefEnc;
#[derive(Clone, Copy)]
pub struct MirLocalDefEncOutput<'vir> {
    pub locals: &'vir IndexVec<mir::Local, LocalDef<'vir>>,
    pub arg_count: usize,
}
pub type MirLocalDefEncError = ();

#[derive(Clone, Copy)]
pub struct LocalDef<'vir> {
    pub local: vir::Local<'vir>,
    pub local_ex: vir::Expr<'vir>,
    pub impure_snap: vir::Expr<'vir>,
    pub impure_pred: vir::Expr<'vir>,
    pub ty: &'vir PredicateEncOutputRef<'vir>,
}

impl TaskEncoder for MirLocalDefEnc {
    task_encoder::encoder_cache!(MirLocalDefEnc);

    type TaskDescription<'vir> = (
        DefId, // ID of the function
        ty::GenericArgsRef<'vir>, // ? this should be the "signature", after applying the env/substs
        Option<DefId>, // ID of the caller function, if any
    );

    type OutputFullLocal<'vir> = MirLocalDefEncOutput<'vir>;

    type EncodingError = MirLocalDefEncError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        let (def_id, substs, caller_def_id) = *task_key;
        deps.emit_output_ref(*task_key, ())?;

        fn mk_local_def<'vir>(
            vcx: &'vir vir::VirCtxt<'vir>,
            name: &'vir str,
            ty: RustTyPredicatesEncOutputRef<'vir>,
        ) -> LocalDef<'vir> {
            let local = vcx.mk_local(name, &vir::TypeData::Ref);
            let local_ex = vcx.mk_local_ex_local(local);
            let impure_snap = ty.ref_to_snap(vcx, local_ex);
            let impure_pred = ty.ref_to_pred(vcx, local_ex, None);
            LocalDef {
                local,
                local_ex,
                impure_snap,
                impure_pred,
                ty: vcx.alloc(ty.generic_predicate),
            }
        }

        vir::with_vcx(|vcx| {
            let data = if let Some(local_def_id) = def_id.as_local() {
                let body = vcx.body_mut().get_impure_fn_body(local_def_id, substs, caller_def_id);
                let locals = IndexVec::from_fn_n(|arg: mir::Local| {
                    let local = vir::vir_format!(vcx, "_{}p", arg.index());
                    let ty = deps.require_ref::<RustTyPredicatesEnc>(
                        body.local_decls[arg].ty,
                    ).unwrap();
                    mk_local_def(vcx, local, ty)
                }, body.local_decls.len());
                MirLocalDefEncOutput {
                    locals: vcx.alloc(locals),
                    arg_count: body.arg_count,
                }
            } else {
                let param_env = vcx.tcx().param_env(caller_def_id.unwrap_or(def_id));
                let sig = vcx.tcx()
                    .instantiate_and_normalize_erasing_regions(substs, param_env, vcx.tcx().fn_sig(def_id));
                let sig = sig.skip_binder();

                let locals = IndexVec::from_fn_n(|arg: mir::Local| {
                    let local = vir::vir_format!(vcx, "_{}p", arg.index());
                    let ty = if arg.index() == 0 {
                        sig.output()
                    } else {
                        sig.inputs()[arg.index() - 1]
                    };
                    let ty = deps.require_ref::<RustTyPredicatesEnc>(
                        ty,
                    ).unwrap();
                    mk_local_def(vcx, local, ty)
                }, sig.inputs_and_output.len());

                MirLocalDefEncOutput {
                    locals: vcx.alloc(locals),
                    arg_count: sig.inputs().len(),
                }
            };
            Ok((data, ()))
        })
    }
}
