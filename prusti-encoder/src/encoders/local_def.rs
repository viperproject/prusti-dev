use prusti_rustc_interface::{
    index::IndexVec,
    middle::{mir, ty},
    span::def_id::DefId
};

use task_encoder::{TaskEncoder, TaskEncoderDependencies};
use std::cell::RefCell;

use crate::encoders::TypeEncoderOutputRef;

pub struct MirLocalDefEncoder;
#[derive(Clone, Copy)]
pub struct MirLocalDefEncoderOutput<'vir> {
    pub locals: &'vir IndexVec<mir::Local, LocalDef<'vir>>,
    pub arg_count: usize,
}
pub type MirLocalDefEncoderError = ();

#[derive(Clone, Copy)]
pub struct LocalDef<'vir> {
    pub local: vir::Local<'vir>,
    pub local_ex: vir::Expr<'vir>,
    pub impure_snap: vir::Expr<'vir>,
    pub impure_pred: vir::Expr<'vir>,
    pub ty: &'vir crate::encoders::TypeEncoderOutputRef<'vir>,
}

thread_local! {
    static CACHE: task_encoder::CacheStaticRef<MirLocalDefEncoder> = RefCell::new(Default::default());
}

impl TaskEncoder for MirLocalDefEncoder {
    type TaskDescription<'tcx> = (
        DefId, // ID of the function
        ty::GenericArgsRef<'tcx>, // ? this should be the "signature", after applying the env/substs
        Option<DefId>, // ID of the caller function, if any
    );

    type OutputFullLocal<'vir> = MirLocalDefEncoderOutput<'vir>;

    type EncodingError = MirLocalDefEncoderError;

    fn with_cache<'tcx: 'vir, 'vir, F, R>(f: F) -> R
    where
        F: FnOnce(&'vir task_encoder::CacheRef<'tcx, 'vir, MirLocalDefEncoder>) -> R,
    {
        CACHE.with(|cache| {
            // SAFETY: the 'vir and 'tcx given to this function will always be
            //   the same (or shorter) than the lifetimes of the VIR arena and
            //   the rustc type context, respectively
            let cache = unsafe { std::mem::transmute(cache) };
            f(cache)
        })
    }

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'tcx: 'vir, 'vir>(
        task_key: &Self::TaskKey<'tcx>,
        deps: &mut TaskEncoderDependencies<'vir>,
    ) -> Result<
        (
            Self::OutputFullLocal<'vir>,
            Self::OutputFullDependency<'vir>,
        ),
        (
            Self::EncodingError,
            Option<Self::OutputFullDependency<'vir>>,
        ),
    > {
        let (def_id, substs, caller_def_id) = *task_key;
        deps.emit_output_ref::<Self>(*task_key, ());
        fn mk_local_def<'vir, 'tcx>(vcx: &'vir vir::VirCtxt<'tcx>, name: &'vir str, ty: TypeEncoderOutputRef<'vir>) -> LocalDef<'vir> {
            let local = vcx.mk_local(name);
            let local_ex = vcx.mk_local_ex_local(local);
            let impure_snap = ty.ref_to_snap.apply(vcx, [local_ex]);
            let impure_pred = vcx.mk_predicate_app_expr(ty.ref_to_pred.apply(vcx, [local_ex]));
            LocalDef {
                local,
                local_ex,
                impure_snap,
                impure_pred,
                ty: vcx.alloc(ty),
            }
        }

        vir::with_vcx(|vcx| {
            let data = if let Some(local_def_id) = def_id.as_local() {
                let body = vcx.body.borrow_mut().get_impure_fn_body(local_def_id, substs, caller_def_id);
                let locals = IndexVec::from_fn_n(|arg: mir::Local| {
                    let local = vir::vir_format!(vcx, "_{}p", arg.index());
                    let ty = deps.require_ref::<crate::encoders::TypeEncoder>(
                        body.local_decls[arg].ty,
                    ).unwrap();
                    mk_local_def(vcx, local, ty)
                }, body.local_decls.len());
                MirLocalDefEncoderOutput {
                    locals: vcx.alloc(locals),
                    arg_count: body.arg_count,
                }
            } else {
                let param_env = vcx.tcx.param_env(caller_def_id.unwrap_or(def_id));
                let sig = vcx.tcx
                    .subst_and_normalize_erasing_regions(substs, param_env, vcx.tcx.fn_sig(def_id));
                let sig = sig.skip_binder();

                let locals = IndexVec::from_fn_n(|arg: mir::Local| {
                    let local = vir::vir_format!(vcx, "_{}p", arg.index());
                    let ty = if arg.index() == 0 {
                        sig.output()
                    } else {
                        sig.inputs()[arg.index() - 1]
                    };
                    let ty = deps.require_ref::<crate::encoders::TypeEncoder>(
                        ty,
                    ).unwrap();
                    mk_local_def(vcx, local, ty)
                }, sig.inputs_and_output.len());

                MirLocalDefEncoderOutput {
                    locals: vcx.alloc(locals),
                    arg_count: sig.inputs().len(),
                }
            };
            Ok((data, ()))
        })
    }
}
