use prusti_rustc_interface::{
    index::IndexVec,
    middle::mir,
    span::def_id::DefId
};

use task_encoder::{TaskEncoder, TaskEncoderDependencies};
use std::cell::RefCell;

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
    pub snapshot: &'vir vir::TypeData<'vir>,
    pub local_ex: vir::Expr<'vir>,
    pub impure_snap: vir::Expr<'vir>,
    pub impure_pred: vir::Expr<'vir>,
    pub ty: &'vir crate::encoders::TypeEncoderOutputRef<'vir>,
}

thread_local! {
    static CACHE: task_encoder::CacheStaticRef<MirLocalDefEncoder> = RefCell::new(Default::default());
}

impl TaskEncoder for MirLocalDefEncoder {
    type TaskDescription<'vir> = DefId;

    type OutputFullLocal<'vir> = MirLocalDefEncoderOutput<'vir>;

    type EncodingError = MirLocalDefEncoderError;

    fn with_cache<'vir, F, R>(f: F) -> R
    where
        F: FnOnce(&'vir task_encoder::CacheRef<'vir, MirLocalDefEncoder>) -> R,
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

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
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
        let def_id = *task_key;
        deps.emit_output_ref::<Self>(def_id, ());

        vir::with_vcx(|vcx| {
            let local_def_id = def_id.expect_local();           
            let body = vcx.body.borrow_mut().get_impure_fn_body_identity(local_def_id);
            let locals = IndexVec::from_fn_n(|arg: mir::Local| {
                let local = vcx.mk_local(vir::vir_format!(vcx, "_{}p", arg.index()));
                let ty = deps.require_ref::<crate::encoders::TypeEncoder>(
                    body.local_decls[arg].ty,
                ).unwrap();
                let snapshot = ty.snapshot;
                let local_ex = vcx.mk_local_ex_local(local);
                let impure_snap = ty.ref_to_snap.apply(vcx, [local_ex]);
                let impure_pred = vcx.alloc(vir::ExprData::PredicateApp(
                    ty.ref_to_pred.apply(vcx, [local_ex])
                ));
                LocalDef {
                    local,
                    snapshot,
                    local_ex,
                    impure_snap,
                    impure_pred,
                    ty: vcx.alloc(ty),
                }
            }, body.local_decls.len());
            let data = MirLocalDefEncoderOutput {
                locals: vcx.alloc(locals),
                arg_count: body.arg_count,
            };
            Ok((data, ()))
        })
    }
}
