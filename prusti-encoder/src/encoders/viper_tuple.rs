use prusti_rustc_interface::middle::ty;
use task_encoder::{
    TaskEncoder,
    TaskEncoderDependencies,
};
use std::cell::RefCell;

use crate::encoders::DomainEnc;

use super::{domain::DomainDataStruct, SnapshotEnc};

pub struct ViperTupleEncoder;

#[derive(Clone, Debug)]
pub struct ViperTupleEncoderOutput<'vir> {
    tuple: Option<DomainDataStruct<'vir>>,
}

impl<'vir> ViperTupleEncoderOutput<'vir> {
    pub fn mk_cons<'tcx, Curr, Next>(
        &self,
        vcx: &'vir vir::VirCtxt<'tcx>,
        elems: &[vir::ExprGen<'vir, Curr, Next>]
    ) -> vir::ExprGen<'vir, Curr, Next> {
        self.tuple
            .map(|t| t.field_snaps_to_snap.apply(vcx, elems))
            .unwrap_or_else(|| elems[0])
    }

    pub fn mk_elem<'tcx, Curr, Next>(
        &self,
        vcx: &'vir vir::VirCtxt<'tcx>,
        tuple: vir::ExprGen<'vir, Curr, Next>,
        elem: usize,
    ) -> vir::ExprGen<'vir, Curr, Next> {
        self.tuple
            .map(|t| t.field_access[elem].read.apply(vcx, [tuple]))
            .unwrap_or_else(|| tuple)
    }
}

thread_local! {
    static CACHE: task_encoder::CacheStaticRef<ViperTupleEncoder> = RefCell::new(Default::default());
}

impl TaskEncoder for ViperTupleEncoder {
    type TaskDescription<'vir> = usize;

    type OutputFullLocal<'vir> = ViperTupleEncoderOutput<'vir>;
    type EncodingError = ();

    fn with_cache<'tcx, 'vir, F, R>(f: F) -> R
       where F: FnOnce(&'vir task_encoder::CacheRef<'tcx, 'vir, ViperTupleEncoder>) -> R,
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
    ) -> Result<(
        Self::OutputFullLocal<'vir>,
        Self::OutputFullDependency<'vir>,
    ), (
        Self::EncodingError,
        Option<Self::OutputFullDependency<'vir>>,
    )> {
        deps.emit_output_ref::<Self>(*task_key, ());
        if *task_key == 1 {
            Ok((ViperTupleEncoderOutput { tuple: None }, ()))
        } else {
            let tuple = vir::with_vcx(|vcx| {
                let new_tys = vcx.tcx.mk_type_list_from_iter((0..*task_key).map(|index|
                    SnapshotEnc::to_placeholder(vcx.tcx, Some(index))
                ));
                vcx.tcx.mk_ty_from_kind(ty::TyKind::Tuple(new_tys))
            });
            let ret = deps.require_dep::<DomainEnc>(tuple).unwrap();
            Ok((ViperTupleEncoderOutput { tuple: Some(ret.expect_structlike()) }, ()))
        }
    }
}
