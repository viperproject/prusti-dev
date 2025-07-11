use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::CastType;

use super::{
    domain::{DomainDataStruct, DomainEnc},
    most_generic_ty::MostGenericTy,
    rust_ty_snapshots::RustTySnapshotsEnc,
};

pub struct ViperTupleEnc;

#[derive(Clone, Debug)]
pub struct ViperTupleEncOutput<'vir> {
    tuple: Option<(vir::TypeSnap<'vir>, DomainDataStruct<'vir>)>,
}

impl<'vir> ViperTupleEncOutput<'vir> {
    pub fn snapshot(&self) -> Option<vir::TypeSnap<'vir>> {
        self.tuple.map(|t| t.0)
    }

    pub fn mk_cons<'tcx, Curr, Next>(
        &self,
        _vcx: &'vir vir::VirCtxt<'tcx>,
        elems: &[vir::ExprGenSnap<'vir, Curr, Next>],
    ) -> vir::ExprGenSnap<'vir, Curr, Next> {
        self.tuple
            .map(|t| (t.1.field_snaps_to_snap.gen())(elems).upcast_ty())
            .unwrap_or_else(|| elems[0])
    }

    pub fn mk_elem<'tcx, Curr, Next>(
        &self,
        _vcx: &'vir vir::VirCtxt<'tcx>,
        tuple: vir::ExprGenSnap<'vir, Curr, Next>,
        elem: usize,
    ) -> vir::ExprGenSnap<'vir, Curr, Next> {
        self.tuple
            .map(|t| t.1.field_access[elem].gen()(tuple.downcast_ty()))
            .unwrap_or_else(|| tuple)
    }
}

impl TaskEncoder for ViperTupleEnc {
    task_encoder::encoder_cache!(ViperTupleEnc);

    type TaskDescription<'vir> = usize;

    type OutputFullLocal<'vir> = ViperTupleEncOutput<'vir>;
    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        if *task_key == 1 {
            Ok((ViperTupleEncOutput { tuple: None }, ()))
        } else {
            let most_generic_ty = MostGenericTy::tuple(*task_key);
            let ret_ref = deps.require_ref::<RustTySnapshotsEnc>(most_generic_ty.ty())?;
            let snapshot = ret_ref.generic_snapshot.snapshot;
            let ret = deps.require_dep::<DomainEnc>(most_generic_ty)?;
            Ok((
                ViperTupleEncOutput {
                    tuple: Some((snapshot, ret.expect_structlike())),
                },
                (),
            ))
        }
    }
}
