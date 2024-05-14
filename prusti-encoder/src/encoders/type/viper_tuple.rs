use task_encoder::{
    TaskEncoder,
    TaskEncoderDependencies,
    EncodeFullResult,
};

use super::{domain::{DomainDataStruct, DomainEnc}, most_generic_ty::MostGenericTy};

pub struct ViperTupleEnc;

#[derive(Clone, Debug)]
pub struct ViperTupleEncOutput<'vir> {
    tuple: Option<DomainDataStruct<'vir>>,
}

impl<'vir> ViperTupleEncOutput<'vir> {
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
            let ret = deps.require_dep::<DomainEnc>(MostGenericTy::tuple(*task_key))?;
            Ok((ViperTupleEncOutput { tuple: Some(ret.expect_structlike()) }, ()))
        }
    }
}
