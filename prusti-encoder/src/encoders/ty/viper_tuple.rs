use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::CastType;

use prusti_rustc_interface::{abi, middle::ty, span::def_id::DefId};

use crate::encoders::ty::{
    RustTyDecomposition,
    use_pure::{TyUsePure, TyUsePureEnc, TyUsePureStruct},
};

pub struct ViperTupleEnc;

#[derive(Clone, Debug)]
pub struct ViperTupleEncOutput<'vir> {
    domain_data: TyUsePure<'vir>,
}

impl<'vir> ViperTupleEncOutput<'vir> {
    fn structlike(&self) -> &TyUsePureStruct<'vir> {
        self.domain_data.expect_structlike()
    }

    pub fn snapshot(&self) -> vir::TypeSnap<'vir> {
        self.domain_data.snapshot
    }

    pub fn mk_cons<'tcx, Curr, Next>(
        &self,
        _vcx: &'vir vir::VirCtxt<'tcx>,
        elems: Vec<vir::ExprGenSnap<'vir, Curr, Next>>,
    ) -> vir::ExprGenSnap<'vir, Curr, Next> {
        self.structlike().field_snaps_to_snap(elems).upcast_ty()
    }

    pub fn mk_elem<'tcx, Curr, Next>(
        &self,
        _vcx: &'vir vir::VirCtxt<'tcx>,
        tuple: vir::ExprGenSnap<'vir, Curr, Next>,
        elem: usize,
    ) -> vir::ExprGenSnap<'vir, Curr, Next> {
        self.structlike()[abi::FieldIdx::from_usize(elem)].read(tuple.downcast_ty())
    }

    pub fn mk_unreachable<'tcx, Curr, Next>(
        &self,
        _vcx: &'vir vir::VirCtxt<'tcx>,
    ) -> vir::ExprGenSnap<'vir, Curr, Next> {
        self.domain_data.unreachable_to_snap()
    }
}

impl TaskEncoder for ViperTupleEnc {
    task_encoder::encoder_cache!(ViperTupleEnc);

    type TaskDescription<'vir> = (DefId, Vec<ty::Ty<'vir>>);
    type TaskKey<'vir> = RustTyDecomposition<'vir>;

    type OutputFullDependency<'vir> = ViperTupleEncOutput<'vir>;
    type EncodingError = ();

    fn task_to_key<'vir>((def_id, tys): &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        vir::with_vcx(|vcx| {
            let tys = vcx.tcx().mk_type_list(tys);
            let ty = vcx.tcx().mk_ty_from_kind(ty::TyKind::Tuple(tys));
            RustTyDecomposition::from_ty(ty, *def_id)
        })
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        let domain_data = deps.require_dep::<TyUsePureEnc>(*task_key)?;
        Ok(((), ViperTupleEncOutput { domain_data }))
    }
}
