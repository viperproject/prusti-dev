use prusti_rustc_interface::{middle::ty, span::def_id::DefId};

use crate::encoders::ty::{LazyRustTy, generics::GParams};

pub struct RustSignature<'tcx> {
    pub gparams: GParams<'tcx>,
    pub inputs: &'tcx [LazyRustTy<'tcx>],
    pub output: LazyRustTy<'tcx>,
}

impl<'tcx> RustSignature<'tcx> {
    pub fn new(def_id: DefId) -> Self {
        let fn_sig = vir::with_vcx(|vcx| {
            vcx.tcx()
                .fn_sig(def_id)
                .instantiate_identity()
                .skip_binder()
        });
        let gparams = GParams::from(def_id);
        let inputs = LazyRustTy::new_slice(fn_sig.inputs());
        let output = LazyRustTy::new(fn_sig.output());
        Self {
            gparams,
            inputs,
            output,
        }
    }

    pub fn get_def_id_and_caller_substs(ty: ty::Ty<'tcx>) -> (DefId, ty::GenericArgsRef<'tcx>) {
        match ty.kind() {
            ty::TyKind::FnDef(def_id, substs) => (*def_id, substs),
            _ => todo!(),
        }
    }
}
