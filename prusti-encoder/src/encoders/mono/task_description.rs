use std::fmt::Write;
use prusti_rustc_interface::{
    span::def_id::DefId,
    middle::ty
};
use vir::VirCtxt;

#[derive(Hash, PartialEq, Eq, Clone, Copy, Debug)]
pub struct FunctionCallTaskDescription<'tcx> {
    pub def_id: DefId,
    // Substitutions at the call site
    pub substs: ty::GenericArgsRef<'tcx>,
    pub caller_def_id: DefId,
}

impl <'tcx> FunctionCallTaskDescription<'tcx> {
    pub fn new(def_id: DefId, substs: ty::GenericArgsRef<'tcx>, caller_def_id: DefId) -> Self {
        Self { def_id, substs, caller_def_id }
    }

    pub fn vir_function_ident<'vir>(&self, vcx: &'vir VirCtxt<'tcx>) -> vir::ViperIdent<'vir> {
        vir::vir_format_identifier!(vcx, "f_{}", self.get_mangled_name(vcx))
    }
    pub fn vir_method_ident<'vir>(&self, vcx: &'vir VirCtxt<'tcx>) -> vir::ViperIdent<'vir> {
        vir::vir_format_identifier!(vcx, "m_{}", self.get_mangled_name(vcx))
    }

    fn get_mangled_name(&self, vcx: &VirCtxt<'tcx>) -> String {
        let mut name = vcx.tcx().def_path_str_with_args(self.def_id, self.substs);
        write!(name, "_CALLER_{}_{}", self.caller_def_id.krate, self.caller_def_id.index.index()).unwrap();
        name
    }

}
