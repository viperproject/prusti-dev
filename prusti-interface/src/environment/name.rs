use prusti_rustc_interface::{
    middle::ty::TyCtxt,
    span::def_id::{CrateNum, DefId},
};
use std::path::PathBuf;

#[derive(Copy, Clone)]
pub struct EnvName<'tcx> {
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> EnvName<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        EnvName { tcx }
    }

    /// Returns the path of the source that is being compiled
    pub fn source_path(self) -> PathBuf {
        self.tcx.sess.local_crate_source_file().unwrap().into_local_path().unwrap()
    }

    /// Returns the file name of the source that is being compiled
    pub fn source_file_name(self) -> String {
        let source_path = self.source_path();
        source_path
            .file_name()
            .unwrap()
            .to_str()
            .unwrap()
            .to_owned()
    }

    /// Returns the name of the crate given a crate number,
    /// in the '_' format (i.e. `prusti_contracts`)
    pub fn crate_name(self, cnum: CrateNum) -> String {
        self.tcx.crate_name(cnum).to_string()
    }

    /// Returns the name of the crate that is being compiled
    pub fn local_crate_name(self) -> String {
        self.crate_name(prusti_rustc_interface::span::def_id::LOCAL_CRATE)
    }

    /// Get an absolute `def_path`. Note: not preserved across compilations!
    pub fn get_item_def_path(self, def_id: DefId) -> String {
        let def_path = self.tcx.def_path(def_id);
        let mut crate_name = self.crate_name(def_path.krate);
        crate_name.push_str(&def_path.to_string_no_crate_verbose());
        crate_name
    }

    /// Get descriptive name prepended with crate name to make it unique.
    pub fn get_unique_item_name(self, def_id: DefId) -> String {
        let def_path = self.tcx.def_path(def_id);
        format!(
            "{}::{}",
            self.crate_name(def_path.krate),
            self.tcx.def_path_str(def_id)
        )
    }

    pub fn get_absolute_item_name(self, def_id: DefId) -> String {
        self.tcx.def_path_str(def_id)
    }

    pub fn get_item_name(self, def_id: DefId) -> String {
        self.tcx.def_path_str(def_id)
        // self.tcx().item_path_str(def_id)
    }

    pub fn local_crate_filename(self) -> String {
        format!(
            "{}{}",
            self.local_crate_name(),
            self.tcx.sess.opts.cg.extra_filename
        )
    }
}
