use std::collections::HashMap;

use rustc_middle::{mir, ty, ty::TyCtxt};
use rustc_hir::{def_id::DefId};
use rustc_mir::borrow_check::facts::AllFacts;
use rustc_mir::borrow_check::location::LocationTable;

mod extract;
mod derive;

pub(super) use self::extract::enrich_mir_body;

/// A wrapper around MIR body that hides unnecessary details.
pub struct MirBody<'tcx> {
    def_id: DefId,
    // Information obtained from the borrow checker.
    body: mir::Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    universal_regions: Vec<ty::RegionVid>,
    universal_regions_outlives: Vec<(ty::RegionVid, ty::RegionVid)>,
    polonius_facts: AllFacts,
    location_table: LocationTable,
    // Derived information.
    /// The names of local variables.
    local_names: HashMap<mir::Local, String>,
}

pub struct Variable<'body, 'tcx> {
    id: mir::Local,
    decl: &'body mir::LocalDecl<'tcx>,
    body: &'body MirBody<'tcx>,
}

impl<'tcx> MirBody<'tcx> {
    pub fn iter_locals<'a>(&'a self) -> impl Iterator<Item=Variable<'a, 'tcx>> {
        self.body.local_decls.iter_enumerated().map(move |(id, decl)| {
            Variable {
                id,
                decl,
                body: self,
            }
        })
    }
}

impl<'body, 'tcx> Variable<'body, 'tcx> {
    /// Return the user-friendly name of the variable.
    pub fn name(&self) -> Option<&str> {
        self.body.local_names.get(&self.id).map(|s| s.as_ref())
    }
    /// Return the identifier of the variable.
    pub fn id(&self) -> mir::Local {
        self.id
    }
    /// Return the type of the variable.
    pub fn ty(&self) -> ty::Ty<'tcx> {
        self.decl.ty
    }
}