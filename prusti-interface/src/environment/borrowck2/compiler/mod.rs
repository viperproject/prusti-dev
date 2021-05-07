use rustc_middle::{mir, ty, ty::TyCtxt};
use rustc_hir::{def_id::DefId};
use rustc_mir::borrow_check::facts::AllFacts;
use rustc_mir::borrow_check::location::LocationTable;

mod extract;

pub(super) use self::extract::enrich_mir_body;

/// A wrapper around MIR body that hides unnecessary details.
pub struct MirBody<'tcx> {
    def_id: DefId,
    body: mir::Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    universal_regions: Vec<ty::RegionVid>,
    universal_regions_outlives: Vec<(ty::RegionVid, ty::RegionVid)>,
    polonius_facts: AllFacts,
    location_table: LocationTable,
}
