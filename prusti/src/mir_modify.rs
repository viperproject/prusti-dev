use prusti_rustc_interface::{
    interface::DEFAULT_QUERY_PROVIDERS,
    middle::{
        ty::{self, TyCtxt},
        mir::{
            Body,
            visit::MutVisitor,
        },
    },
    span::def_id::LocalDefId,
    data_structures::steal::Steal,
};


/// Compute the main MIR body and the list of MIR bodies of the promoteds.
pub(crate) fn mir_built(
    tcx: TyCtxt<'_>,
    def: ty::WithOptConstParam<LocalDefId>,
) -> &Steal<Body<'_>> {
    // is it our job to store it?
    let steal = ((*DEFAULT_QUERY_PROVIDERS).mir_built)(tcx, def);
    let mut stolen = steal.steal();

    let mut visitor = InsertChecksVisitor { tcx };
    visitor.visit_body(&mut stolen);

    tcx.alloc_steal_mir(stolen)
}


struct InsertChecksVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> MutVisitor<'tcx> for InsertChecksVisitor<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }
    fn visit_body(&mut self, body: &mut Body<'tcx>) {
        self.super_body(body);
    }
}
