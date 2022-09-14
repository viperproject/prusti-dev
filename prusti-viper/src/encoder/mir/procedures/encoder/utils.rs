use prusti_rustc_interface::middle::{
    mir,
    ty::{self, TyCtxt},
};

pub(super) fn get_last_deref_with_lifetime<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
    place: mir::Place<'tcx>,
    pointer_deref_lifetime: Option<ty::Region<'tcx>>,
) -> Option<(mir::PlaceRef<'tcx>, ty::Region<'tcx>)> {
    let deref_reference = get_last_reference_deref(tcx, body, place);
    if deref_reference.is_some() {
        deref_reference
    } else if let Some(pointer_deref_lifetime) = pointer_deref_lifetime {
        place
            .iter_projections()
            .rev()
            .filter(|(_, projection)| projection == &mir::ProjectionElem::Deref)
            .last()
            .map(|(place, _)| (place, pointer_deref_lifetime))
    } else {
        None
    }
}

fn get_last_reference_deref<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
    place: mir::Place<'tcx>,
) -> Option<(mir::PlaceRef<'tcx>, ty::Region<'tcx>)> {
    place
        .iter_projections()
        .rev()
        .filter(|(_, projection)| projection == &mir::ProjectionElem::Deref)
        .flat_map(|(place, _)| {
            if let ty::TyKind::Ref(reference_region, _, _) = place.ty(body, tcx).ty.kind() {
                Some((place, *reference_region))
            } else {
                None
            }
        })
        .last()
}
