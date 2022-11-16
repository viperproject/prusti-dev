use prusti_rustc_interface::middle::mir;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct MirPlace<'tcx> {
    pub local: mir::Local,
    pub projection: Vec<mir::PlaceElem<'tcx>>,
}

impl<'tcx> From<mir::Place<'tcx>> for MirPlace<'tcx> {
    fn from(place: mir::Place<'tcx>) -> Self {
        MirPlace {
            local: place.local,
            projection: place.projection.to_vec(),
        }
    }
}
