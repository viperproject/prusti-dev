use prusti_rustc_interface::{
    abi::FieldIdx,
    middle::{mir, ty},
};

pub trait AllPlaces<'tcx> {
    /// Returns all places that are below the given local variable. Right now, this only handles
    /// tuples. For a local variable `_2: u32`, `Place::Local(_2).all_places(&mir) == [_2]`. For a
    /// local variable `_2: (u32, u32)`, `Place::Local(_2).all_places(&mir) == [_2, _2.0, _2.1]`.
    fn all_places(self, tcx: ty::TyCtxt<'tcx>, mir: &mir::Body<'tcx>) -> Vec<mir::Place<'tcx>>;
}

impl<'tcx> AllPlaces<'tcx> for mir::Local {
    fn all_places(self, tcx: ty::TyCtxt<'tcx>, mir: &mir::Body<'tcx>) -> Vec<mir::Place<'tcx>> {
        let mut places = vec![self.into()];
        let ty = mir.local_decls[self].ty;
        if let ty::TyKind::Tuple(types) = ty.kind() {
            for (i, ty) in types.iter().enumerate() {
                let field = FieldIdx::from_usize(i);
                let place = tcx.mk_place_field(self.into(), field, ty);
                places.push(place);
            }
        }
        places
    }
}
