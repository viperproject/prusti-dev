use prusti_rustc_interface::middle::ty;

pub trait TupleItemsForTy<'tcx> {
    /// Tries to interpret the given `mir::Ty` as a tuple type. If this succeeds, it returns the
    /// nested types making up the tuple. If this failes, it returns `None`.
    fn tuple_items(&self) -> Option<Vec<ty::Ty<'tcx>>>;
}

impl<'tcx> TupleItemsForTy<'tcx> for ty::Ty<'tcx> {
    fn tuple_items(&self) -> Option<Vec<ty::Ty<'tcx>>> {
        if let ty::TyKind::Tuple(types) = self.kind() {
            Some(types.to_vec())
        } else {
            None
        }
    }
}
