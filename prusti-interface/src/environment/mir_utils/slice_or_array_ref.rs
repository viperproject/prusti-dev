use prusti_rustc_interface::middle::ty::{Ty, TyKind};

pub trait SliceOrArrayRef<'tcx> {
    fn is_slice_ref(&self) -> bool;
    fn is_array_ref(&self) -> bool;
    fn is_slice_or_ref(&self) -> bool;
    fn is_array_or_ref(&self) -> bool;
}

impl<'tcx> SliceOrArrayRef<'tcx> for Ty<'tcx> {
    fn is_slice_ref(&self) -> bool {
        match self.kind() {
            TyKind::Ref(_, ty, _) => matches!(ty.kind(), TyKind::Slice(_)),
            _ => false,
        }
    }

    fn is_array_ref(&self) -> bool {
        match self.kind() {
            TyKind::Ref(_, ty, _) => matches!(ty.kind(), TyKind::Array(..)),
            _ => false,
        }
    }

    fn is_slice_or_ref(&self) -> bool {
        self.is_slice() || self.is_slice_ref()
    }

    fn is_array_or_ref(&self) -> bool {
        self.is_array() || self.is_array_ref()
    }
}
