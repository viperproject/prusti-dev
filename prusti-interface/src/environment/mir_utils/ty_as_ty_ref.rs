use prusti_rustc_interface::middle::mir::terminator::Mutability;
use prusti_rustc_interface::middle::ty::Region;
use prusti_rustc_interface::middle::ty::Ty;
use prusti_rustc_interface::middle::ty::TyKind;

pub trait TyAsRef<'tcx> {
    fn as_ty_ref(&self) -> Option<(Region<'tcx>, Ty<'tcx>, Mutability)>;
}

impl<'tcx> TyAsRef<'tcx> for Ty<'tcx> {
    fn as_ty_ref(&self) -> Option<(Region<'tcx>, Ty<'tcx>, Mutability)> {
        match self.kind() {
            TyKind::Ref(region, ty, mutability) =>
                Some((*region, *ty, *mutability)),
            _ => None
        }
    }
}
