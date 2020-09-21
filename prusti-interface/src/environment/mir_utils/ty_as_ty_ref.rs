use rustc_middle::mir::terminator::Mutability;
use rustc_middle::ty::Region;
use rustc_middle::ty::Ty;
use rustc_middle::ty::TyKind;

pub trait TyAsRef<'tcx> {
    fn as_ty_ref(&self) -> Option<(Region<'tcx>, Ty<'tcx>, Mutability)>;
}

impl<'tcx> TyAsRef<'tcx> for Ty<'tcx> {
    fn as_ty_ref(&self) -> Option<(Region<'tcx>, Ty<'tcx>, Mutability)> {
        match self.kind() {
            TyKind::Ref(region, ty, mutability) =>
                Some((region, ty, *mutability)),
            _ => None
        }
    }
}
