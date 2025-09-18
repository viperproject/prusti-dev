use prusti_rustc_interface::middle::ty;

use super::GParams;

/// The instantiation of generic arguments, typically found in `TyKind::Adt` and
/// `TyKind::FnDef`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct GArgs<'tcx> {
    pub(super) context: GParams<'tcx>,
    pub(super) args: &'tcx [ty::GenericArg<'tcx>],
}

impl<'tcx> GArgs<'tcx> {
    pub fn new(context: impl Into<GParams<'tcx>>, args: &'tcx [ty::GenericArg<'tcx>]) -> Self {
        GArgs { context: context.into(), args }
    }

    pub(in crate::encoders::ty) fn context(self) -> GParams<'tcx> {
        self.context
    }

    pub fn args(self) -> &'tcx [ty::GenericArg<'tcx>] {
        self.args
    }

    /// Substitutes type arguments and try to normalize associated types
    pub fn normalize(self, ty: ty::Ty<'tcx>) -> ty::Ty<'tcx> {
        // Substitute type parameters
        let ty = vir::with_vcx(|vcx| ty::EarlyBinder::bind(ty).instantiate(vcx.tcx(), self.args));
        // Normalize associated types
        self.context.normalize(ty)
    }

    pub fn expect_param(self) -> ty::ParamTy {
        assert_eq!(self.args.len(), 1);
        match self.args[0].expect_ty().kind() {
            ty::TyKind::Param(p) => *p,
            // TODO: this needs to be changed to support type aliases
            ty::TyKind::Alias(..) => panic!("type aliases are not currently supported"),
            other => panic!("expected type parameter, {other:?}"),
        }
    }
}
