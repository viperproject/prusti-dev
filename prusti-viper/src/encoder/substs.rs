//! Custom wrapper for substitutions

use prusti_interface::environment::Environment;
use rustc_hash::{FxHashMap};
use rustc_middle::ty;
use rustc_middle::ty::subst;
use rustc_middle::ty::fold::TypeFoldable;

pub type SubstMap<'tcx> = FxHashMap<ty::Ty<'tcx>, ty::Ty<'tcx>>;

/// Extension methods for `SubstMap`
pub trait SubstMapExt<'v, 'tcx: 'v> {
    /// Updates `substs` with information of `tymap` (SubstMap)
    fn apply_to_substs(&self, env: &'v Environment<'tcx>, substs: subst::SubstsRef<'tcx>) -> subst::SubstsRef<'tcx>;
}

impl<'v, 'tcx: 'v> SubstMapExt<'v, 'tcx> for SubstMap<'tcx> {
    fn apply_to_substs(&self, env: &'v Environment<'tcx>, substs: subst::SubstsRef<'tcx>) -> subst::SubstsRef<'tcx> {
        let mut folder = SubstMapFolder {
            env,
            tymap: self,
        };
        substs.super_fold_with(&mut folder)
    }
}

struct SubstMapFolder<'v, 'tcx: 'v> {
    env: &'v Environment<'tcx>,
    tymap: &'v SubstMap<'tcx>,
}

impl<'v, 'tcx: 'v> ty::fold::TypeFolder<'tcx> for SubstMapFolder<'v, 'tcx> {
    fn tcx(&self) -> ty::TyCtxt<'tcx> {
        self.env.tcx()
    }

    fn fold_ty(&mut self, t: ty::Ty<'tcx>) -> ty::Ty<'tcx> {
        if self.tymap.contains_key(t) {
            let substitute = self.tymap.get(&t).unwrap();
            substitute.super_fold_with(self)
        } else {
            t.super_fold_with(self)
        }
    }
}