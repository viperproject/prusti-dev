//! Custom wrapper for substitutions

use log::debug;
use prusti_interface::environment::Environment;
use rustc_hash::FxHashMap;
use rustc_middle::{
    ty,
    ty::{fold::TypeFoldable, subst},
};
use rustc_span::def_id::DefId;

pub type SubstMap<'tcx> = FxHashMap<ty::Ty<'tcx>, ty::Ty<'tcx>>;

/// Extension methods for `SubstMap`
pub trait SubstMapExt<'v, 'tcx: 'v> {
    /// Updates `substs` with information of `tymap` (SubstMap)
    fn apply_to_substs(
        &self,
        env: &'v Environment<'tcx>,
        substs: subst::SubstsRef<'tcx>,
    ) -> subst::SubstsRef<'tcx>;

    /// Combines `tymap` substitution information with the substitutions inherent to the provided
    /// `DefId`
    fn apply_to_def_id(&self, env: &'v Environment<'tcx>, def_id: DefId) -> subst::SubstsRef<'tcx>;
}

impl<'v, 'tcx: 'v> SubstMapExt<'v, 'tcx> for SubstMap<'tcx> {
    fn apply_to_substs(
        &self,
        env: &'v Environment<'tcx>,
        substs: subst::SubstsRef<'tcx>,
    ) -> subst::SubstsRef<'tcx> {
        debug!("Merging substs = {:?} with tymap = {:?}", substs, self);
        let mut folder = SubstMapFolder::new(env, self);
        let result = substs.super_fold_with(&mut folder);
        debug!("Merged substs = {:?}", result);
        result
    }

    fn apply_to_def_id(&self, env: &'v Environment<'tcx>, def_id: DefId) -> subst::SubstsRef<'tcx> {
        let substs = ty::List::identity_for_item(env.tcx(), def_id);
        self.apply_to_substs(env, substs)
    }
}

struct SubstMapFolder<'v, 'tcx: 'v> {
    env: &'v Environment<'tcx>,
    tymap: &'v SubstMap<'tcx>,

    /// Tymap may contain cycles. This field is used to break them.
    /// # Example:
    /// Given `tymap = {T: Bar<T>}` a query for substituting `T` will result in `Bar<T>`
    already_substituted: FxHashMap<ty::Ty<'tcx>, ty::Ty<'tcx>>,
}

impl<'v, 'tcx: 'v> SubstMapFolder<'v, 'tcx> {
    fn new(env: &'v Environment<'tcx>, tymap: &'v SubstMap<'tcx>) -> Self {
        Self {
            env,
            tymap,
            already_substituted: FxHashMap::default(),
        }
    }
}

impl<'v, 'tcx: 'v> ty::fold::TypeFolder<'tcx> for SubstMapFolder<'v, 'tcx> {
    fn tcx(&self) -> ty::TyCtxt<'tcx> {
        self.env.tcx()
    }

    fn fold_ty(&mut self, t: ty::Ty<'tcx>) -> ty::Ty<'tcx> {
        if self.tymap.is_empty() {
            return t;
        }

        if self.already_substituted.contains_key(t) {
            return self.already_substituted.get(t).unwrap();
        }

        // Fold the "nested" types first
        // i.e. for `Foo<T>`, we recusively fold `T` first
        let t_clone = t.clone();
        let t = t.super_fold_with(self);

        // Mark `t` als already substituted (see field docs)
        self.already_substituted.insert(t_clone, t);

        if self.tymap.contains_key(t) {
            let substitute = self.tymap.get(&t).unwrap();
            substitute.fold_with(self)
        } else {
            t
        }
    }
}
