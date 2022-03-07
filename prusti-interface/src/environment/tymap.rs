use super::{traits, Environment};
use crate::data::ProcedureDefId;
use log::{trace, warn};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_middle::{ty, ty::subst::SubstsRef};

type Key<'tcx> = ty::Ty<'tcx>;
type Value<'tcx> = ty::Ty<'tcx>;

#[derive(Default, Clone, Debug)]
pub struct SubstMap<'tcx> {
    map: FxHashMap<Key<'tcx>, Value<'tcx>>,
}

impl<'tcx> SubstMap<'tcx> {
    /// Builds a SubstMap from a call to a function.
    /// The built tymap considers whether the called function resolves to a trait implementation
    /// and adds the necessary substitutions.
    pub fn build<'a>(
        env: &'a Environment<'tcx>,
        def_id: ProcedureDefId,
        call_substs: SubstsRef<'tcx>,
    ) -> Self {
        trace!(
            "Building tymap for {:?} with substs {:?}",
            def_id,
            call_substs
        );

        let mut tymap = Self::default();

        // Add generic information from the call to this method
        let own_substs = ty::List::identity_for_item(env.tcx(), def_id);
        own_substs
            .iter()
            .zip(call_substs)
            .for_each(|(generic_arg, call_arg)| tymap.insert_arg(generic_arg, call_arg));

        // In case this is a trait method implementation, we also extend
        // tymap with information from the implementation itself
        let maybe_impl_did = if call_substs.is_empty() {
            None
        } else {
            env.find_impl_of_trait_method_call(def_id, call_substs)
        };

        if let Some(impl_did) = maybe_impl_did {
            let impl_own_substs = ty::List::identity_for_item(env.tcx(), impl_did);
            let trait_did = env.tcx().trait_of_item(def_id).unwrap();
            let trait_ref = ty::TraitRef::from_method(env.tcx(), trait_did, call_substs);
            let trait_binder = ty::Binder::dummy(trait_ref);
            let param_env = env.tcx().param_env(impl_did);
            let obligation =
                traits::codegen_fulfill_obligation(env.tcx(), (param_env, trait_binder));
            let obligation_substs =
                if let Ok(rustc_middle::traits::ImplSource::UserDefined(ud)) = obligation {
                    trace!(
                        "Additional substs declared on trait method impl: {:?}",
                        ud.substs
                    );
                    ud.substs
                } else {
                    call_substs
                };

            impl_own_substs
                .iter()
                .zip(obligation_substs)
                .for_each(|(impl_arg, obligation_arg)| tymap.insert_arg(impl_arg, obligation_arg));
        }

        trace!("\t-> {:?}", tymap);
        tymap
    }

    pub fn get(&self, ty: &Key<'tcx>) -> Option<&Value<'tcx>> {
        self.map.get(ty)
    }

    pub fn insert_ty(&mut self, k: Key<'tcx>, v: Value<'tcx>) -> Option<Value<'tcx>> {
        self.map.insert(k, v)
    }

    pub fn insert_arg(&mut self, k: ty::subst::GenericArg<'tcx>, v: ty::subst::GenericArg<'tcx>) {
        if let (ty::subst::GenericArgKind::Type(ty1), ty::subst::GenericArgKind::Type(ty2)) =
            (k.unpack(), v.unpack())
        {
            if ty1 != ty2 {
                self.insert_ty(ty1, ty2);
            }
        }
    }

    pub fn extend(&mut self, other: SubstMap<'tcx>) {
        self.map.extend(other.map);
    }

    /// Transitively resolves a type.
    /// In case there are cyclic dependencies, returns the last visited type.
    pub fn resolve(&self, ty: &Key<'tcx>) -> Option<&Value<'tcx>> {
        trace!("Resolving type {:?} with tymap {:?}", ty, self);
        let mut result = self.map.get(ty);

        // Handle cyclic dependencies with a set of already visited types
        let mut visited: FxHashSet<Key<'tcx>> = FxHashSet::default();
        while result.is_some() && self.map.contains_key(result.unwrap()) {
            visited.insert(result.unwrap());

            result = self.map.get(result.unwrap());

            if let Some(result) = result {
                if visited.contains(result) {
                    warn!("Type {:?} has cyclic dependency", ty);
                    return Some(result);
                }
                visited.insert(result);
            }
        }

        trace!("\t-> {:?}", result);
        result
    }

    pub fn iter(&self) -> impl Iterator<Item = (&Key<'tcx>, &Value<'tcx>)> {
        self.map.iter()
    }
}
