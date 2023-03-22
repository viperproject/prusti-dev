// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use derive_more::{Deref, DerefMut};
use prusti_rustc_interface::{
    data_structures::{fx::{FxHashSet, FxHashMap}, graph::WithStartNode},
    dataflow::{storage, Analysis, ResultsCursor, AnalysisDomain, JoinSemiLattice, CallReturnPlaces,
        impls::{MaybeStorageLive, MaybeBorrowedLocals, MaybeRequiresStorage, MaybeLiveLocals}},
    index::vec::{Idx, IndexVec},
    middle::{
        mir::{Statement, Location, Terminator, Body, BasicBlock, HasLocalDecls, Local, RETURN_PLACE},
        ty::TyCtxt,
    },
    hir::Mutability,
};

use crate::{
    CapabilityKind, CapabilityLocal, utils::PlaceRepacker, RepackOp, CapabilityProjections, PlaceOrdering, Summary, Place, Fpcs, RelatedSet
};

impl<'tcx> Fpcs<'_, 'tcx> {
    pub(crate) fn requires_unalloc(&mut self, local: Local) {
        assert!(self.summary[local].is_unallocated());
    }
    pub(crate) fn requires_unalloc_or_uninit(&mut self, local: Local) {
        if !self.summary[local].is_unallocated() {
            self.requires_write(local);
        }
    }
    pub(crate) fn requires_read(&mut self, place: impl Into<Place<'tcx>>) {
        self.requires(place, CapabilityKind::Read)
    }
    /// May obtain write _or_ exclusive, if one should only have write afterwards,
    /// make sure to also call `ensures_write`!
    pub(crate) fn requires_write(&mut self, place: impl Into<Place<'tcx>>) {
        self.requires(place, CapabilityKind::Write)
    }
    pub(crate) fn requires_exclusive(&mut self, place: impl Into<Place<'tcx>>) {
        self.requires(place, CapabilityKind::Exclusive(None))
    }
    fn requires(&mut self, place: impl Into<Place<'tcx>>, cap: CapabilityKind) {
        let place = place.into();
        let cp: &mut CapabilityProjections = &mut self.summary[place.local].get_allocated_mut();
        cp.repack(place, self.repacker);
        let kind = (*cp)[&place];
        assert!(kind >= cap);
    }
    pub(crate) fn requires_exclusive_deep(&mut self, place: impl Into<Place<'tcx>>) {
        self.requires_deep(place, CapabilityKind::Exclusive(None))
    }
    fn requires_deep(&mut self, place: impl Into<Place<'tcx>>, cap: CapabilityKind) {
        let place = place.into();
        let cp: &mut CapabilityProjections = &mut self.summary[place.local].get_allocated_mut();
        cp.repack(place, self.repacker);
        let kind = (*cp)[&place];
        assert!(kind >= cap);
    }

    pub(crate) fn ensures_unalloc(&mut self, local: Local) {
        self.summary[local].clear();
    }
    pub(crate) fn ensures_allocates(&mut self, local: Local) {
        assert_eq!(self.summary[local], CapabilityLocal::Unallocated);
        self.summary[local] = CapabilityLocal::Allocated(CapabilityProjections::new_uninit(local));
    }
    fn ensures_alloc(&mut self, place: impl Into<Place<'tcx>>, cap: CapabilityKind) {
        let place = place.into();
        let cp: &mut CapabilityProjections = &mut self.summary[place.local].get_allocated_mut();
        let old = cp.insert(place, cap);
        assert!(old.is_some());
    }
    pub(crate) fn ensures_exclusive(&mut self, place: impl Into<Place<'tcx>>) {
        self.ensures_alloc(place, CapabilityKind::Exclusive(None))
    }
    pub(crate) fn ensures_write(&mut self, place: impl Into<Place<'tcx>>) {
        self.ensures_alloc(place, CapabilityKind::Write)
    }
    pub(crate) fn ensures_blocked_read(&mut self, place: impl Into<Place<'tcx>>) {
        let place = place.into();
        let cp: &mut CapabilityProjections = &mut self.summary[place.local].get_allocated_mut();
        if let Some(CapabilityKind::Exclusive(m)) = cp.get_mut(&place) {
            assert!(m.is_none());
            *m = Some(Mutability::Not);
        }
    }
    pub(crate) fn ensures_blocked_exclusive(&mut self, place: impl Into<Place<'tcx>>) {
        let place = place.into();
        let cp: &mut CapabilityProjections = &mut self.summary[place.local].get_allocated_mut();
        if let Some(CapabilityKind::Exclusive(m)) = cp.get_mut(&place) {
            assert!(m.is_none());
            *m = Some(Mutability::Mut);
        }
    }
}

impl<'tcx> CapabilityProjections<'tcx> {
    fn repack(&mut self, to: Place<'tcx>, repacker: PlaceRepacker<'_, 'tcx>) {
        let related = self.find_all_related(to, None);
        match related.relation {
            PlaceOrdering::Prefix => {
                self.unpack(related.from[0].0, related.to, repacker);
            }
            PlaceOrdering::Equal => {}
            PlaceOrdering::Suffix => {
                self.pack(related.get_from(), related.to, related.minimum, repacker);
            }
            PlaceOrdering::Both => {
                let cp = repacker.common_prefix(related.from[0].0, to);
                // Pack
                self.weaken(&related);
                self.pack(related.get_from(), cp, related.minimum, repacker);
                // Unpack
                self.unpack(cp, related.to, repacker);
            }
        }
    }

    pub(crate) fn weaken(
        &mut self,
        related: &RelatedSet<'tcx>,
    ) {
        let more_than_min = related.from.iter().filter(|(_, k)| *k != related.minimum);
        // TODO: This will replace `PermissionKind::Exclusive` with `PermissionKind::Shared`
        // the exclusive permission will never be able to be recovered anymore!
        for &(p, k) in more_than_min {
            let old = self.insert(p, related.minimum);
            assert_eq!(old, Some(k));
        }
    }
}

// pub type UpdateSummary<'tcx> = Summary<UpdateLocal<'tcx>>;
// #[derive(Clone, Debug, PartialEq, Eq, Deref, DerefMut, Default)]
// pub struct UpdateLocal<'tcx>(
//     (
//         Option<LocalRequirement<'tcx>>,
//         Option<CapabilityLocal<'tcx>>,
//     ),
// );

// #[derive(Clone, Debug, PartialEq, Eq, Deref, DerefMut, Default)]
// pub struct LocalRequirement<'tcx> {
//     unalloc_allowed: bool,
//     #[deref]
//     #[deref_mut]
//     place_reqs: FxHashMap<Place<'tcx>, FxHashSet<CapabilityKind>>,
// }

// impl<'tcx> UpdateLocal<'tcx> {
//     fn init_pre(&mut self) -> &mut LocalRequirement<'tcx> {
//         assert!(self.0 .0.is_none());
//         self.0 .0 = Some(LocalRequirement::default());
//         self.0 .0.as_mut().unwrap()
//     }
//     pub(crate) fn requires_unalloc_or_uninit(&mut self, local: Local) {
//         let req = self.init_pre();
//         req.unalloc_allowed = true;
//         self.requires_alloc(local.into(), &[CapabilityKind::Write]);
//     }
//     pub(crate) fn requires_alloc(&mut self, place: Place<'tcx>, perms: &[CapabilityKind]) {
//         let req = if self.0 .0.is_none() {
//             self.init_pre()
//         } else {
//             self.0 .0.as_mut().unwrap()
//         };
//         assert!(
//             req.keys().all(|other| !place.related_to(*other)),
//             "{req:?} {place:?} {perms:?}"
//         );
//         req.insert(place, perms.iter().copied().collect());
//     }
//     pub(crate) fn requires_unalloc(&mut self) {
//         let req = self.init_pre();
//         req.unalloc_allowed = true;
//     }
//     pub(crate) fn requires_alloc_one(&mut self, place: Place<'tcx>, perm: CapabilityKind) {
//         self.requires_alloc(place, &[perm]);
//     }

//     pub(crate) fn ensures_unalloc(&mut self) {
//         assert!(self.0 .1.is_none());
//         self.0 .1 = Some(CapabilityLocal::Unallocated);
//     }
//     pub(crate) fn ensures_alloc(&mut self, place: Place<'tcx>, perm: CapabilityKind) {
//         if let Some(pre) = &mut self.0 .1 {
//             let pre = pre.get_allocated_mut();
//             assert!(pre.keys().all(|other| !place.related_to(*other)));
//             pre.insert(place, perm);
//         } else {
//             self.0 .1 = Some(CapabilityLocal::Allocated(
//                 CapabilityProjections::new_update(place, perm),
//             ));
//         }
//     }

//     /// Used for the edge case of assigning to the same place you copy from, do not use otherwise!
//     pub(crate) fn get_pre_for(&self, place: Place<'tcx>) -> Option<&FxHashSet<CapabilityKind>> {
//         let pre = self.0 .0.as_ref()?;
//         pre.get(&place)
//     }

//     pub(crate) fn get_pre(&self, state: &CapabilityLocal<'tcx>) -> Option<CapabilityLocal<'tcx>> {
//         let pre = self.0 .0.as_ref()?;
//         match state {
//             CapabilityLocal::Unallocated => {
//                 assert!(pre.unalloc_allowed);
//                 Some(CapabilityLocal::Unallocated)
//             }
//             CapabilityLocal::Allocated(state) => {
//                 let mut achievable = CapabilityProjections::empty();
//                 for (place, allowed_perms) in pre.iter() {
//                     let related_set = state.find_all_related(*place, None);
//                     let mut perm = None;
//                     for &ap in allowed_perms {
//                         if related_set.minimum >= ap {
//                             perm = Some(ap);
//                         }
//                         if related_set.minimum == ap {
//                             break;
//                         }
//                     }
//                     assert!(
//                         perm.is_some(),
//                         "{place:?}, {allowed_perms:?}, {state:?}, {:?}, {:?}",
//                         related_set.minimum,
//                         related_set.from
//                     );
//                     achievable.insert(*place, perm.unwrap());
//                 }
//                 Some(CapabilityLocal::Allocated(achievable))
//             }
//         }
//     }
// }
