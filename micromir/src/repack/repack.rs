// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::fmt::{Debug, Formatter, Result};

use derive_more::{Deref, DerefMut};
use prusti_rustc_interface::{
    data_structures::fx::FxHashMap,
    middle::mir::{BasicBlock, Local},
};

use crate::{
    repack::place::PlaceRepacker, FreeState, FreeStateUpdate, PermissionKind, PermissionLocal,
    PermissionProjections, Place, PlaceOrdering, RelatedSet,
};

#[derive(Clone, Deref, DerefMut)]
pub struct Repacks<'tcx>(Vec<RepackOp<'tcx>>);
impl Debug for Repacks<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        self.0.fmt(f)
    }
}
impl<'tcx> Repacks<'tcx> {
    pub fn new() -> Self {
        Self(Vec::new())
    }
}

#[derive(Clone)]
pub struct PlaceCapabilitySummary<'tcx> {
    state_before: FreeState<'tcx>,
    repacks: Repacks<'tcx>,
}

impl Debug for PlaceCapabilitySummary<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        if self.repacks.len() == 0 {
            write!(f, "{:?}", &self.state_before)
        } else {
            f.debug_struct("PCS")
                .field("state", &self.state_before)
                .field("repacks", &self.repacks)
                .finish()
        }
    }
}

impl<'tcx> PlaceCapabilitySummary<'tcx> {
    pub fn state(&self) -> &FreeState<'tcx> {
        &self.state_before
    }
    pub fn state_mut(&mut self) -> &mut FreeState<'tcx> {
        &mut self.state_before
    }
    pub fn repacks(&self) -> &Repacks<'tcx> {
        &self.repacks
    }
}

#[derive(Clone)]
pub struct TerminatorPlaceCapabilitySummary<'tcx> {
    state_before: FreeState<'tcx>,
    repacks: FxHashMap<BasicBlock, Repacks<'tcx>>,
}

impl Debug for TerminatorPlaceCapabilitySummary<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        if self.repacks.len() == 0 {
            write!(f, "{:?}", &self.state_before)
        } else {
            f.debug_struct("PCS")
                .field("state", &self.state_before)
                .field("repacks", &self.repacks)
                .finish()
        }
    }
}

impl<'tcx> TerminatorPlaceCapabilitySummary<'tcx> {
    pub(crate) fn empty(state_before: FreeState<'tcx>) -> Self {
        Self {
            state_before,
            repacks: FxHashMap::default(),
        }
    }
    pub fn state(&self) -> &FreeState<'tcx> {
        &self.state_before
    }
    pub fn state_mut(&mut self) -> &mut FreeState<'tcx> {
        &mut self.state_before
    }
    pub fn repacks(&self) -> &FxHashMap<BasicBlock, Repacks<'tcx>> {
        &self.repacks
    }

    #[tracing::instrument(name = "PCS::join", level = "debug", skip(rp))]
    pub(crate) fn join(
        &mut self,
        to: &FreeState<'tcx>,
        bb: BasicBlock,
        is_cleanup: bool,
        rp: PlaceRepacker<'_, 'tcx>,
    ) {
        let repacks = self.repacks.entry(bb).or_insert_with(Repacks::new);
        repacks.clear();
        for (l, to) in to.iter_enumerated() {
            let new =
                PermissionLocal::bridge(&self.state_before[l], Some(to), repacks, is_cleanup, rp);
            debug_assert_eq!(&new, to);
        }
    }
}

impl<'tcx> FreeState<'tcx> {
    /// The `from` state should never contain any `DontCare` permissions
    #[tracing::instrument(level = "debug", skip(rp), ret)]
    pub(crate) fn bridge(
        self,
        update: &FreeStateUpdate<'tcx>,
        rp: PlaceRepacker<'_, 'tcx>,
    ) -> (PlaceCapabilitySummary<'tcx>, FreeState<'tcx>) {
        let mut repacks = Repacks::new();
        let pre = update
            .iter_enumerated()
            .map(|(l, update)| {
                PermissionLocal::bridge(
                    &self[l],
                    update.get_pre(&self[l]).as_ref(),
                    &mut repacks,
                    false,
                    rp,
                )
            })
            .collect();
        (
            PlaceCapabilitySummary {
                state_before: self,
                repacks,
            },
            pre,
        )
    }

    #[tracing::instrument(name = "FreeState::join", level = "info", skip(rp))]
    pub(crate) fn join(&self, to: &mut Self, is_cleanup: bool, rp: PlaceRepacker<'_, 'tcx>) {
        for (l, to) in to.iter_enumerated_mut() {
            PermissionLocal::join(&self[l], to, is_cleanup, rp);
        }
    }
}

impl<'tcx> PermissionLocal<'tcx> {
    #[tracing::instrument(level = "trace", skip(rp), ret)]
    fn bridge(
        &self,
        to: Option<&PermissionLocal<'tcx>>,
        repacks: &mut Repacks<'tcx>,
        is_cleanup: bool,
        rp: PlaceRepacker<'_, 'tcx>,
    ) -> PermissionLocal<'tcx> {
        use PermissionLocal::*;
        match (self, to) {
            (_, None) | (Unallocated, Some(Unallocated)) => self.clone(),
            (Allocated(from_places), Some(Allocated(places))) => {
                let mut from_places = from_places.clone();
                for (&to_place, &to_kind) in &**places {
                    from_places.repack_op(to_place, repacks, rp);
                    let from_kind = *from_places.get(&to_place).unwrap();
                    assert!(from_kind >= to_kind, "!({from_kind:?} >= {to_kind:?})");
                    if from_kind > to_kind {
                        from_places.insert(to_place, to_kind);
                        repacks.push(RepackOp::Weaken(to_place, from_kind, to_kind));
                    }
                }
                Allocated(from_places)
            }
            (Allocated(a), Some(Unallocated)) => {
                let local = a.iter().next().unwrap().0.local;
                let root_place = local.into();
                let mut a = a.clone();
                a.repack_op(root_place, repacks, rp);
                if a[&root_place] != PermissionKind::Uninit {
                    assert_eq!(a[&root_place], PermissionKind::Exclusive);
                    repacks.push(RepackOp::Weaken(
                        root_place,
                        a[&root_place],
                        PermissionKind::Uninit,
                    ));
                }
                if is_cleanup {
                    repacks.push(RepackOp::DeallocForCleanup(local));
                } else {
                    println!("TODO: figure out why this happens and if it's ok");
                    repacks.push(RepackOp::DeallocUnknown(local));
                }
                Unallocated
            }
            a @ (Unallocated, Some(Allocated(..))) => unreachable!("{:?}", a),
        }
    }
    #[tracing::instrument(level = "info", skip(rp))]
    fn join(&self, to: &mut Self, _is_cleanup: bool, rp: PlaceRepacker<'_, 'tcx>) {
        match (self, &mut *to) {
            (PermissionLocal::Unallocated, PermissionLocal::Unallocated) => (),
            (PermissionLocal::Allocated(from_places), PermissionLocal::Allocated(places)) => {
                from_places.join(places, rp);
            }
            // Can jump to a `is_cleanup` block with some paths being alloc and other not
            (PermissionLocal::Allocated(..), PermissionLocal::Unallocated) => (),
            (PermissionLocal::Unallocated, PermissionLocal::Allocated(..)) => {
                *to = PermissionLocal::Unallocated
            }
        };
    }
}

impl<'tcx> PermissionProjections<'tcx> {
    #[tracing::instrument(level = "debug", skip(rp))]
    pub(crate) fn repack_op(
        &mut self,
        to: Place<'tcx>,
        repacks: &mut Vec<RepackOp<'tcx>>,
        rp: PlaceRepacker<'_, 'tcx>,
    ) {
        let mut related = self.find_all_related(to, None);
        match related.relation {
            PlaceOrdering::Prefix => self.unpack_op(related, repacks, rp),
            PlaceOrdering::Equal => {}
            PlaceOrdering::Suffix => self.pack_op(related, repacks, rp),
            PlaceOrdering::Both => {
                let cp = rp.common_prefix(related.from[0].0, to);
                let minimum = related.minimum;
                // Pack
                related.to = cp;
                related.relation = PlaceOrdering::Both;
                self.pack_op(related, repacks, rp);
                // Unpack
                let related = RelatedSet {
                    from: vec![(cp, minimum)],
                    to,
                    minimum,
                    relation: PlaceOrdering::Prefix,
                };
                self.unpack_op(related, repacks, rp);
            }
        }
    }
    pub(crate) fn unpack_op(
        &mut self,
        related: RelatedSet<'tcx>,
        repacks: &mut Vec<RepackOp<'tcx>>,
        rp: PlaceRepacker<'_, 'tcx>,
    ) {
        let unpacks = self.unpack(related.from[0].0, related.to, rp);
        repacks.extend(
            unpacks
                .into_iter()
                .map(move |(place, to)| RepackOp::Unpack(place, to, related.minimum)),
        );
    }
    pub(crate) fn pack_op(
        &mut self,
        related: RelatedSet<'tcx>,
        repacks: &mut Vec<RepackOp<'tcx>>,
        rp: PlaceRepacker<'_, 'tcx>,
    ) {
        let more_than_min = related.from.iter().filter(|(_, k)| *k != related.minimum);
        // TODO: This will replace `PermissionKind::Exclusive` with `PermissionKind::Shared`
        // the exclusive permission will never be able to be recovered anymore!
        for &(p, k) in more_than_min {
            let old = self.insert(p, related.minimum);
            assert_eq!(old, Some(k));
            repacks.push(RepackOp::Weaken(p, k, related.minimum));
        }

        let packs = self.pack(related.get_from(), related.to, related.minimum, rp);
        repacks.extend(
            packs
                .into_iter()
                .map(move |(place, to)| RepackOp::Pack(place, to, related.minimum)),
        );
    }
}

#[derive(Clone, Debug)]
pub enum RepackOp<'tcx> {
    Weaken(Place<'tcx>, PermissionKind, PermissionKind),
    // TODO: figure out when and why this happens
    DeallocUnknown(Local),
    DeallocForCleanup(Local),
    // First place is packed up, second is guide place to pack up from
    Pack(Place<'tcx>, Place<'tcx>, PermissionKind),
    // First place is packed up, second is guide place to unpack to
    Unpack(Place<'tcx>, Place<'tcx>, PermissionKind),
}
