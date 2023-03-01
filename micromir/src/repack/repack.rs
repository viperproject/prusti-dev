// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::cmp::Ordering;

use prusti_rustc_interface::middle::mir::Place;

use crate::{
    repack::place::PlaceRepacker, FreeState, FreeStateUpdate, LocalUpdate, PermissionKind,
    PermissionLocal, PermissionProjections,
};

#[derive(Clone, Debug)]
pub struct PlaceCapabilitySummary<'tcx> {
    state_before: FreeState<'tcx>,
    repacks: Vec<RepackOp<'tcx>>,
}

impl<'tcx> PlaceCapabilitySummary<'tcx> {
    pub(crate) fn empty(state_before: FreeState<'tcx>) -> Self {
        Self {
            state_before,
            repacks: Vec::new(),
        }
    }
    pub fn state(&self) -> &FreeState<'tcx> {
        &self.state_before
    }
    pub fn state_mut(&mut self) -> &mut FreeState<'tcx> {
        &mut self.state_before
    }
    pub fn repacks(&self) -> &Vec<RepackOp<'tcx>> {
        &self.repacks
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
        if cfg!(debug_assertions) {
            self.consistency_check();
        }
        let mut repacks = Vec::new();
        let pre = update
            .iter_enumerated()
            .map(|(l, update)| PermissionLocal::bridge(&self[l], update, &mut repacks, rp))
            .collect();
        (
            PlaceCapabilitySummary {
                state_before: self,
                repacks,
            },
            pre,
        )
    }

    #[tracing::instrument(level = "debug", skip(rp))]
    pub(crate) fn join(&self, to: &mut Self, is_cleanup: bool, rp: PlaceRepacker<'_, 'tcx>) {
        if cfg!(debug_assertions) {
            self.consistency_check();
        }
        for (l, to) in to.iter_enumerated_mut() {
            PermissionLocal::join(&self[l], to, is_cleanup, rp);
        }
    }
}

impl<'tcx> PermissionLocal<'tcx> {
    #[tracing::instrument(level = "debug", skip(rp), ret)]
    fn bridge(
        &self,
        update: &LocalUpdate<'tcx>,
        repacks: &mut Vec<RepackOp<'tcx>>,
        rp: PlaceRepacker<'_, 'tcx>,
    ) -> PermissionLocal<'tcx> {
        match (self, update.get_pre()) {
            (_, None) | (PermissionLocal::Unallocated, Some(PermissionLocal::Unallocated)) => {
                self.clone()
            }
            (PermissionLocal::Allocated(from_places), Some(PermissionLocal::Allocated(places))) => {
                let mut from_places = from_places.clone();
                for (&to_place, &to_kind) in &**places {
                    repacks.extend(from_places.repack(to_place, rp));
                    let from_kind = *from_places.get(&to_place).unwrap();
                    assert!(
                        from_kind >= to_kind,
                        "!({from_kind:?} >= {to_kind:?})"
                    );
                    if from_kind == PermissionKind::Exclusive && to_kind == PermissionKind::Uninit
                    {
                        from_places.insert(to_place, to_kind);
                        repacks.push(RepackOp::Drop(to_place, from_kind));
                    }
                }
                PermissionLocal::Allocated(from_places)
            }
            a => unreachable!("{:?}", a),
        }
    }
    fn join(&self, to: &mut Self, is_cleanup: bool, rp: PlaceRepacker<'_, 'tcx>) {
        match (self, &mut *to) {
            (PermissionLocal::Unallocated, PermissionLocal::Unallocated) => (),
            (PermissionLocal::Allocated(from_places), PermissionLocal::Allocated(places)) => {
                from_places.join(places, rp);
            }
            // Can jump to a `is_cleanup` block with some paths being alloc and other not
            (PermissionLocal::Allocated(..), PermissionLocal::Unallocated) if is_cleanup => (),
            (PermissionLocal::Unallocated, PermissionLocal::Allocated(..)) if is_cleanup => {
                *to = PermissionLocal::Unallocated
            }
            a => unreachable!("{:?}", a),
        };
    }
}

impl<'tcx> PermissionProjections<'tcx> {
    pub(crate) fn repack(
        &mut self,
        to: Place<'tcx>,
        rp: PlaceRepacker<'_, 'tcx>,
    ) -> Box<dyn Iterator<Item = RepackOp<'tcx>> + '_> {
        let mut related = self.find_all_related(to);
        let (cmp, p, k) = related.next().unwrap();
        match cmp {
            Ordering::Less => {
                std::mem::drop(related);
                box self
                    .unpack(to, rp)
                    .into_iter()
                    .map(move |p| RepackOp::Unpack(p, k))
            }
            Ordering::Equal => box std::iter::empty(),
            Ordering::Greater => {
                let related = related.collect::<Vec<_>>();
                let mut minimum = k;
                for (_, _, other) in &related {
                    match minimum.partial_cmp(other) {
                        None => {
                            unreachable!("Cannot find minimum of ({p:?}, {k:?}) and {related:?}")
                        }
                        Some(Ordering::Greater) => {
                            minimum = *other;
                        }
                        _ => (),
                    }
                }
                let all_related = related
                    .into_iter()
                    .chain(std::iter::once((cmp, p, k)))
                    .filter(|(_, _, k)| *k != minimum);
                // TODO: This will replace `PermissionKind::Exclusive` with `PermissionKind::Shared`
                // the exclusive permission will never be able to be recovered anymore!
                let mut repacks: Vec<_> = all_related
                    .map(|(_, p, _k)| RepackOp::Drop(p, self.insert(p, minimum).unwrap()))
                    .collect();
                if minimum != PermissionKind::Uninit {
                    repacks = Vec::new();
                }

                box repacks.into_iter().chain(
                    self.pack(to, rp)
                        .into_iter()
                        .map(move |p| RepackOp::Unpack(p, k)),
                )
            }
        }
    }
}

#[derive(Clone, Debug)]
pub enum RepackOp<'tcx> {
    Drop(Place<'tcx>, PermissionKind),
    Pack(Place<'tcx>, PermissionKind),
    Unpack(Place<'tcx>, PermissionKind),
}
