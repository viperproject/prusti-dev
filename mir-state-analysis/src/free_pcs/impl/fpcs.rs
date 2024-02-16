// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::fmt::{Debug, Formatter, Result};

use derive_more::{Deref, DerefMut};
use prusti_rustc_interface::{
    index::Idx,
    dataflow::fmt::DebugWithContext, index::IndexVec, middle::mir::{Local, RETURN_PLACE},
};

use crate::{
    free_pcs::{
        CapabilityLocal, CapabilityProjections, RepackOp,
    },
    utils::PlaceRepacker,
};

use super::{CapabilityKind, RepackingBridgeSemiLattice, engine::FpcsEngine};

pub struct FreePlaceCapabilitySummary<'a, 'tcx> {
    pub(crate) repacker: PlaceRepacker<'a, 'tcx>,
    pub before_start: CapabilitySummary<'tcx>,
    pub before_after: CapabilitySummary<'tcx>,
    pub start: CapabilitySummary<'tcx>,
    pub after: CapabilitySummary<'tcx>,
}
impl<'a, 'tcx> FreePlaceCapabilitySummary<'a, 'tcx> {
    pub(crate) fn new(repacker: PlaceRepacker<'a, 'tcx>) -> Self {
        let after = CapabilitySummary::default(repacker.local_count());
        Self {
            repacker,
            before_start: CapabilitySummary::empty(),
            before_after: CapabilitySummary::empty(),
            start: CapabilitySummary::empty(),
            after,
        }
    }
    pub fn initialize_as_start_block(&mut self) {
        let always_live = self.repacker.always_live_locals();
        let return_local = RETURN_PLACE;
        let last_arg = Local::new(self.repacker.body().arg_count);
        for (local, cap) in self.after.iter_enumerated_mut() {
            let new_cap = if local == return_local {
                // Return local is allocated but uninitialized
                CapabilityLocal::new(local, CapabilityKind::Write)
            } else if local <= last_arg {
                // Arguments are allocated and initialized
                CapabilityLocal::new(local, CapabilityKind::Exclusive)
            } else if always_live.contains(local) {
                // Always live locals start allocated but uninitialized
                CapabilityLocal::new(local, CapabilityKind::Write)
            } else {
                // Other locals are unallocated
                CapabilityLocal::Unallocated
            };
            *cap = new_cap;
        }
    }

    pub fn repack_ops(&self, previous: &CapabilitySummary<'tcx>) -> (Vec<RepackOp<'tcx>>, Vec<RepackOp<'tcx>>) {
        let from_prev = previous.bridge(&self.before_start, self.repacker);
        let middle = self.before_after.bridge(&self.start, self.repacker);
        (from_prev, middle)
    }
}

impl Clone for FreePlaceCapabilitySummary<'_, '_> {
    fn clone(&self) -> Self {
        Self {
            repacker: self.repacker,
            before_start: self.before_start.clone(),
            before_after: self.before_after.clone(),
            start: self.start.clone(),
            after: self.after.clone(),
        }
    }
}
impl PartialEq for FreePlaceCapabilitySummary<'_, '_> {
    fn eq(&self, other: &Self) -> bool {
        self.after == other.after
    }
}
impl Eq for FreePlaceCapabilitySummary<'_, '_> {}

impl Debug for FreePlaceCapabilitySummary<'_, '_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        self.after.fmt(f)
    }
}
impl<'a, 'tcx> DebugWithContext<FpcsEngine<'a, 'tcx>> for FreePlaceCapabilitySummary<'a, 'tcx> {
    fn fmt_diff_with(
        &self,
        old: &Self,
        _ctxt: &FpcsEngine<'a, 'tcx>,
        f: &mut Formatter<'_>,
    ) -> Result {
        let (from_prev, middle) = self.repack_ops(&old.after);
        if !from_prev.is_empty() {
            writeln!(f, "{from_prev:?}")?;
        }
        CapabilitySummaryCompare(&self.before_start, &old.after, "").fmt(f)?;
        CapabilitySummaryCompare(&self.before_after, &self.before_start, "ARGUMENTS:\n").fmt(f)?;
        if !middle.is_empty() {
            writeln!(f, "{middle:?}")?;
        }
        CapabilitySummaryCompare(&self.start, &self.before_after, "").fmt(f)?;
        CapabilitySummaryCompare(&self.after, &self.start, "STATEMENT:\n").fmt(f)?;
        Ok(())
    }
}

#[derive(Clone, PartialEq, Eq, Deref, DerefMut)]
/// The free pcs of all locals
pub struct CapabilitySummary<'tcx>(IndexVec<Local, CapabilityLocal<'tcx>>);

impl<'tcx> Debug for CapabilitySummary<'tcx> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let v: Vec<_> = self.0.iter().filter(|c| !c.is_unallocated()).collect();
        v.fmt(f)
    }
}

impl<'tcx> CapabilitySummary<'tcx> {
    pub fn default(local_count: usize) -> Self {
        Self(IndexVec::from_elem_n(CapabilityLocal::default(), local_count))
    }
    pub fn empty() -> Self {
        Self(IndexVec::new())
    }
}

struct CapabilitySummaryCompare<'a, 'tcx>(&'a CapabilitySummary<'tcx>, &'a CapabilitySummary<'tcx>, &'a str);
impl Debug for CapabilitySummaryCompare<'_, '_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        if self.0 == self.1 {
            return Ok(());
        }
        write!(f, "{}", self.2)?;
        for (new, old) in self.0.iter().zip(self.1.iter()) {
            let changed = match (new, old) {
                (CapabilityLocal::Unallocated, CapabilityLocal::Unallocated) => false,
                (CapabilityLocal::Unallocated, CapabilityLocal::Allocated(a)) => {
                    write!(f, "\u{001f}-{:?}", a.get_local())?;
                    true
                }
                (CapabilityLocal::Allocated(a), CapabilityLocal::Unallocated) => {
                    write!(f, "\u{001f}+{:?}", a.get_local())?;
                    true
                }
                (CapabilityLocal::Allocated(new), CapabilityLocal::Allocated(old)) => {
                    if new != old {
                        let mut new_set = CapabilityProjections::empty();
                        let mut old_set = CapabilityProjections::empty();
                        for (&p, &nk) in new.iter() {
                            match old.get(&p) {
                                Some(&ok) if nk == ok => (),
                                _ => {
                                    new_set.insert(p, nk);
                                }
                            }
                        }
                        for (&p, &ok) in old.iter() {
                            match new.get(&p) {
                                Some(&nk) if nk == ok => (),
                                _ => {
                                    old_set.insert(p, ok);
                                }
                            }
                        }
                        if !old_set.is_empty() {
                            write!(f, "\u{001f}-{old_set:?}")?
                        }
                        if !new_set.is_empty() {
                            write!(f, "\u{001f}+{new_set:?}")?
                        }
                        true
                    } else {
                        false
                    }
                }
            };
            if changed {
                write!(f, "</font><font color=\"black\">")?;
                if f.alternate() {
                    writeln!(f)?;
                } else {
                    write!(f, "\t")?;
                }
            }
        }
        Ok(())
    }
}
