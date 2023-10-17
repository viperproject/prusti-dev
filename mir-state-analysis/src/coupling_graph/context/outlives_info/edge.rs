// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::{
    borrow::Cow,
    fmt::{Debug, Display, Formatter, Result},
};

use derive_more::{Deref, DerefMut};
use prusti_interface::environment::borrowck::facts::{BorrowckFacts, BorrowckFacts2};
use prusti_rustc_interface::{
    borrowck::{
        borrow_set::BorrowData,
        consumers::{BorrowIndex, OutlivesConstraint},
    },
    data_structures::fx::{FxHashMap, FxHashSet, FxIndexMap, FxIndexSet},
    dataflow::fmt::DebugWithContext,
    index::{bit_set::BitSet, IndexVec},
    middle::{
        mir::{BasicBlock, ConstraintCategory, Local, Location, Operand, RETURN_PLACE, TerminatorKind, StatementKind, Rvalue},
        ty::{RegionVid, TyKind},
    },
};

use crate::coupling_graph::CgContext;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct EdgeInfo<'tcx> {
    /// The region which outlives (usually means blocked)
    sup: RegionVid,
    /// The region which is outlived (usually means blocking)
    sub: RegionVid,
    pub creation: Option<Location>,
    pub reason: Option<ConstraintCategory<'tcx>>,
}

impl<'tcx> EdgeInfo<'tcx> {
    pub fn no_reason(sup: RegionVid, sub: RegionVid, creation: Option<Location>) -> Self {
        assert_ne!(sup, sub);
        Self {
            sup,
            sub,
            creation,
            reason: None,
        }
    }
    pub fn sup(self) -> RegionVid {
        self.sup
    }
    pub fn sub(self) -> RegionVid {
        self.sub
    }
    pub fn kind(self, cgx: &CgContext<'_, 'tcx>) -> EdgeKind<'tcx> {
        let (sup_info, sub_info) = (cgx.region_info.map.get(self.sup), cgx.region_info.map.get(self.sub));
        let stmt = self.creation.map(|location| cgx.rp.body().stmt_at(location));
        let term = stmt.and_then(|stmt| stmt.right()).map(|t| &t.kind);
        let stmt = stmt.and_then(|stmt| stmt.left()).map(|s| &s.kind);
        match (self.reason, stmt, term) {
            (Some(ConstraintCategory::BoringNoLocation), _, Some(TerminatorKind::Call { .. })) if sup_info.from_function_depth() > 0 && sub_info.from_function_depth() > 0 =>
                EdgeKind::FnCallImplied,
            (Some(ConstraintCategory::Predicate(_)), _, _) => {
                assert!(matches!(term.unwrap(), TerminatorKind::Call { .. }));
                assert!(sup_info.from_function_depth() > 0 && sub_info.from_function_depth() > 0);
                EdgeKind::FnCallPredicate
            }
            (Some(ConstraintCategory::CallArgument(_)), _, _) => {
                assert!(matches!(term.unwrap(), TerminatorKind::Call { .. }));
                // Can get a `Self::Static` outlives requirement from a function call
                let static_eq = sup_info.is_static() ^ sub_info.is_static();
                let placeholders = sup_info.is_placeholder() && sub_info.is_placeholder();
                let sup_depth = sub_info.from_function_depth();
                let sub_depth = sup_info.from_function_depth();
                assert!(static_eq || placeholders || (sup_depth + 1 == sub_depth) || (sup_depth == sub_depth + 1),
                    "{sup_info:?} ({})\nand\n{sub_info:?} ({})\n({self:?})", sup_info.from_function_depth(), sub_info.from_function_depth());
                EdgeKind::FnCallArgument
            }
            (Some(ConstraintCategory::Assignment), _, Some(TerminatorKind::Call { .. })) => {
                let static_eq = sup_info.is_static() ^ sub_info.is_static();
                // let placeholders = sup_info.is_placeholder() && sub_info.is_placeholder();
                let sup_depth = sub_info.from_function_depth();
                let sub_depth = sup_info.from_function_depth();
                assert!(static_eq || (sup_depth + 1 == sub_depth) || (sup_depth == sub_depth + 1));
                EdgeKind::FnCallReturn
            }
            _ if sub_info.is_borrow() || sub_info.is_projection_annotation() => {
                if sub_info.is_borrow() {
                    assert!(matches!(stmt.unwrap(), StatementKind::Assign(box (_, Rvalue::Ref(..)))));
                }
                // assert_eq!(sup_info.get_place().unwrap(), sub_info.get_borrow_or_projection_local().unwrap());
                EdgeKind::ContainedIn
            }
            _ => EdgeKind::Unknown(self.creation, self.reason),
        }
    }
    pub fn many_kind(edge: &Vec<Self>, cgx: &CgContext<'_, 'tcx>) -> Vec<EdgeKind<'tcx>> {
        edge.iter().map(|e| e.kind(cgx)).collect()
    }

    /// Is the old edge contained in the new edge?
    pub fn is_new_edge(new: &Vec<Self>, old: &Vec<Self>) -> bool {
        assert_ne!(old.len(), 0);
        if new.len() < old.len() {
            return true;
        }
        // TODO: optimize?
        let mut looking_for = 0;
        for (idx, elem) in new.iter().enumerate() {
            if &old[looking_for] == elem {
                looking_for += 1;
            }
            let left_to_find = old.len() - looking_for;
            if left_to_find == 0 {
                return false;
            }
            if new.len() - idx - 1 < left_to_find {
                return true;
            }
        }
        unreachable!()
    }
}

impl Display for EdgeInfo<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let reason = if let Some(reason) = self.reason {
            match reason {
                ConstraintCategory::Return(_) => "return",
                ConstraintCategory::Yield => "yield",
                ConstraintCategory::UseAsConst => "const",
                ConstraintCategory::UseAsStatic => "static",
                ConstraintCategory::TypeAnnotation => "type",
                ConstraintCategory::Cast => "cast",
                ConstraintCategory::ClosureBounds => "closure",
                ConstraintCategory::CallArgument(_) => "arg",
                ConstraintCategory::CopyBound => "copy",
                ConstraintCategory::SizedBound => "sized",
                ConstraintCategory::Assignment => "assign",
                ConstraintCategory::Usage => "use",
                ConstraintCategory::OpaqueType => "opaque",
                ConstraintCategory::ClosureUpvar(_) => "upvar",
                ConstraintCategory::Predicate(_) => "pred",
                ConstraintCategory::Boring => "?",
                ConstraintCategory::BoringNoLocation => "? no_loc",
                ConstraintCategory::Internal => "internal",
            }
        } else {
            "other"
        };
        let creation = self
            .creation
            .map(|c| format!("{c:?}"))
            .unwrap_or_else(|| "sig".to_string());
        write!(f, "{creation} ({reason})")
    }
}

impl<'tcx> From<OutlivesConstraint<'tcx>> for EdgeInfo<'tcx> {
    fn from(c: OutlivesConstraint<'tcx>) -> Self {
        Self {
            sup: c.sup,
            sub: c.sub,
            creation: c.locations.from_location(),
            reason: Some(c.category),
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum EdgeKind<'tcx> {
    /// An edge from `'a` to `'b` created when
    /// re-borrowing `_ = &'a mut (*x).0` with `x: &'b mut (_, _)`.
    ContainedIn,
    /// An edge from `'a` to `'b` created when
    /// calling `fn foo<'a, 'b>(x: &'a mut &'b mut _)`.
    FnCallImplied,
    /// An edge from `'a` to `'b` created when
    /// calling `fn foo<'a, 'b: 'a>(_: &'b mut _) -> &'a mut _`.
    FnCallPredicate,
    /// An edge from `'a` to `'b` created when
    /// calling `fn foo<'a>(_: &'a mut _)` with `x: &'b mut _`.
    FnCallArgument,
    /// An edge from `'a` to `'b` created when
    /// calling `fn foo<'b>(_) -> &'b mut _` to `r: &'a mut = foo()`.
    FnCallReturn,
    Unknown(Option<Location>, Option<ConstraintCategory<'tcx>>),
}

impl<'tcx> EdgeKind<'tcx> {
    pub fn is_blocking(self) -> bool {
        !matches!(self, EdgeKind::ContainedIn | EdgeKind::FnCallImplied)
    }

    pub fn many_blocking(kinds: Vec<Self>) -> bool {
        kinds.iter().any(|kind| kind.is_blocking())
    }
}
