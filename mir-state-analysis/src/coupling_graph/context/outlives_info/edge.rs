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
pub enum EdgeOrigin {
    Rustc,
    RustcUniversal,
    Static,
    Opaque,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct EdgeInfo<'tcx> {
    /// The region which outlives (usually means blocked)
    sup: RegionVid,
    /// The region which is outlived (usually means blocking)
    sub: RegionVid,
    pub creation: Option<Location>,
    pub reason: Option<ConstraintCategory<'tcx>>,
    pub origin: EdgeOrigin,
}

impl<'tcx> EdgeInfo<'tcx> {
    pub fn no_reason(sup: RegionVid, sub: RegionVid, creation: Option<Location>, origin: EdgeOrigin) -> Self {
        if !matches!(origin, EdgeOrigin::Opaque) {
            assert_ne!(sup, sub);
        }
        Self {
            sup,
            sub,
            creation,
            reason: None,
            origin,
        }
    }
    pub fn sup(self) -> RegionVid {
        self.sup
    }
    pub fn sub(self) -> RegionVid {
        self.sub
    }
    pub fn is_opaque(self) -> bool {
        matches!(self.origin, EdgeOrigin::Opaque)
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
                // assert_eq!(sup_info.get_place().unwrap(), sub_info.get_borrow_or_projection_local().unwrap());
                EdgeKind::ContainedIn
            }
            _ => EdgeKind::Unknown(self.creation, self.reason),
        }
    }
    pub fn many_kind(edge: &Vec<Self>, cgx: &CgContext<'_, 'tcx>) -> Vec<EdgeKind<'tcx>> {
        edge.iter().map(|e| e.kind(cgx)).collect()
    }

    pub fn widen(edge: &Vec<Self>, top: impl Fn(RegionVid, RegionVid) -> Self, needs_widening: impl Fn(Location) -> bool) -> Vec<Self> {
        let mut new_edge = Vec::new();
        let widen_edge: &mut Option<(RegionVid, RegionVid)> = &mut None;
        for &e in edge {
            if e.creation.map(|loc| needs_widening(loc)).unwrap_or_default() {
                match widen_edge {
                    Some((_, sup)) => *sup = e.sup,
                    None => *widen_edge = Some((e.sub, e.sup)),
                }
            } else {
                if let Some((sub, sup)) = widen_edge.take() {
                    new_edge.push(top(sup, sub));
                }
                new_edge.push(e);
            }
        }
        if let Some((sub, sup)) = widen_edge.take() {
            new_edge.push(top(sup, sub));
        }
        new_edge
    }
    pub fn generalized_by(target: &Vec<Self>, by: &Vec<Self>) -> bool {
        let mut looking_for = 0;
        for elem in target.iter().copied() {
            if looking_for == by.len() {
                return false;
            } else if by[looking_for].is_opaque() {
                if looking_for == by.len() - 1 {
                    return true;
                } else if by[looking_for + 1] == elem {
                    looking_for += 2;
                }
            } else if by[looking_for] == elem {
                looking_for += 1;
            } else {
                return false;
            }
        }
        looking_for == by.len()
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
        match self.origin {
            EdgeOrigin::Rustc => write!(f, "{creation} ({reason})"),
            EdgeOrigin::RustcUniversal => {
                assert!(self.reason.is_none() && self.creation.is_none());
                write!(f, "universal")
            }
            EdgeOrigin::Static => {
                assert!(self.reason.is_none() && self.creation.is_none());
                write!(f, "promoted")
            }
            EdgeOrigin::Opaque => {
                assert!(self.reason.is_none() && self.creation.is_some());
                write!(f, "{creation} (loop)")
            }
        }
    }
}

impl<'tcx> From<OutlivesConstraint<'tcx>> for EdgeInfo<'tcx> {
    fn from(c: OutlivesConstraint<'tcx>) -> Self {
        Self {
            sup: c.sup,
            sub: c.sub,
            creation: c.locations.from_location(),
            reason: Some(c.category),
            origin: EdgeOrigin::Rustc,
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
