// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_interface::environment::borrowck::facts::{BorrowckFacts, BorrowckFacts2};
use prusti_rustc_interface::{
    borrowck::{
        borrow_set::BorrowData,
        consumers::{BorrowIndex, Borrows, OutlivesConstraint},
    },
    data_structures::fx::FxHashMap,
    dataflow::{Analysis, ResultsCursor},
    index::IndexVec,
    infer::infer::{
        region_constraints::RegionVariableInfo, LateBoundRegionConversionTime,
        NllRegionVariableOrigin, RegionVariableOrigin,
    },
    middle::{
        mir::{Body, BorrowKind, Local, Location, Operand, RETURN_PLACE},
        ty::{BoundRegionKind, PlaceholderRegion, RegionVid, Ty, TyCtxt, TyKind},
    },
    span::{Span, Symbol},
};

use crate::{
    coupling_graph::CgContext,
    utils::{Place, PlaceRepacker},
};

#[derive(Debug)]
pub struct RegionInfoMap<'tcx> {
    region_info: IndexVec<RegionVid, RegionKind<'tcx>>,
    universal: usize,
    constant_regions: Vec<RegionVid>,
}

#[derive(Debug, Clone)]
pub enum RegionKind<'tcx> {
    // Universal regions (placeholders)
    Static,
    Param(ParamRegion),
    Function,
    UnknownUniversal,
    // Local regions
    ConstRef(bool),
    Place {
        region: RegionVid,
        local: Local,
        // ty: Ty<'tcx>,
    },
    Borrow(BorrowData<'tcx>),
    EarlyBound(Symbol),
    LateBound {
        // span: Span,
        kind: BoundRegionKind,
        ctime: LateBoundRegionConversionTime,
    },
    Placeholder(Option<PlaceholderRegion>),
    MiscLocal,
    UnknownLocal,
}

impl<'tcx> RegionKind<'tcx> {
    pub fn is_static(&self) -> bool {
        matches!(self, Self::Static)
    }
    pub fn is_param(&self) -> bool {
        matches!(self, Self::Param(..))
    }
    pub fn is_function(&self) -> bool {
        matches!(self, Self::Function)
    }
    pub fn is_unknown_universal(&self) -> bool {
        matches!(self, Self::UnknownUniversal)
    }
    pub fn is_const_ref(&self) -> bool {
        matches!(self, Self::ConstRef(..))
    }
    pub fn is_place(&self) -> bool {
        matches!(self, Self::Place { .. })
    }
    pub fn is_borrow(&self) -> bool {
        matches!(self, Self::Borrow(..))
    }
    pub fn is_early_bound(&self) -> bool {
        matches!(self, Self::EarlyBound(..))
    }
    pub fn is_late_bound(&self) -> bool {
        matches!(self, Self::LateBound { .. })
    }
    pub fn is_placeholder(&self) -> bool {
        matches!(self, Self::Placeholder(..))
    }
    pub fn is_misc_local(&self) -> bool {
        matches!(self, Self::MiscLocal)
    }
    pub fn is_unknown_local(&self) -> bool {
        matches!(self, Self::UnknownLocal)
    }

    pub fn is_unknown(&self) -> bool {
        matches!(self, Self::UnknownUniversal | Self::UnknownLocal)
    }

    pub fn is_universal(&self) -> bool {
        matches!(
            self,
            Self::Static | Self::Param(..) | Self::Function | Self::UnknownUniversal
        )
    }
    pub fn is_local(&self) -> bool {
        !self.is_universal()
    }

    // #[tracing::instrument(name = "RegionKind::get_place", level = "trace", ret)]
    pub fn get_place(&self) -> Option<Local> {
        match self {
            Self::Place { local, .. } => Some(*local),
            _ => None,
        }
    }
    pub fn get_borrow(&self) -> Option<&BorrowData<'tcx>> {
        match self {
            Self::Borrow(data) => Some(data),
            _ => None,
        }
    }

    pub fn to_string(&self, cgx: &CgContext<'_, 'tcx>) -> String {
        match self {
            Self::Static => "'static".to_string(),
            Self::Param(ParamRegion { regions }) => {
                let mut result = "old(".to_string();
                for (idx, r) in regions
                    .iter()
                    .map(|&r| cgx.region_info.map.get(r).to_string(cgx))
                    .enumerate()
                {
                    if idx != 0 {
                        result += " + ";
                    }
                    result += &r;
                }
                result += ")";
                result
            }
            Self::Function => "'fn".to_string(),
            Self::UnknownUniversal => "'unknown".to_string(),
            Self::ConstRef(true) => "ext_const".to_string(),
            Self::ConstRef(false) => "const".to_string(),
            Self::Place { region, local } => {
                let place = Place::from(*local);
                let exact = place.deref_to_region(*region, cgx.rp);
                let display = exact.unwrap_or(place).to_string(cgx.rp);
                if exact.is_some() {
                    format!("{display:?}")
                } else {
                    format!("AllIn({region:?}, {display:?})")
                }
            }
            Self::Borrow(b) => match b.kind {
                BorrowKind::Shared => {
                    format!("& {:?}", Place::from(b.borrowed_place).to_string(cgx.rp))
                }
                BorrowKind::Mut { .. } => {
                    format!("&mut {:?}", Place::from(b.borrowed_place).to_string(cgx.rp))
                }
                BorrowKind::Shallow => {
                    format!("&sh {:?}", Place::from(b.borrowed_place).to_string(cgx.rp))
                }
            },
            Self::EarlyBound(name) => name.as_str().to_string(),
            Self::LateBound { kind, ctime } => {
                let kind = match kind {
                    BoundRegionKind::BrAnon(..) => "'_",
                    BoundRegionKind::BrNamed(_, name) => name.as_str(),
                    BoundRegionKind::BrEnv => "'env",
                };
                let ctime = match ctime {
                    LateBoundRegionConversionTime::FnCall => "fn",
                    LateBoundRegionConversionTime::HigherRankedType => "hrt",
                    LateBoundRegionConversionTime::AssocTypeProjection(_) => "atp",
                };
                format!("{kind} ({ctime})")
            }
            Self::Placeholder(None) => "'for".to_string(),
            Self::Placeholder(Some(p)) => {
                let kind = match &p.bound.kind {
                    BoundRegionKind::BrAnon(..) => "'_",
                    BoundRegionKind::BrNamed(_, name) => name.as_str(),
                    BoundRegionKind::BrEnv => "'env",
                };
                format!("{kind}@{:?}", p.universe)
            }
            Self::MiscLocal => "?misc?".to_string(),
            Self::UnknownLocal => "???".to_string(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct ParamRegion {
    pub regions: Vec<RegionVid>,
}

impl<'tcx> RegionInfoMap<'tcx> {
    pub fn new(universal: usize, total: usize) -> Self {
        let region_info = IndexVec::from_fn_n(
            |r: RegionVid| {
                if r.index() < universal {
                    RegionKind::UnknownUniversal
                } else {
                    RegionKind::UnknownLocal
                }
            },
            total,
        );
        Self {
            region_info,
            universal,
            constant_regions: Vec::new(),
        }
    }

    pub(super) fn set(&mut self, r: RegionVid, kind: RegionKind<'tcx>) {
        match self.get(r) {
            RegionKind::UnknownUniversal => assert!(kind.is_static() || kind.is_function()),
            RegionKind::UnknownLocal => assert!(
                kind.is_const_ref()
                    || kind.is_place()
                    || kind.is_borrow()
                    || kind.is_early_bound()
                    || kind.is_late_bound()
                    || kind.is_placeholder()
                    || kind.is_misc_local(),
                "{kind:?}"
            ),
            other => panic!("{other:?}"),
        }
        if kind.is_const_ref() {
            self.constant_regions.push(r);
        }
        self.region_info[r] = kind;
    }
    pub(super) fn set_param(&mut self, r: RegionVid, local: RegionVid) {
        let info = &mut self.region_info[r];
        match info {
            RegionKind::Param(ParamRegion { regions }) => regions.push(local),
            RegionKind::UnknownUniversal => {
                *info = RegionKind::Param(ParamRegion {
                    regions: vec![local],
                })
            }
            // Ignore equivalences between static and a local
            RegionKind::Static => (),
            _ => panic!("{info:?}"),
        }
    }
    pub(super) fn set_region_info(&mut self, r: RegionVid, info: RegionVariableInfo) {
        // TODO: figure out the universes stuff
        // assert_eq!(info.universe.index(), 0);
        match info.origin {
            RegionVariableOrigin::MiscVariable(_) => self.set(r, RegionKind::MiscLocal),
            RegionVariableOrigin::PatternRegion(_) => todo!(),
            RegionVariableOrigin::AddrOfRegion(_) => todo!(),
            RegionVariableOrigin::Autoref(_) => todo!(),
            RegionVariableOrigin::Coercion(_) => todo!(),
            RegionVariableOrigin::EarlyBoundRegion(_, name) => {
                self.set(r, RegionKind::EarlyBound(name))
            }
            RegionVariableOrigin::LateBoundRegion(_, kind, ctime) => {
                self.set(r, RegionKind::LateBound { kind, ctime })
            }
            RegionVariableOrigin::UpvarRegion(_, _) => todo!(),
            RegionVariableOrigin::Nll(k) => match k {
                NllRegionVariableOrigin::FreeRegion => {
                    assert!(self.get(r).is_universal());
                    return;
                }
                NllRegionVariableOrigin::Placeholder(p) => {
                    self.set(r, RegionKind::Placeholder(Some(p)))
                }
                NllRegionVariableOrigin::Existential { from_forall: true } => {
                    self.set(r, RegionKind::Placeholder(None))
                }
                NllRegionVariableOrigin::Existential { from_forall: false } => (),
            },
        }
        assert!(!self.get(r).is_universal());
    }

    // #[tracing::instrument(name = "RegionInfoMap::get", level = "trace", skip(self), ret)]
    pub fn get(&self, r: RegionVid) -> &RegionKind<'tcx> {
        &self.region_info[r]
    }
    pub fn is_universal(&self, r: RegionVid) -> bool {
        r.index() < self.universal
    }
    pub(super) fn universal(&self) -> usize {
        self.universal
    }

    pub fn region_len(&self) -> usize {
        self.region_info.len()
    }
    pub fn all_regions(&self) -> impl Iterator<Item = RegionVid> {
        (0..self.region_info.len()).map(RegionVid::from)
    }
    pub fn for_local(&self, r: RegionVid, l: Local) -> bool {
        self.get(r).get_place() == Some(l)
    }
    pub fn const_regions(&self) -> &[RegionVid] {
        &self.constant_regions
    }
}
