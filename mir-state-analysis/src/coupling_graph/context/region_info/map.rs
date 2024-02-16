// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::{fmt::Display, marker::PhantomData};

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
        mir::{
            Body, BorrowKind, Local, Location, Operand, PlaceElem, PlaceRef, Promoted, RETURN_PLACE,
        },
        ty::{BoundRegionKind, PlaceholderRegion, RegionVid, Ty, TyCtxt, TyKind},
    },
    span::{def_id::DefId, Span, Symbol},
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

#[derive(Debug, Clone, Copy)]
pub struct GenericArgRegion<'tcx> {
    pub did: DefId,
    pub gen_idx: usize,
    pub full_ty: Option<Ty<'tcx>>,
}

impl<'tcx> GenericArgRegion<'tcx> {
    fn to_string(gars: &Vec<Self>, cgx: &CgContext<'_, 'tcx>) -> String {
        gars.iter()
            .map(|gar| {
                let tcx = cgx.rp.tcx();
                let generic = tcx.generics_of(gar.did).param_at(gar.gen_idx, tcx);
                assert_eq!(generic.kind.is_ty_or_const(), gar.full_ty.is_some());
                let ty = gar.full_ty.map(|ty| format!(" = {ty}")).unwrap_or_default();
                if tcx.is_closure(gar.did) {
                    format!(" closure::<{}{ty}>", generic.name.as_str())
                } else {
                    format!(
                        " {}::<{}{ty}>",
                        tcx.item_name(gar.did).as_str(),
                        generic.name.as_str()
                    )
                }
            })
            .collect()
    }
}

#[derive(Debug, Clone, Copy)]
pub enum ConstRegionKind {
    Const(Promote),
    TyConst,
    /// Crated constructing an Aggregate with internal regions,
    /// for example a struct with reference-typed fields.
    Aggregate(Promote),
}
impl Display for ConstRegionKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConstRegionKind::Const(p) => write!(f, "const{p}"),
            ConstRegionKind::TyConst => write!(f, "tconst"),
            ConstRegionKind::Aggregate(p) => write!(f, "aggregate{p}"),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum OtherAnnotationKind {
    UserTy,
    YieldTy,
    RvalueTy(Promote),
}
impl Display for OtherAnnotationKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OtherAnnotationKind::UserTy => write!(f, "user"),
            OtherAnnotationKind::YieldTy => write!(f, "yield"),
            OtherAnnotationKind::RvalueTy(p) => write!(f, "rvalue{p}"),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Promote {
    NotPromoted,
    Promoted(Promoted),
}
impl Display for Promote {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Promote::NotPromoted => Ok(()),
            Promote::Promoted(p) => write!(f, " @promoted[{}]", p.index()),
        }
    }
}

#[derive(Debug, Clone)]
pub enum RegionKind<'tcx> {
    // Universal regions (placeholders)
    Static,
    Param(ParamRegion),
    Function,
    UnknownUniversal,
    //  - update `fn universal` if a new one is added!

    // Local regions
    ConstRef(ConstRegionKind, Vec<GenericArgRegion<'tcx>>),
    Place {
        local: Local,
        ty: Ty<'tcx>,
        promoted: Promote,
        fn_generic: Vec<GenericArgRegion<'tcx>>,
    },
    Borrow(BorrowData<'tcx>, Promote),
    UnusedReturnBug(Promote), // TODO: remove once `https://github.com/rust-lang/rust/pull/116792` lands

    // AggregateGeneric(DefId, usize, Option<Ty<'tcx>>),
    // FnGeneric(DefId, usize, Option<Ty<'tcx>>),
    EarlyBound(Symbol),
    LateBound {
        // span: Span,
        kind: BoundRegionKind,
        ctime: LateBoundRegionConversionTime,
    },
    Placeholder(Option<PlaceholderRegion>),
    ProjectionAnnotation(Place<'tcx>, Ty<'tcx>, Vec<GenericArgRegion<'tcx>>),
    OtherAnnotation(OtherAnnotationKind, Ty<'tcx>, Vec<GenericArgRegion<'tcx>>),
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
    pub fn get_param(&self) -> Option<&ParamRegion> {
        match self {
            Self::Param(p) => Some(p),
            _ => None,
        }
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
    pub fn is_unused_return_bug(&self) -> bool {
        matches!(self, Self::UnusedReturnBug(..))
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
    pub fn is_projection_annotation(&self) -> bool {
        matches!(self, Self::ProjectionAnnotation(..))
    }
    pub fn is_other_annotation(&self) -> bool {
        matches!(self, Self::OtherAnnotation(..))
    }
    pub fn is_misc_local(&self) -> bool {
        matches!(self, Self::MiscLocal)
    }
    pub fn is_unknown_local(&self) -> bool {
        matches!(self, Self::UnknownLocal)
    }

    pub fn promoted(&self) -> bool {
        matches!(
            self,
            Self::Place {
                promoted: Promote::Promoted(..),
                ..
            } | Self::Borrow(_, Promote::Promoted(..))
                | Self::UnusedReturnBug(Promote::Promoted(..))
                | Self::OtherAnnotation(OtherAnnotationKind::RvalueTy(Promote::Promoted(..)), _, _)
                | Self::ConstRef(ConstRegionKind::Const(Promote::Promoted(..)), _)
                | Self::ConstRef(ConstRegionKind::Aggregate(Promote::Promoted(..)), _)
        )
    }
    pub fn unknown(&self) -> bool {
        matches!(self, Self::UnknownUniversal | Self::UnknownLocal)
    }

    pub fn universal(&self) -> bool {
        matches!(
            self,
            Self::Static | Self::Param(..) | Self::Function | Self::UnknownUniversal
        )
    }
    pub fn local(&self) -> bool {
        !self.universal()
    }

    pub fn from_function_depth(&self) -> usize {
        match self {
            Self::LateBound {
                ctime: LateBoundRegionConversionTime::FnCall,
                ..
            } => 1,
            Self::ConstRef(_, fn_generic)
            | Self::Place { fn_generic, .. }
            | Self::ProjectionAnnotation(_, _, fn_generic)
            | Self::OtherAnnotation(_, _, fn_generic) => fn_generic.len(),
            _ => 0,
        }
    }

    pub fn set_fn_generic(&mut self, generic: GenericArgRegion<'tcx>) {
        match self {
            Self::ConstRef(_, fn_generic)
            | Self::Place { fn_generic, .. }
            | Self::ProjectionAnnotation(_, _, fn_generic)
            | Self::OtherAnnotation(_, _, fn_generic) => fn_generic.push(generic),
            _ => panic!("{self:?} ({generic:?})"),
        }
    }
    pub fn unset_fn_generic(&mut self) {
        match self {
            Self::ConstRef(_, fn_generic)
            | Self::Place { fn_generic, .. }
            | Self::ProjectionAnnotation(_, _, fn_generic)
            | Self::OtherAnnotation(_, _, fn_generic) => assert!(fn_generic.pop().is_some()),
            _ => panic!(),
        }
    }

    // #[tracing::instrument(name = "RegionKind::get_place", level = "trace", ret)]
    pub fn get_place(&self) -> Option<Local> {
        match self {
            Self::Place {
                local,
                promoted: Promote::NotPromoted,
                ..
            } => Some(*local),
            _ => None,
        }
    }
    pub fn get_borrow(&self) -> Option<&BorrowData<'tcx>> {
        match self {
            Self::Borrow(data, Promote::NotPromoted) => Some(data),
            _ => None,
        }
    }
    pub fn get_borrow_or_projection_local(&self) -> Option<Local> {
        match self {
            Self::Borrow(data, Promote::NotPromoted) => Some(data.borrowed_place.local),
            Self::ProjectionAnnotation(place, _, _) => Some(place.local),
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
            Self::ConstRef(kind, fn_generic) => {
                format!("{kind}{}", GenericArgRegion::to_string(fn_generic, cgx))
            }
            Self::Place {
                local,
                ty,
                promoted,
                fn_generic,
            } => {
                let place = Place::from(*local);
                // let exact = place.deref_to_region(*region, cgx.rp);
                // let display = exact.unwrap_or(place).to_string(cgx.rp);
                // if exact.is_some() {
                //     format!("{display:?}{promoted}")
                // } else {
                format!("AllIn({:?} = {ty}){promoted}", place.to_string(cgx.rp))
                // }
            }
            Self::Borrow(b, promoted) => match b.kind {
                BorrowKind::Shared => {
                    format!(
                        "& {:?}{promoted}",
                        Place::from(b.borrowed_place).to_string(cgx.rp)
                    )
                }
                BorrowKind::Mut { .. } => {
                    format!(
                        "&mut {:?}{promoted}",
                        Place::from(b.borrowed_place).to_string(cgx.rp)
                    )
                }
                BorrowKind::Shallow => {
                    format!(
                        "&sh {:?}{promoted}",
                        Place::from(b.borrowed_place).to_string(cgx.rp)
                    )
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
            Self::ProjectionAnnotation(place, ty, fn_generic) => format!(
                "{:?}: {ty}{}",
                place.to_string(cgx.rp),
                GenericArgRegion::to_string(fn_generic, cgx)
            ),
            &Self::OtherAnnotation(kind, ty, ref fn_generic) => format!(
                "{kind} {ty}{}",
                GenericArgRegion::to_string(fn_generic, cgx)
            ),
            Self::MiscLocal => "?misc?".to_string(),
            Self::UnusedReturnBug(..) => unreachable!(),
            Self::UnknownLocal => "???".to_string(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
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

    pub(super) fn check_already_local(&mut self, r: RegionVid, l: Local) {
        let kind = self.get(r);
        if kind.get_place().is_none() {
            panic!("{r:?}: {:?} != {:?}", kind, l);
        }
        assert_eq!(kind.get_place().unwrap(), l);
    }
    pub(super) fn check_already_borrow(&mut self, r: RegionVid, b: &BorrowData<'tcx>) {
        let data = self.get(r).get_borrow().unwrap();
        assert_eq!(data.to_string(), b.to_string());
        assert_eq!(data.reserve_location, b.reserve_location);
        assert_eq!(data.activation_location, b.activation_location);
    }
    pub(super) fn set(&mut self, r: RegionVid, kind: RegionKind<'tcx>) {
        match self.get(r) {
            RegionKind::UnknownUniversal => assert!(kind.is_static() || kind.is_function()),
            RegionKind::UnknownLocal => assert!(
                kind.is_const_ref()
                    || kind.is_place()
                    || kind.is_borrow()
                    || kind.is_unused_return_bug()
                    || kind.is_early_bound()
                    || kind.is_late_bound()
                    || kind.is_placeholder()
                    || kind.is_projection_annotation()
                    || kind.is_other_annotation()
                    || kind.is_misc_local(),
                "{kind:?}"
            ),
            other => panic!("{other:?} ({kind:?})"),
        }
        if kind.is_const_ref() && kind.from_function_depth() == 0 {
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
                self.set(r, RegionKind::EarlyBound(name));
                todo!(); // Figure out how this compares to `FnGeneric`
            }
            RegionVariableOrigin::LateBoundRegion(_, kind, ctime) => {
                self.set(r, RegionKind::LateBound { kind, ctime })
            }
            RegionVariableOrigin::UpvarRegion(_, _) => todo!(),
            RegionVariableOrigin::Nll(k) => match k {
                NllRegionVariableOrigin::FreeRegion => {
                    assert!(self.get(r).universal());
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
        assert!(!self.get(r).universal());
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
    pub fn universal_regions(&self) -> impl Iterator<Item = RegionVid> {
        (0..self.universal).map(RegionVid::from)
    }
    pub fn for_local(&self, r: RegionVid, l: Local) -> bool {
        self.get(r).get_place() == Some(l)
            || self.get(r).get_borrow_or_projection_local() == Some(l)
    }
    pub fn const_regions(&self) -> &[RegionVid] {
        &self.constant_regions
    }
}
