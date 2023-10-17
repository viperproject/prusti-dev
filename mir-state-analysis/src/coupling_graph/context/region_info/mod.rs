// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::{ops::ControlFlow, marker::PhantomData};

use prusti_interface::environment::borrowck::facts::{BorrowckFacts, BorrowckFacts2};
use prusti_rustc_interface::{
    borrowck::{
        borrow_set::{BorrowData, TwoPhaseActivation},
        consumers::{BorrowIndex, Borrows, OutlivesConstraint, PoloniusInput, RustcFacts},
    },
    data_structures::fx::FxHashMap,
    dataflow::{Analysis, ResultsCursor},
    index::Idx,
    middle::{
        mir::{visit::{Visitor, TyContext, PlaceContext}, Body, Constant, Local, Location, Operand, RETURN_PLACE, Rvalue, ConstantKind, Terminator, TerminatorKind, PlaceRef, PlaceElem, ProjectionElem, AggregateKind, Promoted, Place as MirPlace},
        ty::{TypeVisitor, TypeSuperVisitable, TypeVisitable, GenericArg, RegionVid, Ty, TyCtxt, TyKind, Region, GenericArgsRef, BoundVariableKind, Const, GenericArgKind},
    },
    span::{Span, Symbol, def_id::DefId},
};

use crate::{
    coupling_graph::region_info::map::ParamRegion,
    utils::{Place, PlaceRepacker, r#const::ConstEval},
};

use self::map::{RegionInfoMap, RegionKind, GenericArgRegion, ConstRegionKind, OtherAnnotationKind, Promote};

use super::{shared_borrow_set::SharedBorrowSet, CgContext};

pub mod map;

#[derive(Debug)]
pub struct RegionInfo<'tcx> {
    pub map: RegionInfoMap<'tcx>,
    pub static_region: RegionVid,
    pub function_region: RegionVid,
}

impl<'tcx> RegionInfo<'tcx> {
    pub fn new(
        rp: PlaceRepacker<'_, 'tcx>,
        input_facts: &PoloniusInput,
        facts2: &BorrowckFacts2<'tcx>,
        sbs: &SharedBorrowSet<'tcx>,
    ) -> Self {
        let mut map = RegionInfoMap::new(
            input_facts.universal_region.len(),
            facts2.region_inference_context.var_infos.len(),
        );
        // Assumption: universal regions are the first regions
        debug_assert!(input_facts
            .universal_region
            .iter()
            .all(|&r| map.is_universal(r)));

        // Init universals
        let (static_region, function_region) =
            Self::initialize_universals(&mut map, rp, input_facts, facts2);

        // Init consts
        Self::initialize_consts(&mut map, rp, facts2);

        // Init locals
        Self::initialize_locals(&mut map, rp, input_facts, facts2, sbs);

        // Init from `var_infos`
        for r in map.all_regions() {
            let info = facts2.region_inference_context.var_infos[r];
            map.set_region_info(r, info);
        }

        // We should have figured out all local regions
        for r in map.all_regions() {
            // TODO: resolve all unknowns
            assert!(!map.get(r).is_unknown_local(), "{r:?} is unknown: {map:?}");
            // assert!(!map.get(r).unknown(), "{r:?} is unknown: {map:?}");
        }

        Self {
            map,
            static_region,
            function_region,
        }
    }

    pub fn initialize_universals(
        map: &mut RegionInfoMap<'tcx>,
        rp: PlaceRepacker<'_, 'tcx>,
        input_facts: &PoloniusInput,
        facts2: &BorrowckFacts2,
    ) -> (RegionVid, RegionVid) {
        let static_region = *input_facts.universal_region.first().unwrap();
        // Check that static is actually first
        if cfg!(debug_symbols) {
            // Static should outlive all other placeholders
            let outlives = input_facts
                .known_placeholder_subset
                .iter()
                .filter(|&&(sup, sub)| {
                    assert_ne!(static_region, sub);
                    static_region == sup
                });
            assert_eq!(outlives.count(), map.universal() - 1);
        }
        let function_region = *input_facts.universal_region.last().unwrap();
        // Check that the function region is actually last
        if cfg!(debug_symbols) {
            // All other placeholders should outlive the function region
            let outlives = input_facts
                .known_placeholder_subset
                .iter()
                .filter(|&&(sup, sub)| {
                    assert_ne!(function_region, sup);
                    function_region == sub
                });
            assert_eq!(outlives.count(), map.universal() - 1);
        }

        // Collect equivalences between universal and local
        let mut equivalence_map: FxHashMap<(RegionVid, RegionVid), u8> = FxHashMap::default();
        for c in facts2
            .region_inference_context
            .outlives_constraints()
            .filter(|o| {
                o.locations.from_location().is_none()
                    && (map.is_universal(o.sup) || map.is_universal(o.sub))
                    && !(map.is_universal(o.sup) && map.is_universal(o.sub))
            })
        {
            let (universal, other, incr) = if map.is_universal(c.sup) {
                (c.sup, c.sub, 1)
            } else {
                (c.sub, c.sup, 2)
            };
            let entry = equivalence_map.entry((universal, other)).or_default();
            *entry |= incr;
            // Note: Outlives constraints may be duplicated!!
            // e.g. in `hashbrown-0.14.1` in `hashbrown::raw::RawTable::<T, A>::clear::{closure#0}` at `src/raw/mod.rs:1021:37: 1021:66 (#0)`
        }

        // Set the entries in the map
        map.set(static_region, RegionKind::Static);
        for ((universal, local), sum) in equivalence_map {
            if sum == 3 {
                map.set_param(universal, local);
            }
        }
        map.set(function_region, RegionKind::Function);
        (static_region, function_region)
    }

    pub fn initialize_consts(map: &mut RegionInfoMap<'tcx>, rp: PlaceRepacker<'_, 'tcx>, facts2: &BorrowckFacts2<'tcx>) {
        let mut collector = ConstantRegionCollector {
            map, inner_kind: None, fn_ptr: false, rp, facts2, return_ty: None, promoted_idx: Promote::NotPromoted, regions_set: None, max_region: None,
        };
        for (idx, promoted) in rp.promoted().iter_enumerated() {
            collector.promoted_idx = Promote::Promoted(idx);
            collector.visit_body(promoted);
        }
        collector.promoted_idx = Promote::NotPromoted;
        collector.visit_body(rp.body());
        // for constant in &rp.body().required_consts {
        //     for r in constant.ty().walk().flat_map(|ga| ga.as_region()) {
        //         assert!(r.is_var(), "{r:?} in {constant:?}");
        //         map.set(r.as_var(), RegionKind::ConstRef(ConstRegionKind::ExternalConst, Vec::new()));
        //     }
        // }
    }

    pub fn initialize_locals(
        map: &mut RegionInfoMap<'tcx>,
        rp: PlaceRepacker<'_, 'tcx>,
        input_facts: &PoloniusInput,
        facts2: &BorrowckFacts2<'tcx>,
        sbs: &SharedBorrowSet<'tcx>,
    ) {
        for &(local, region) in &input_facts.use_of_var_derefs_origin {
            // TODO: remove
            map.check_already_local(region, local);
        }
        for data in sbs
            .location_map
            .values()
            .chain(facts2.borrow_set.location_map.values())
        {
            map.check_already_borrow(data.region, data);
        }
    }
}

struct ConstantRegionCollector<'a, 'b, 'tcx> {
    map: &'a mut RegionInfoMap<'tcx>,
    inner_kind: Option<RegionKind<'tcx>>,
    promoted_idx: Promote,
    fn_ptr: bool,
    rp: PlaceRepacker<'b, 'tcx>,
    facts2: &'b BorrowckFacts2<'tcx>,
    return_ty: Option<Ty<'tcx>>,
    // Set this to start counting regions
    regions_set: Option<usize>,
    max_region: Option<RegionVid>,
}
impl<'tcx> ConstantRegionCollector<'_, '_, 'tcx> {
    fn with_kind<T>(&mut self, kind: RegionKind<'tcx>, f: impl FnOnce(&mut Self) -> T) -> T {
        let disc = std::mem::discriminant(&kind);
        let old_kind = self.inner_kind.replace(kind);
        assert!(old_kind.is_none());
        let t = f(self);
        let kind = self.inner_kind.take();
        assert_eq!(std::mem::discriminant(&kind.unwrap()), disc);
        self.inner_kind = old_kind;
        t
    }
    
    fn visit_generics_args(&mut self, did: DefId, generics: GenericArgsRef<'tcx>) {
        for (gen_idx, arg) in generics.iter().enumerate() {
            let inner_kind = self.inner_kind.as_mut().unwrap();
            inner_kind.set_fn_generic(GenericArgRegion { did, gen_idx, full_ty: arg.as_type() });
            arg.visit_with(self);
            self.inner_kind.as_mut().unwrap().unset_fn_generic();
        }
    }

    fn set_region(&mut self, r: RegionVid, kind: RegionKind<'tcx>) {
        assert!(self.promoted_idx == Promote::NotPromoted || kind.promoted(), "{kind:?} {r:?}");
        self.map.set(r, kind);
        if let Some(regions_set) = &mut self.regions_set {
            *regions_set += 1;
            if let Some(max_region) = self.max_region {
                assert_eq!(max_region.index() + 1, r.index());
            }
            self.max_region = Some(r);
        }
    }
}

impl<'tcx> Visitor<'tcx> for ConstantRegionCollector<'_, '_, 'tcx> {
    #[tracing::instrument(name = "ConstantRegionCollector::visit_ty", level = "trace", skip(self), fields(promoted_idx = ?self.promoted_idx, inner_kind = ?self.inner_kind))]
    fn visit_ty(&mut self, ty: Ty<'tcx>, ctx: TyContext) {
        // println!("Ty ({ctx:?}): {ty:?}");
        match ctx {
            TyContext::LocalDecl { local, .. } => {
                if local == RETURN_PLACE {
                    assert!(self.regions_set.is_none() && self.max_region.is_none());
                    self.regions_set = Some(0);
                }
                self.with_kind(RegionKind::Place { local, ty, promoted: self.promoted_idx, fn_generic: Vec::new() }, 
                    |this| ty.visit_with(this)
                );
                if local == RETURN_PLACE {
                    // TODO: remove this once `https://github.com/rust-lang/rust/pull/116792` lands
                    let return_regions = self.regions_set.take().unwrap();
                    if let Some(new_max) = self.max_region.take() {
                        for r in (0..return_regions).rev().map(|sub| RegionVid::from_usize(new_max.index() - return_regions - sub)) {
                            self.map.set(r, RegionKind::UnusedReturnBug(self.promoted_idx));
                        }
                    }
                }
            }
            TyContext::ReturnTy(_) => {
                assert_eq!(ty, self.return_ty.unwrap())
            }
            TyContext::UserTy(_) => {
                self.with_kind(RegionKind::OtherAnnotation(OtherAnnotationKind::UserTy, ty, Vec::new()), 
                    |this| ty.visit_with(this)
                );
            }
            TyContext::YieldTy(_) =>  {
                self.with_kind(RegionKind::OtherAnnotation(OtherAnnotationKind::YieldTy, ty, Vec::new()), 
                    |this| ty.visit_with(this)
                );
            }
            TyContext::Location(_location) => {
                assert!(self.inner_kind.is_some());
                ty.visit_with(self);
            }
        }
    }

    #[tracing::instrument(name = "ConstantRegionCollector::visit_projection_elem", level = "trace", skip(self), fields(promoted_idx = ?self.promoted_idx, inner_kind = ?self.inner_kind))]
    fn visit_projection_elem(&mut self, place_ref: PlaceRef<'tcx>, elem: PlaceElem<'tcx>, ctx: PlaceContext, location: Location) {
        // println!("Projection elem ({ctx:?}): {place_ref:?} ({elem:?}) [{location:?}]");
        let place = Place::from(place_ref).mk_place_elem(elem, self.rp);
        if let Some(ty) = place.last_projection_ty() {
            assert!(matches!(elem, ProjectionElem::Field(..) | ProjectionElem::OpaqueCast(..)));
            self.with_kind(RegionKind::ProjectionAnnotation(place, ty, Vec::new()), 
                |this| this.super_projection_elem(place_ref, elem, ctx, location)
            )
        } else {
            self.super_projection_elem(place_ref, elem, ctx, location)
        }
    }
    #[tracing::instrument(name = "ConstantRegionCollector::visit_ty_const", level = "trace", skip(self), fields(promoted_idx = ?self.promoted_idx, inner_kind = ?self.inner_kind))]
    fn visit_ty_const(&mut self, ct: Const<'tcx>, _location: Location) {
        // e.g. from `Rvalue::Repeat`
        self.with_kind(RegionKind::ConstRef(ConstRegionKind::TyConst, Vec::new()), |this| {
            ct.visit_with(this);
        });
    }
    #[tracing::instrument(name = "ConstantRegionCollector::visit_constant", level = "trace", skip(self), fields(promoted_idx = ?self.promoted_idx, inner_kind = ?self.inner_kind))]
    fn visit_constant(&mut self, constant: &Constant<'tcx>, _location: Location) {
        // println!("Constant: {:?}", constant.ty());
        assert!(self.inner_kind.is_none());
        self.with_kind(RegionKind::ConstRef(ConstRegionKind::Const(self.promoted_idx), Vec::new()), |this| {
            constant.visit_with(this);
        });
    }
    #[tracing::instrument(name = "ConstantRegionCollector::visit_args", level = "trace", skip(self), fields(promoted_idx = ?self.promoted_idx, inner_kind = ?self.inner_kind))]
    fn visit_args(&mut self, args: &GenericArgsRef<'tcx>, location: Location) {
        // Do nothing since already handled by `Rvalue::Aggregate`.
    }
    #[tracing::instrument(name = "ConstantRegionCollector::visit_region", level = "trace", skip(self), fields(promoted_idx = ?self.promoted_idx, inner_kind = ?self.inner_kind))]
    fn visit_region(&mut self, region: Region<'tcx>, location: Location) {
        // Do nothing since already handled by `Rvalue::Ref`.
    }

    #[tracing::instrument(name = "ConstantRegionCollector::visit_operand", level = "trace", skip(self), fields(promoted_idx = ?self.promoted_idx, inner_kind = ?self.inner_kind))]
    fn visit_operand(&mut self, operand: &Operand<'tcx>, location: Location) {
        // Temporarily remove `OtherAnnotationKind::RvalueTy`
        let from_rvalue = matches!(self.inner_kind, Some(RegionKind::OtherAnnotation(OtherAnnotationKind::RvalueTy(_), _, _)));
        if from_rvalue {
            let kind = self.inner_kind.take();
            self.super_operand(operand, location);
            self.inner_kind = kind;
        } else {
            self.super_operand(operand, location)
        }
    }
    #[tracing::instrument(name = "ConstantRegionCollector::visit_assign", level = "trace", skip(self), fields(promoted_idx = ?self.promoted_idx, inner_kind = ?self.inner_kind))]
    fn visit_assign(&mut self, place: &MirPlace<'tcx>, rvalue: &Rvalue<'tcx>, location: Location) {
        match rvalue {
            &Rvalue::Aggregate(box AggregateKind::Adt(did, _, generics, _, _), _) |
            &Rvalue::Aggregate(box AggregateKind::Closure(did, generics), _) |
            &Rvalue::Aggregate(box AggregateKind::Generator(did, generics, _), _) => {
                self.with_kind(RegionKind::ConstRef(ConstRegionKind::Aggregate(self.promoted_idx), Vec::new()),
                    |this| this.visit_generics_args(did, generics));
                self.super_assign(place, rvalue, location); // For the operand
            }
            &Rvalue::Ref(region, kind, borrowed_place) => {
                let is_non_promoted = matches!(self.promoted_idx, Promote::NotPromoted);
                let location_map = &self.facts2.borrow_set.location_map;
                if is_non_promoted && location_map.contains_key(&location) {
                    let borrow = location_map.get(&location).unwrap();
                    assert_eq!(borrow.region, region.as_var());
                    self.set_region(borrow.region, RegionKind::Borrow(borrow.clone(), Promote::NotPromoted))
                } else {
                    let region = region.as_var();
                    let borrow = BorrowData {
                        reserve_location: location,
                        activation_location: TwoPhaseActivation::NotTwoPhase,
                        kind,
                        region,
                        borrowed_place,
                        assigned_place: *place,
                    };
                    self.set_region(borrow.region, RegionKind::Borrow(borrow, self.promoted_idx))
                }
                self.super_assign(place, rvalue, location)
            }
            Rvalue::Aggregate(box AggregateKind::Array(ty), _) |
            Rvalue::Cast(_, _, ty) |
            Rvalue::NullaryOp(_, ty) |
            Rvalue::ShallowInitBox(_, ty) => {
                self.with_kind(RegionKind::OtherAnnotation(OtherAnnotationKind::RvalueTy(self.promoted_idx), *ty, Vec::new()),
                    |this| this.super_assign(place, rvalue, location)
                );
            }
            _ => self.super_assign(place, rvalue, location),
        }
    }
    #[tracing::instrument(name = "ConstantRegionCollector::visit_body", level = "trace", skip_all, fields(promoted_idx = ?self.promoted_idx, inner_kind = ?self.inner_kind))]
    fn visit_body(&mut self, body: &Body<'tcx>) {
        // println!("body: {body:#?}");
        self.return_ty = Some(body.local_decls[RETURN_PLACE].ty);
        self.super_body(body);
        self.return_ty = None;
    }
}

impl<'tcx> TypeVisitor<TyCtxt<'tcx>> for ConstantRegionCollector<'_, '_, 'tcx> {
    #[tracing::instrument(name = "ConstantRegionCollector::visit_region", level = "trace", skip(self), fields(promoted_idx = ?self.promoted_idx, inner_kind = ?self.inner_kind))]
    fn visit_region(&mut self, r: Region<'tcx>) -> ControlFlow<Self::BreakTy> {
        // println!("Region: {r:?}");
        if self.fn_ptr && !r.is_var() {
            return ControlFlow::Continue(());
        }
        let kind = self.inner_kind.clone().unwrap();
        self.set_region(r.as_var(), kind);
        ControlFlow::Continue(())
    }
    #[tracing::instrument(name = "ConstantRegionCollector::visit_ty", level = "trace", skip(self), fields(promoted_idx = ?self.promoted_idx, inner_kind = ?self.inner_kind))]
    fn visit_ty(&mut self, ty: Ty<'tcx>) -> ControlFlow<Self::BreakTy> {
        // println!("Ty inner: {ty:?}");
        match ty.kind() {
            &TyKind::FnDef(did, generics) |
            &TyKind::Closure(did, generics) => {
                self.visit_generics_args(did, generics);
                ControlFlow::Continue(())
            }
            TyKind::FnPtr(_) => {
                self.fn_ptr = true;
                let r = ty.super_visit_with(self);
                self.fn_ptr = false;
                r
            }
            // Maybe we want to handle the `region` here differently?
            // TyKind::Dynamic(other, region, _) => todo!(),
            TyKind::Generator(_, _, _) => todo!(),
            TyKind::GeneratorWitness(_) => todo!(),
            TyKind::GeneratorWitnessMIR(_, _) => todo!(),
            TyKind::Bound(_, _) => todo!(),
            _ => ty.super_visit_with(self),
        }
    }
}
