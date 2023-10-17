// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_rustc_interface::{
    data_structures::fx::FxHashSet,
    dataflow::storage,
    index::{bit_set::BitSet, Idx, IndexVec},
    middle::{
        mir::{
            tcx::PlaceTy, Body, HasLocalDecls, Local, Mutability, Place as MirPlace, PlaceElem,
            ProjectionElem, Promoted,
        },
        ty::{RegionVid, Region, Ty, TyCtxt, TyKind},
    },
    target::abi::FieldIdx,
};

use crate::utils::ty::{DeepTypeVisitable, DeepTypeVisitor, Stack};

use super::Place;

#[derive(Debug, Clone, Copy)]
pub enum ProjectionRefKind {
    Ref(Mutability),
    RawPtr(Mutability),
    Box,
    Other,
}
impl ProjectionRefKind {
    pub fn is_ref(self) -> bool {
        matches!(self, ProjectionRefKind::Ref(_))
    }
    pub fn is_raw_ptr(self) -> bool {
        matches!(self, ProjectionRefKind::RawPtr(_))
    }
    pub fn is_box(self) -> bool {
        matches!(self, ProjectionRefKind::Box)
    }
    pub fn is_deref(self) -> bool {
        self.is_ref() || self.is_raw_ptr() || self.is_box()
    }
    pub fn is_shared_ref(self) -> bool {
        matches!(self, ProjectionRefKind::Ref(Mutability::Not))
    }
}

#[derive(Copy, Clone)]
// TODO: modified version of fns taken from `prusti-interface/src/utils.rs`; deduplicate
pub struct PlaceRepacker<'a, 'tcx: 'a> {
    pub(super) mir: &'a Body<'tcx>,
    pub(super) promoted: &'a IndexVec<Promoted, Body<'tcx>>,
    pub(super) tcx: TyCtxt<'tcx>,
}

impl<'a, 'tcx: 'a> PlaceRepacker<'a, 'tcx> {
    pub fn new(mir: &'a Body<'tcx>, promoted: &'a IndexVec<Promoted, Body<'tcx>>, tcx: TyCtxt<'tcx>) -> Self {
        Self { mir, promoted, tcx }
    }

    pub fn local_count(self) -> usize {
        self.mir.local_decls().len()
    }

    pub fn always_live_locals(self) -> BitSet<Local> {
        storage::always_storage_live_locals(self.mir)
    }
    pub fn always_live_locals_non_args(self) -> BitSet<Local> {
        let mut all = self.always_live_locals();
        for arg in 0..self.mir.arg_count + 1 {
            // Includes `RETURN_PLACE`
            all.remove(Local::new(arg));
        }
        all
    }

    pub fn body(self) -> &'a Body<'tcx> {
        self.mir
    }

    pub fn promoted(self) -> &'a IndexVec<Promoted, Body<'tcx>> {
        self.promoted
    }

    pub fn tcx(self) -> TyCtxt<'tcx> {
        self.tcx
    }
}

impl<'tcx> Place<'tcx> {
    pub fn to_rust_place(self, repacker: PlaceRepacker<'_, 'tcx>) -> MirPlace<'tcx> {
        MirPlace {
            local: self.local,
            projection: repacker.tcx.mk_place_elems(self.projection),
        }
    }

    /// Subtract the `to` place from the `self` place. The
    /// subtraction is defined as set minus between `self` place replaced
    /// with a set of places that are unrolled up to the same level as
    /// `to` and the singleton `to` set. For example,
    /// `expand(x.f, x.f.g.h)` is performed by unrolling `x.f` into
    /// `{x.g, x.h, x.f.f, x.f.h, x.f.g.f, x.f.g.g, x.f.g.h}` and
    /// subtracting `{x.f.g.h}` from it, which results into (`{x.f, x.f.g}`, `{x.g, x.h,
    /// x.f.f, x.f.h, x.f.g.f, x.f.g.g}`). The first vector contains the chain of
    /// places that were expanded along with the target to of each expansion.
    #[tracing::instrument(level = "trace", skip(repacker), ret)]
    pub fn expand(
        mut self,
        to: Self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> (Vec<(Self, Self, ProjectionRefKind)>, Vec<Self>) {
        assert!(
            self.is_prefix(to),
            "The minuend ({self:?}) must be the prefix of the subtrahend ({to:?})."
        );
        let mut place_set = Vec::new();
        let mut expanded = Vec::new();
        while self.projection.len() < to.projection.len() {
            let (new_minuend, places, kind) = self.expand_one_level(to, repacker);
            expanded.push((self, new_minuend, kind));
            place_set.extend(places);
            self = new_minuend;
        }
        (expanded, place_set)
    }

    /// Try to collapse all places in `from` by following the
    /// `guide_place`. This function is basically the reverse of
    /// `expand`.
    #[tracing::instrument(level = "trace", skip(repacker), ret)]
    pub fn collapse(
        self,
        from: &mut FxHashSet<Self>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Vec<(Self, Self, ProjectionRefKind)> {
        let mut collapsed = Vec::new();
        let mut guide_places = vec![self];
        while let Some(guide_place) = guide_places.pop() {
            if !from.remove(&guide_place) {
                let expand_guide = *from
                    .iter()
                    .find(|p| guide_place.is_prefix(**p))
                    .unwrap_or_else(|| {
                        panic!(
                            "The `from` set didn't contain all \
                            the places required to construct the \
                            `guide_place`. Currently tried to find \
                            `{guide_place:?}` in `{from:?}`."
                        )
                    });
                let (expanded, new_places) = guide_place.expand(expand_guide, repacker);
                // Doing `collapsed.extend(expanded)` would result in a reversed order.
                // Could also change this to `collapsed.push(expanded)` and return Vec<Vec<_>>.
                collapsed.extend(expanded);
                guide_places.extend(new_places);
                from.remove(&expand_guide);
            }
        }
        collapsed.reverse();
        collapsed
    }

    /// Expand `self` one level down by following the `guide_place`.
    /// Returns the new `self` and a vector containing other places that
    /// could have resulted from the expansion. Note: this vector is always
    /// incomplete when projecting with `Index` or `Subslice` and also when
    /// projecting a slice type with `ConstantIndex`!
    #[tracing::instrument(level = "trace", skip(repacker), ret)]
    pub fn expand_one_level(
        self,
        guide_place: Self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> (Self, Vec<Self>, ProjectionRefKind) {
        let index = self.projection.len();
        let new_projection = repacker.tcx.mk_place_elems_from_iter(
            self.projection
                .iter()
                .copied()
                .chain([guide_place.projection[index]]),
        );
        let new_current_place = Place::new(self.local, new_projection);
        let (other_places, kind) = match guide_place.projection[index] {
            ProjectionElem::Field(projected_field, _field_ty) => {
                let other_places = self.expand_field(Some(projected_field.index()), repacker);
                (other_places, ProjectionRefKind::Other)
            }
            ProjectionElem::ConstantIndex {
                offset,
                min_length,
                from_end,
            } => {
                let range = if from_end {
                    1..min_length + 1
                } else {
                    0..min_length
                };
                assert!(range.contains(&offset));
                let other_places = range
                    .filter(|&i| i != offset)
                    .map(|i| {
                        repacker
                            .tcx
                            .mk_place_elem(
                                self.to_rust_place(repacker),
                                ProjectionElem::ConstantIndex {
                                    offset: i,
                                    min_length,
                                    from_end,
                                },
                            )
                            .into()
                    })
                    .collect();
                (other_places, ProjectionRefKind::Other)
            }
            ProjectionElem::Deref => {
                let typ = self.ty(repacker);
                let kind = match typ.ty.kind() {
                    TyKind::Ref(_, _, mutbl) => ProjectionRefKind::Ref(*mutbl),
                    TyKind::RawPtr(ptr) => ProjectionRefKind::RawPtr(ptr.mutbl),
                    _ if typ.ty.is_box() => ProjectionRefKind::Box,
                    _ => unreachable!(),
                };
                (Vec::new(), kind)
            }
            ProjectionElem::Index(..)
            | ProjectionElem::Subslice { .. }
            | ProjectionElem::Downcast(..)
            | ProjectionElem::OpaqueCast(..) => (Vec::new(), ProjectionRefKind::Other),
        };
        (new_current_place, other_places, kind)
    }

    /// Expands a place `x.f.g` of type struct into a vector of places for
    /// each of the struct's fields `{x.f.g.f, x.f.g.g, x.f.g.h}`. If
    /// `without_field` is not `None`, then omits that field from the final
    /// vector.
    pub fn expand_field(
        self,
        without_field: Option<usize>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Vec<Self> {
        let mut places = Vec::new();
        let typ = self.ty(repacker);
        if !matches!(typ.ty.kind(), TyKind::Adt(..)) {
            assert!(
                typ.variant_index.is_none(),
                "We have assumed that only enums can have variant_index set. Got {typ:?}."
            );
        }
        match typ.ty.kind() {
            TyKind::Adt(def, substs) => {
                let variant = typ
                    .variant_index
                    .map(|i| def.variant(i))
                    .unwrap_or_else(|| def.non_enum_variant());
                for (index, field_def) in variant.fields.iter().enumerate() {
                    if Some(index) != without_field {
                        let field = FieldIdx::from_usize(index);
                        let field_place = repacker.tcx.mk_place_field(
                            self.to_rust_place(repacker),
                            field,
                            field_def.ty(repacker.tcx, substs),
                        );
                        places.push(field_place.into());
                    }
                }
            }
            TyKind::Tuple(slice) => {
                for (index, arg) in slice.iter().enumerate() {
                    if Some(index) != without_field {
                        let field = FieldIdx::from_usize(index);
                        let field_place =
                            repacker
                                .tcx
                                .mk_place_field(self.to_rust_place(repacker), field, arg);
                        places.push(field_place.into());
                    }
                }
            }
            TyKind::Closure(_, substs) => {
                for (index, subst_ty) in substs.as_closure().upvar_tys().iter().enumerate() {
                    if Some(index) != without_field {
                        let field = FieldIdx::from_usize(index);
                        let field_place = repacker.tcx.mk_place_field(
                            self.to_rust_place(repacker),
                            field,
                            subst_ty,
                        );
                        places.push(field_place.into());
                    }
                }
            }
            TyKind::Generator(_, substs, _) => {
                for (index, subst_ty) in substs.as_generator().upvar_tys().iter().enumerate() {
                    if Some(index) != without_field {
                        let field = FieldIdx::from_usize(index);
                        let field_place = repacker.tcx.mk_place_field(
                            self.to_rust_place(repacker),
                            field,
                            subst_ty,
                        );
                        places.push(field_place.into());
                    }
                }
            }
            ty => unreachable!("ty={:?}", ty),
        }
        places
    }

    // /// Pop the last projection from the place and return the new place with the popped element.
    // pub fn pop_one_level(self, place: Place<'tcx>) -> (PlaceElem<'tcx>, Place<'tcx>) {
    //     assert!(place.projection.len() > 0);
    //     let last_index = place.projection.len() - 1;
    //     let projection = self.tcx.intern_place_elems(&place.projection[..last_index]);
    //     (
    //         place.projection[last_index],
    //         Place::new(place.local, projection),
    //     )
    // }
}

// impl<'tcx> RootPlace<'tcx> {
//     pub fn get_parent(self, repacker: PlaceRepacker<'_, 'tcx>) -> Place<'tcx> {
//         assert!(self.projection.len() > 0);
//         let idx = self.projection.len() - 1;
//         let projection = repacker.tcx.intern_place_elems(&self.projection[..idx]);
//         Place::new(self.local, projection)
//     }
// }

impl<'tcx> Place<'tcx> {
    pub fn ty(self, repacker: PlaceRepacker<'_, 'tcx>) -> PlaceTy<'tcx> {
        (*self).ty(repacker.mir, repacker.tcx)
    }
    // pub fn get_root(self, repacker: PlaceRepacker<'_, 'tcx>) -> RootPlace<'tcx> {
    //     if let Some(idx) = self.projection.iter().rev().position(RootPlace::is_indirect) {
    //         let idx = self.projection.len() - idx;
    //         let projection = repacker.tcx.intern_place_elems(&self.projection[..idx]);
    //         let new = Self::new(self.local, projection);
    //         RootPlace::new(new)
    //     } else {
    //         RootPlace::new(self.local.into())
    //     }
    // }

    /// Should only be called on a `Place` obtained from `RootPlace::get_parent`.
    pub fn get_ref_mutability(self, repacker: PlaceRepacker<'_, 'tcx>) -> Mutability {
        let typ = self.ty(repacker);
        if let TyKind::Ref(_, _, mutability) = typ.ty.kind() {
            *mutability
        } else {
            unreachable!("get_ref_mutability called on non-ref type: {:?}", typ.ty);
        }
    }

    /// Returns all `TyKind::Ref` and `TyKind::RawPtr` that `self` projects through.
    /// The `Option` acts as an either where `TyKind::RawPtr` corresponds to a `None`.
    #[tracing::instrument(name = "Place::projection_refs", level = "trace", skip(repacker))]
    pub fn projection_refs(
        self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> impl Iterator<Item = Option<(Region<'tcx>, Ty<'tcx>, Mutability)>> {
        self.projection_tys(repacker).filter_map(|(ty, _)| match ty.ty.kind() {
            &TyKind::Ref(r, ty, m) => Some(Some((r, ty, m))),
            &TyKind::RawPtr(_) => Some(None),
            _ => None,
        })
    }

    pub fn projects_shared_ref(self, repacker: PlaceRepacker<'_, 'tcx>) -> bool {
        self.projects_ty(
            |typ| {
                typ.ty
                    .ref_mutability()
                    .map(|m| m.is_not())
                    .unwrap_or_default()
            },
            repacker,
        )
        .is_some()
    }

    #[tracing::instrument(name = "Place::projects_ptr", level = "trace", skip(repacker), ret)]
    pub fn projects_ptr(self, repacker: PlaceRepacker<'_, 'tcx>) -> Option<Place<'tcx>> {
        self.projects_ty(
            |typ| typ.ty.is_ref() || typ.ty.is_box() || typ.ty.is_unsafe_ptr(),
            repacker,
        )
    }

    pub fn can_deinit(self, repacker: PlaceRepacker<'_, 'tcx>) -> bool {
        let mut projects_shared_ref = false;
        self.projects_ty(
            |typ| {
                projects_shared_ref = projects_shared_ref
                    || typ
                        .ty
                        .ref_mutability()
                        .map(|m| m.is_not())
                        .unwrap_or_default();
                projects_shared_ref = projects_shared_ref && !typ.ty.is_unsafe_ptr();
                false
            },
            repacker,
        );
        !projects_shared_ref
    }

    pub fn projects_ty(
        self,
        mut predicate: impl FnMut(PlaceTy<'tcx>) -> bool,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Option<Place<'tcx>> {
        // TODO: remove
        let old_result = (|| {
            let mut typ = PlaceTy::from_ty(repacker.mir.local_decls()[self.local].ty);
            for (idx, elem) in self.projection.iter().enumerate() {
                if predicate(typ) {
                    let projection = repacker.tcx.mk_place_elems(&self.projection[0..idx]);
                    return Some(Self::new(self.local, projection));
                }
                typ = typ.projection_ty(repacker.tcx, *elem);
            }
            None
        })();
        let new_result = self.projection_tys(repacker).find(|(typ, _)| predicate(*typ)).map(|(_, proj)| {
            let projection = repacker.tcx.mk_place_elems(proj);
            Self::new(self.local, projection)
        });
        assert_eq!(old_result, new_result);
        new_result
    }

    #[tracing::instrument(name = "Place::projection_tys", level = "trace", skip(repacker), ret)]
    pub fn projection_tys(
        self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> impl Iterator<Item = (PlaceTy<'tcx>, &'tcx [PlaceElem<'tcx>])> {
        let mut typ = PlaceTy::from_ty(repacker.mir.local_decls()[self.local].ty);
        self.projection.iter().enumerate().map(move |(idx, elem)| {
            let ret = (typ, &self.projection[0..idx]);
            typ = typ.projection_ty(repacker.tcx, *elem);
            ret
        })
    }

    pub fn all_behind_region(self, r: RegionVid, repacker: PlaceRepacker<'_, 'tcx>) -> Vec<Self> {
        struct AllBehindWalker<'tcx>(Place<'tcx>, Vec<Place<'tcx>>, TyCtxt<'tcx>);
        impl<'tcx> DeepTypeVisitor<'tcx> for AllBehindWalker<'tcx> {
            fn tcx(&self) -> TyCtxt<'tcx> {
                self.2
            }

            fn visit_rec(&mut self, ty: Ty<'tcx>, stack: &mut Stack<'tcx>) {
                ty.visit_with(self, stack);
            }
        }
        todo!()
    }

    pub fn mk_deref(self, repacker: PlaceRepacker<'_, 'tcx>) -> Self {
        self.mk_place_elem(PlaceElem::Deref, repacker)
    }

    pub fn mk_place_elem(self, elem: PlaceElem<'tcx>, repacker: PlaceRepacker<'_, 'tcx>) -> Self {
        let elems = repacker.tcx.mk_place_elems_from_iter(
            self.projection
                .iter()
                .copied()
                .chain([elem]),
        );
        Self::new(self.local, elems)
    }

    pub fn deref_to_region(
        mut self,
        r: RegionVid,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Option<Self> {
        let mut ty = self.ty(repacker).ty;
        while let TyKind::Ref(rr, inner_ty, _) = *ty.kind() {
            ty = inner_ty;
            self = self.mk_deref(repacker);
            if rr.is_var() && rr.as_var() == r {
                return Some(self);
            }
        }
        None
    }

    pub fn param_kind(self, repacker: PlaceRepacker<'_, 'tcx>) -> Option<Local> {
        if self.local.as_usize() <= repacker.mir.arg_count {
            Some(self.local)
        } else {
            None
        }
    }
}
