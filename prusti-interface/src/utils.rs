// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! Various helper functions for working with `mir::Place`.

use rustc_middle::mir;
use rustc_middle::ty::{self, TyCtxt};
use rustc_index::vec::Idx;
use std::collections::HashSet;
use rustc_ast::ast;
use log::trace;

/// Check if the place `potential_prefix` is a prefix of `place`. For example:
///
/// +   `is_prefix(x.f, x.f) == true`
/// +   `is_prefix(x.f.g, x.f) == true`
/// +   `is_prefix(x.f, x.f.g) == false`
pub fn is_prefix(place: &mir::Place, potential_prefix: &mir::Place) -> bool {
    if place.local != potential_prefix.local || place.projection.len() < potential_prefix.projection.len() {
        false
    } else {
        place.projection.iter().zip(potential_prefix.projection.iter()).all(|(e1, e2)| e1 == e2)
    }
}

/// Expands a place `x.f.g` of type struct into a vector of places for
/// each of the struct's fields `{x.f.g.f, x.f.g.g, x.f.g.h}`. If
/// `without_field` is not `None`, then omits that field from the final
/// vector.
pub fn expand_struct_place<'a, 'tcx: 'a>(
    place: &mir::Place<'tcx>,
    mir: &mir::Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    without_field: Option<usize>,
) -> Vec<mir::Place<'tcx>> {
    let mut places = Vec::new();
    let typ = place.ty(mir, tcx);
    if typ.variant_index.is_some() {
        unimplemented!("We do not support downcast yet.");
    }
    match typ.ty.kind {
        ty::Adt(def, substs) => {
            assert!(
                def.is_struct(),
                "Only structs can be expanded. Got def={:?}.",
                def
            );
            let variant = def.non_enum_variant();
            for (index, field_def) in variant.fields.iter().enumerate() {
                if Some(index) != without_field {
                    let field = mir::Field::new(index);
                    let field_place = tcx.mk_place_field(*place, field, field_def.ty(tcx, substs));
                    places.push(field_place);
                }
            }
        }
        ty::Tuple(slice) => {
            for (index, arg) in slice.iter().enumerate() {
                if Some(index) != without_field {
                    let field = mir::Field::new(index);
                    let field_place = tcx.mk_place_field(*place, field, arg.expect_ty());
                    places.push(field_place);
                }
            }
        },
        ty::Ref(_region, _ty, _) => match without_field {
            Some(without_field) => {
                assert_eq!(
                    without_field, 0,
                    "References have only a single “field”."
                );
            }
            None => {
                places.push(tcx.mk_place_deref(*place));
            }
        },
        ref ty => {
            unimplemented!("ty={:?}", ty);
        }
    }
    places
}

/// Expand `current_place` one level down by following the `guide_place`.
/// Returns the new `current_place` and a vector containing other places that
/// could have resulted from the expansion.
pub fn expand_one_level<'tcx>(
    mir: &mir::Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    current_place: mir::Place<'tcx>,
    guide_place: mir::Place<'tcx>,
) -> (mir::Place<'tcx>, Vec<mir::Place<'tcx>>) {
    let index = current_place.projection.len();
    match guide_place.projection[index] {
        mir::ProjectionElem::Field(projected_field, field_ty) => {
            let places =
                expand_struct_place(&current_place, mir, tcx, Some(projected_field.index()));
            let new_current_place = tcx.mk_place_field(current_place, projected_field, field_ty);
            (new_current_place, places)
        }
        mir::ProjectionElem::Downcast(_symbol, variant) => {
            let kind = &current_place.ty(mir, tcx).ty.kind;
            if let ty::TyKind::Adt(adt, _) = kind {
                (tcx.mk_place_downcast(current_place, adt, variant), Vec::new())
            } else {
                unreachable!();
            }
        }
        mir::ProjectionElem::Deref => {
            (tcx.mk_place_deref(current_place), Vec::new())
        }
        elem => {
            unimplemented!("elem = {:?}", elem);
        }
    }
}

/// Pop the last projection from the place and return the new place with the popped element.
pub fn try_pop_one_level<'tcx>(tcx: TyCtxt<'tcx>, place: mir::Place<'tcx>) -> Option<(mir::PlaceElem<'tcx>, mir::Place<'tcx>)> {
    if place.projection.len() > 0 {
        let last_index = place.projection.len()-1;
        let new_place = mir::Place {
            local: place.local,
            projection: tcx.intern_place_elems(&place.projection[..last_index]),
        };
        Some((place.projection[last_index], new_place))
    } else {
        None
    }
}

/// Pop the last element from the place if it is a dereference.
pub fn try_pop_deref<'tcx>(tcx: TyCtxt<'tcx>, place: mir::Place<'tcx>) -> Option<mir::Place<'tcx>> {
    try_pop_one_level(tcx, place).and_then(|(elem, base)| {
        if let mir::ProjectionElem::Deref = elem {
            Some(base)
        } else {
            None
        }
    })
}

/// Subtract the `subtrahend` place from the `minuend` place. The
/// subtraction is defined as set minus between `minuend` place replaced
/// with a set of places that are unrolled up to the same level as
/// `subtrahend` and the singleton `subtrahend` set. For example,
/// `subtract(x.f, x.f.g.h)` is performed by unrolling `x.f` into
/// `{x.g, x.h, x.f.f, x.f.h, x.f.g.f, x.f.g.g, x.f.g.h}` and
/// subtracting `{x.f.g.h}` from it, which results into `{x.g, x.h,
/// x.f.f, x.f.h, x.f.g.f, x.f.g.g}`.
pub fn expand<'a, 'tcx: 'a>(
    mir: &mir::Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    minuend: &mir::Place<'tcx>,
    subtrahend: &mir::Place<'tcx>,
) -> Vec<mir::Place<'tcx>> {
    assert!(
        is_prefix(subtrahend, minuend),
        "The minuend must be the prefix of the subtrahend."
    );
    trace!(
        "[enter] expand minuend={:?} subtrahend={:?}",
        minuend,
        subtrahend
    );
    let mut place_set = Vec::new();
    let mut minuend = *minuend;
    while minuend.projection.len() < subtrahend.projection.len() {
        let (new_minuend, places) = expand_one_level(mir, tcx, minuend, *subtrahend);
        minuend = new_minuend;
        place_set.extend(places);
    }
    trace!(
        "[exit] expand minuend={:?} subtrahend={:?} place_set={:?}",
        minuend,
        subtrahend,
        place_set
    );
    place_set
}

/// Try to collapse all places in `places` by following the
/// `guide_place`. This function is basically the reverse of
/// `expand_struct_place`.
pub fn collapse<'a, 'tcx: 'a>(
    mir: &mir::Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    places: &mut HashSet<mir::Place<'tcx>>,
    guide_place: &mir::Place<'tcx>,
) {
    let mut guide_place = guide_place.clone();
    fn recurse<'tcx>(
        mir: &mir::Body<'tcx>,
        tcx: TyCtxt<'tcx>,
        places: &mut HashSet<mir::Place<'tcx>>,
        current_place: mir::Place<'tcx>,
        guide_place: mir::Place<'tcx>,
    ) {
        if current_place == guide_place {
            return;
        } else {
            let (new_current_place, mut expansion) = expand_one_level(
                mir, tcx, current_place, guide_place);
            recurse(mir, tcx, places, new_current_place, guide_place);
            expansion.push(new_current_place);
            if expansion.iter().all(|place| places.contains(place)) {
                for place in expansion {
                    places.remove(&place);
                }
                places.insert(current_place);
            } else {
                return;
            }
        }
    }
    recurse(mir, tcx, places, guide_place.local.into(), guide_place);
}

#[derive(Debug)]
pub struct VecPlaceComponent<'tcx> {
    place: mir::Place<'tcx>,
}

impl<'tcx> VecPlaceComponent<'tcx> {
    pub fn get_mir_place(&self) -> &mir::Place<'tcx> {
        &self.place
    }
}

/// A different way to represent a place that is more similar to the one
/// mentioned in the issue https://github.com/rust-lang/rust/issues/52708.
#[derive(Debug)]
pub struct VecPlace<'tcx> {
    components: Vec<VecPlaceComponent<'tcx>>,
}

impl<'tcx> VecPlace<'tcx> {
    pub fn new(
        mir: &mir::Body<'tcx>,
        tcx: TyCtxt<'tcx>,
        place: &mir::Place<'tcx>
    ) -> VecPlace<'tcx> {
        let mut vec_place = Self {
            components: Vec::new(),
        };
        let mut prefix: mir::Place = place.local.into();
        vec_place.components.push(VecPlaceComponent { place: prefix });
        while prefix.projection.len() < place.projection.len() {
            let (new_prefix, _) = expand_one_level(mir, tcx, prefix, *place);
            prefix = new_prefix;
            vec_place.components.push(VecPlaceComponent { place: prefix });
        }
        vec_place
    }
    pub fn iter<'a>(&'a self) -> impl DoubleEndedIterator<Item = &'a VecPlaceComponent<'tcx>> {
        self.components.iter()
    }
    pub fn component_count(&self) -> usize {
        self.components.len()
    }
}

// pub fn get_attr_value(attr: &ast::Attribute) -> String {
//     use syntax::parse::token;
//     use syntax::tokenstream::TokenTree;

//     let trees: Vec<_> = attr.tokens.trees().collect();
//     assert_eq!(trees.len(), 2);

//     match trees[0] {
//         TokenTree::Token(_, ref token) => assert_eq!(*token, token::Token::Eq),
//         _ => unreachable!(),
//     };

//     match trees[1] {
//         TokenTree::Token(_, ref token) => match *token {
//             token::Token::Literal(ref lit, None) => match *lit {
//                 token::Lit::Str_(ref name) | token::Lit::StrRaw(ref name, _) => {
//                     name.as_str().to_string()
//                 }
//                 _ => unreachable!(),
//             },
//             _ => unreachable!(),
//         },
//         _ => unreachable!(),
//     }
// }
