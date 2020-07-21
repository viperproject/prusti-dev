// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! Various helper functions for working with `mir::Place`.

use rustc::mir;
use rustc::ty::{self, TyCtxt};
use rustc_data_structures::indexed_vec::Idx;
use std::collections::HashSet;
use syntax::ast;

/// Check if the place `potential_prefix` is a prefix of `place`. For example:
///
/// +   `is_prefix(x.f, x.f) == true`
/// +   `is_prefix(x.f.g, x.f) == true`
/// +   `is_prefix(x.f, x.f.g) == false`
pub fn is_prefix(place: &mir::Place, potential_prefix: &mir::Place) -> bool {
    if place == potential_prefix {
        true
    } else {
        match place {
            mir::Place::Local(_) | mir::Place::Static(_) => false,
            mir::Place::Projection(box mir::Projection { base, .. }) => {
                is_prefix(base, potential_prefix)
            }
        }
    }
}

/// Expands a place `x.f.g` of type struct into a vector of places for
/// each of the struct's fields `{x.f.g.f, x.f.g.g, x.f.g.h}`. If
/// `without_field` is not `None`, then omits that field from the final
/// vector.
pub fn expand_struct_place<'a, 'tcx: 'a>(
    place: &mir::Place<'tcx>,
    mir: &mir::Mir<'tcx>,
    tcx: TyCtxt<'a, 'tcx, 'tcx>,
    without_element: Option<usize>,
) -> Vec<mir::Place<'tcx>> {
    let mut places = Vec::new();
    match place.ty(mir, tcx) {
        mir::tcx::PlaceTy::Ty { ty: base_ty } => match base_ty.sty {
            ty::TyAdt(def, substs) => {
                assert!(
                    def.variants.len() == 1,
                    "Only structs can be expanded. Got def={:?}.",
                    def
                );
                for (index, field_def) in def.variants[0].fields.iter().enumerate() {
                    if Some(index) != without_element {
                        let field = mir::Field::new(index);
                        places.push(place.clone().field(field, field_def.ty(tcx, substs)));
                    }
                }
            }
            ty::TyTuple(slice) => {
                for (index, ty) in slice.iter().enumerate() {
                    if Some(index) != without_element {
                        let field = mir::Field::new(index);
                        places.push(place.clone().field(field, ty));
                    }
                }
            }
            ty::TyRef(_region, _ty, _) => match without_element {
                Some(without_element) => {
                    assert_eq!(without_element, 0, "References have only a single “field”.");
                }
                None => {
                    places.push(place.clone().deref());
                }
            },
            ref ty => {
                unimplemented!("ty={:?}", ty);
            }
        },
        mir::tcx::PlaceTy::Downcast { .. } => {}
    }
    places
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
    mir: &mir::Mir<'tcx>,
    tcx: TyCtxt<'a, 'tcx, 'tcx>,
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
    fn expand_recursively<'a, 'tcx: 'a>(
        place_set: &mut Vec<mir::Place<'tcx>>,
        mir: &mir::Mir<'tcx>,
        tcx: TyCtxt<'a, 'tcx, 'tcx>,
        minuend: &mir::Place<'tcx>,
        subtrahend: &mir::Place<'tcx>,
    ) {
        trace!(
            "[enter] expand_recursively minuend={:?} subtrahend={:?}",
            minuend,
            subtrahend
        );
        if minuend != subtrahend {
            match subtrahend {
                mir::Place::Projection(box mir::Projection { base, elem }) => {
                    // We just recurse until both paths become equal.
                    expand_recursively(place_set, mir, tcx, minuend, base);
                    match elem {
                        mir::ProjectionElem::Field(projected_field, _field_ty) => {
                            let places =
                                expand_struct_place(base, mir, tcx, Some(projected_field.index()));
                            place_set.extend(places);
                        }
                        mir::ProjectionElem::Downcast(_def, _variant) => {}
                        mir::ProjectionElem::Deref => {}
                        elem => {
                            unimplemented!("elem = {:?}", elem);
                        }
                    }
                }
                _ => unreachable!(),
            }
        }
    };
    expand_recursively(&mut place_set, mir, tcx, minuend, subtrahend);
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
    mir: &mir::Mir<'tcx>,
    tcx: TyCtxt<'a, 'tcx, 'tcx>,
    places: &mut HashSet<mir::Place<'tcx>>,
    guide_place: &mir::Place<'tcx>,
) {
    let mut guide_place = guide_place.clone();
    while let mir::Place::Projection(box mir::Projection { base, elem: _ }) = guide_place {
        let expansion = expand_struct_place(&base, mir, tcx, None);
        if expansion.iter().all(|place| places.contains(place)) {
            for place in expansion {
                places.remove(&place);
            }
            places.insert(base.clone());
        } else {
            return;
        }
        guide_place = base;
    }
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
    pub fn new(place: &mir::Place<'tcx>) -> VecPlace<'tcx> {
        let mut vec_place = Self {
            components: Vec::new(),
        };
        fn unroll_place<'tcx>(vec_place: &mut VecPlace<'tcx>, current: &mir::Place<'tcx>) {
            match current {
                mir::Place::Local(_) => {}
                mir::Place::Projection(box mir::Projection { base, .. }) => {
                    unroll_place(vec_place, base);
                }
                _ => unimplemented!(),
            }
            vec_place.components.push(VecPlaceComponent {
                place: current.clone(),
            });
        }
        unroll_place(&mut vec_place, place);
        vec_place
    }
    pub fn iter<'a>(&'a self) -> impl DoubleEndedIterator<Item = &'a VecPlaceComponent<'tcx>> {
        self.components.iter()
    }
    pub fn component_count(&self) -> usize {
        self.components.len()
    }
}

pub fn get_attr_value(attr: &ast::Attribute) -> String {
    use syntax::parse::token;
    use syntax::tokenstream::TokenTree;

    let trees: Vec<_> = attr.tokens.trees().collect();
    assert_eq!(trees.len(), 2);

    match trees[0] {
        TokenTree::Token(_, ref token) => assert_eq!(*token, token::Token::Eq),
        _ => unreachable!(),
    };

    match trees[1] {
        TokenTree::Token(_, ref token) => match *token {
            token::Token::Literal(ref lit, None) => match *lit {
                token::Lit::Str_(ref name) | token::Lit::StrRaw(ref name, _) => {
                    name.as_str().to_string()
                }
                _ => unreachable!(),
            },
            _ => unreachable!(),
        },
        _ => unreachable!(),
    }
}
