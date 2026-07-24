// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! Various helper functions for working with `mir::Place`.

use prusti_rustc_interface::{
    hir,
    middle::{mir, ty::TyCtxt},
    span::Span,
};
use std::borrow::Borrow;

/// Check if the place `potential_prefix` is a prefix of `place`. For example:
///
/// +   `is_prefix(x.f, x.f) == true`
/// +   `is_prefix(x.f.g, x.f) == true`
/// +   `is_prefix(x.f, x.f.g) == false`
pub fn is_prefix<'tcx>(place: mir::Place<'tcx>, potential_prefix: mir::Place<'tcx>) -> bool {
    if place.local != potential_prefix.local
        || place.projection.len() < potential_prefix.projection.len()
    {
        false
    } else {
        place
            .projection
            .iter()
            .zip(potential_prefix.projection.iter())
            .all(|(e1, e2)| e1 == e2)
    }
}

/// Pop the last projection from the place and return the new place with the popped element.
pub fn try_pop_one_level<'tcx>(
    tcx: TyCtxt<'tcx>,
    place: mir::Place<'tcx>,
) -> Option<(mir::PlaceElem<'tcx>, mir::Place<'tcx>)> {
    if !place.projection.is_empty() {
        let last_index = place.projection.len() - 1;
        let new_place = mir::Place {
            local: place.local,
            projection: tcx.mk_place_elems(&place.projection[..last_index]),
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
#[derive(Debug)]
pub struct VecPlaceComponent<'tcx> {
    place: mir::Place<'tcx>,
}

impl<'tcx> VecPlaceComponent<'tcx> {
    pub fn get_mir_place(&self) -> mir::Place<'tcx> {
        self.place
    }
}

/// A different way to represent a place that is more similar to the one
/// mentioned in the issue <https://github.com/rust-lang/rust/issues/52708>.
#[derive(Debug)]
pub struct VecPlace<'tcx> {
    components: Vec<VecPlaceComponent<'tcx>>,
}

impl<'tcx> VecPlace<'tcx> {
    pub fn iter<'a>(&'a self) -> impl DoubleEndedIterator<Item = &'a VecPlaceComponent<'tcx>> {
        self.components.iter()
    }
    pub fn component_count(&self) -> usize {
        self.components.len()
    }
}

/// Returns an iterator over all Prusti attributes (i.e. `prusti::<attr_name>="...")`.
fn get_prusti_attrs<T: Borrow<hir::Attribute>>(
    attrs: &[T],
) -> impl Iterator<Item = &hir::AttrItem> {
    attrs.iter().filter_map(|attr| match attr.borrow() {
        hir::Attribute::Unparsed(item)
            if item.path.segments.len() == 2 && item.path.segments[0].as_str() == "prusti" =>
        {
            Some(&**item)
        }
        _ => None,
    })
}

fn get_prusti_attr<'a, T: Borrow<hir::Attribute>>(
    attrs: &'a [T],
    attr_name: &str,
) -> Option<&'a hir::AttrItem> {
    get_prusti_attrs(attrs).find(|item| item.path.segments[1].as_str() == attr_name)
}

/// Check if `prusti::<name>` is among the attributes.
/// Any arguments of the attribute are ignored.
pub fn has_prusti_attr(attrs: &[hir::Attribute], name: &str) -> bool {
    get_prusti_attr(attrs, name).is_some()
}

/// The span of the `prusti::<name>` marker among `attrs`, if present.
pub fn prusti_attr_span(attrs: &[hir::Attribute], name: &str) -> Option<Span> {
    get_prusti_attr(attrs, name).map(|item| item.span)
}

/// The spans of the user's Prusti annotations among `attrs`: every
/// `prusti::<name>` marker except the per-item version marker. Each marker is
/// emitted at its own annotation's span, so these point at the individual
/// attributes rather than the whole item.
pub fn prusti_annotation_spans(attrs: &[hir::Attribute]) -> impl Iterator<Item = Span> + '_ {
    get_prusti_attrs(attrs)
        .filter(|item| item.path.segments[1].as_str() != "specs_version")
        .map(|item| item.span)
}

/// Check if `prusti::spec_only` is among the attributes.
pub fn has_spec_only_attr(attrs: &[hir::Attribute]) -> bool {
    has_prusti_attr(attrs, "spec_only")
}

/// Check if `prusti::extern_spec` is among the attributes.
pub fn has_extern_spec_attr(attrs: &[hir::Attribute]) -> bool {
    has_prusti_attr(attrs, "extern_spec")
}

pub fn read_extern_spec_attr(attrs: &[hir::Attribute]) -> Option<String> {
    read_prusti_attr("extern_spec", attrs)
}

pub fn read_specs_version_attr(attr: &hir::Attribute) -> Option<String> {
    read_prusti_attr("specs_version", &[attr])
}

pub fn has_to_model_fn_attr(attrs: &[hir::Attribute]) -> bool {
    has_prusti_attr(attrs, "type_models_to_model_fn")
}

pub fn has_to_model_impl_attr(attrs: &[hir::Attribute]) -> bool {
    has_prusti_attr(attrs, "type_models_to_model_impl")
}

pub fn has_trait_bounds_type_cond_spec(attrs: &[hir::Attribute]) -> bool {
    has_prusti_attr(attrs, "type_cond_spec_trait_bounds_in_where_clause")
}

pub fn has_abstract_predicate_attr(attrs: &[hir::Attribute]) -> bool {
    has_prusti_attr(attrs, "abstract_predicate")
}

/// Read the value stored in a Prusti attribute (e.g. `prusti::<attr_name>="...")`.
pub fn read_prusti_attrs<'a, T: Borrow<hir::Attribute>>(
    attr_name: &'a str,
    attrs: &'a [T],
) -> impl Iterator<Item = String> + 'a {
    get_prusti_attrs(attrs)
        .filter(move |item| item.path.segments[1].as_str() == attr_name)
        .filter_map(|item| match &item.args {
            hir::AttrArgs::Eq { expr, .. } => {
                Some(expr.as_token_lit().symbol.as_str().replace("\\\"", "\""))
            }
            _ => None,
        })
}

/// Read the value stored in a single Prusti attribute (e.g. `prusti::<attr_name>="...")`.
pub fn read_prusti_attr<T: Borrow<hir::Attribute>>(attr_name: &str, attrs: &[T]) -> Option<String> {
    read_prusti_attrs(attr_name, attrs).next()
}
