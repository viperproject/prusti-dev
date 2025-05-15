// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! Various helper functions for working with `mir::Place`.

use prusti_rustc_interface::{
    ast::ast,
    middle::{mir, ty::TyCtxt},
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
    if place.projection.len() > 0 {
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

/// Check if `prusti::<name>` is among the attributes.
/// Any arguments of the attribute are ignored.
pub fn has_prusti_attr(attrs: &[ast::Attribute], name: &str) -> bool {
    attrs.iter().any(|attr| match &attr.kind {
        ast::AttrKind::Normal(normal_attr) => {
            let ast::AttrItem {
                unsafety: _,
                path:
                    ast::Path {
                        span: _,
                        segments,
                        tokens: _,
                    },
                args: _,
                tokens: _,
            } = &normal_attr.item;
            segments.len() == 2
                && segments[0].ident.as_str() == "prusti"
                && segments[1].ident.as_str() == name
        }
        _ => false,
    })
}

/// Check if `prusti::spec_only` is among the attributes.
pub fn has_spec_only_attr(attrs: &[ast::Attribute]) -> bool {
    has_prusti_attr(attrs, "spec_only")
}

/// Check if `prusti::extern_spec` is among the attributes.
pub fn has_extern_spec_attr(attrs: &[ast::Attribute]) -> bool {
    has_prusti_attr(attrs, "extern_spec")
}

pub fn read_extern_spec_attr(attrs: &[ast::Attribute]) -> Option<String> {
    read_prusti_attr("extern_spec", attrs)
}

pub fn read_specs_version_attr(attr: &ast::Attribute) -> Option<String> {
    read_prusti_attr("specs_version", &[attr])
}

pub fn has_to_model_fn_attr(attrs: &[ast::Attribute]) -> bool {
    has_prusti_attr(attrs, "type_models_to_model_fn")
}

pub fn has_to_model_impl_attr(attrs: &[ast::Attribute]) -> bool {
    has_prusti_attr(attrs, "type_models_to_model_impl")
}

pub fn has_trait_bounds_type_cond_spec(attrs: &[ast::Attribute]) -> bool {
    has_prusti_attr(attrs, "type_cond_spec_trait_bounds_in_where_clause")
}

pub fn has_abstract_predicate_attr(attrs: &[ast::Attribute]) -> bool {
    has_prusti_attr(attrs, "abstract_predicate")
}

/// Read the value stored in a Prusti attribute (e.g. `prusti::<attr_name>="...")`.
pub fn read_prusti_attrs<T: Borrow<ast::Attribute>>(attr_name: &str, attrs: &[T]) -> Vec<String> {
    let mut strings = vec![];
    for attr in attrs {
        if let ast::AttrKind::Normal(normal_attr) = &attr.borrow().kind {
            if let ast::AttrItem {
                unsafety: _,
                path:
                    ast::Path {
                        span: _,
                        segments,
                        tokens: _,
                    },
                args:
                    ast::AttrArgs::Eq {
                        value: ast::AttrArgsEq::Hir(token_lit),
                        eq_span: _,
                    },
                tokens: _,
            } = &normal_attr.item
            {
                // Skip attributes whose path don't match with "prusti::<attr_name>"
                if !(segments.len() == 2
                    && segments[0].ident.as_str() == "prusti"
                    && segments[1].ident.as_str() == attr_name)
                {
                    continue;
                }
                fn extract_string(token: &prusti_rustc_interface::ast::token::Lit) -> String {
                    token.symbol.as_str().replace("\\\"", "\"")
                }
                strings.push(extract_string(&token_lit.as_token_lit()));
            }
        };
    }
    strings
}

/// Read the value stored in a single Prusti attribute (e.g. `prusti::<attr_name>="...")`.
pub fn read_prusti_attr<T: Borrow<ast::Attribute>>(attr_name: &str, attrs: &[T]) -> Option<String> {
    read_prusti_attrs(attr_name, attrs).pop()
}
