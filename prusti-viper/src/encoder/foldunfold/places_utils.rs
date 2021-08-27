// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use vir_crate::polymorphic as vir;
use std::collections::HashSet;
use std::hash::Hash;

/// Returns the elements of A1 that are a proper extension of at least one element in A2.
///
/// e.g.
/// filter_proper_extensions_of(
///   { a, b.c.d, b.c.e, d.e,h },
///   { a, b.c, d.e.f, d.g }
/// ) = { b.c.d, b.c.e }
pub fn filter_proper_extensions_of(
    left: &HashSet<vir::Expr>,
    right: &HashSet<vir::Expr>,
) -> HashSet<vir::Expr> {
    let mut res = HashSet::new();
    for left_item in left.iter() {
        for right_item in right.iter() {
            if left_item.has_proper_prefix(right_item) {
                res.insert(left_item.clone());
                break;
            }
        }
    }
    res
}

/// Returns the elements of A1 that are not a proper extension of some elements in A2.
///
/// e.g.
/// filter_not_proper_extensions_of(
///   { a, b.c.d, b.c.e, d.e },
///   { a, b.c, d.e.f, d.g }
/// ) = { a, d.e }
pub fn filter_not_proper_extensions_of(
    left: &HashSet<vir::Expr>,
    right: &HashSet<vir::Expr>,
) -> HashSet<vir::Expr> {
    let mut res = HashSet::new();
    for left_item in left.iter() {
        let mut keep: bool = true;
        for right_item in right.iter() {
            if left_item.has_proper_prefix(right_item) {
                keep = false;
                break;
            }
        }
        if keep {
            res.insert(left_item.clone());
        }
    }
    res
}

/// Returns the ancestors of A.
///
/// e.g.
/// ancestors(
///   { a, b.c, b.c.e, d.e.f },
/// ) = { a, b.c, d.e.f }
pub fn ancestors(initial: &HashSet<vir::Expr>) -> HashSet<vir::Expr> {
    let mut res = HashSet::new();
    // Filter paths that are an extension of some other path
    // This way, we avoid having both `d` and `d.g`
    for a in initial.iter() {
        let mut keep_a = true;
        for b in initial.iter() {
            if a.has_proper_prefix(b) {
                keep_a = false;
                break;
            }
        }
        if keep_a {
            res.insert(a.clone());
        }
    }
    res
}

/// Returns the union of two sets
pub fn union<T: Eq + Hash + Clone>(left: &HashSet<T>, right: &HashSet<T>) -> HashSet<T> {
    left.clone().union(right).cloned().collect()
}

/// Returns the union of three sets
pub fn union3<T: Eq + Hash + Clone>(
    left: &HashSet<T>,
    mid: &HashSet<T>,
    right: &HashSet<T>,
) -> HashSet<T> {
    left.clone()
        .union(mid)
        .cloned()
        .collect::<HashSet<T>>()
        .union(right)
        .cloned()
        .collect()
}

/// Returns the intersection of two sets
pub fn intersection<T: Eq + Hash + Clone>(left: &HashSet<T>, right: &HashSet<T>) -> HashSet<T> {
    left.clone().intersection(right).cloned().collect()
}
