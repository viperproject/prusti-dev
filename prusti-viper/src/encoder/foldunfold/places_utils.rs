// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use encoder::vir;
use std::collections::HashSet;

/// Returns the elements of A1 or A2 that have a prefix in the other set.
///
/// e.g.
/// filter_with_prefix_in_other(
///   { a, b.c, d.e.f, d.g },
///   { a, b.c.d, b.c.e, d.e,h }
/// ) = { a, b.c.d, b.c.e, d.e.f }
pub fn filter_with_prefix_in_other(left: &HashSet<vir::Place>, right: &HashSet<vir::Place>) -> HashSet<vir::Place> {
    let mut res = HashSet::new();
    for left_item in left.iter() {
        for right_item in right.iter() {
            if right_item.has_prefix(left_item) {
                res.insert(right_item.clone());
            }
            if left_item.has_prefix(right_item) {
                res.insert(left_item.clone());
            }
        }
    }
    res
}

/// Returns the elements of A1 that are a prefix of at least one element in A2.
///
/// e.g.
/// filter_prefixes_of(
///   { a, b.c, d.e.f, d.g },
///   { a, b.c.d, b.c.e, d.e,h }
/// ) = { a, b.c }
pub fn filter_prefixes_of(left: &HashSet<vir::Place>, right: &HashSet<vir::Place>) -> HashSet<vir::Place> {
    let mut res = HashSet::new();
    for left_item in left.iter() {
        for right_item in right.iter() {
            if right_item.has_prefix(left_item) {
                res.insert(left_item.clone());
            }
        }
    }
    res
}

/// Returns the elements of A1 that are a proper prefix of at least one element in A2.
///
/// e.g.
/// filter_proper_prefixes_of(
///   { a, b.c, d.e.f, d.g },
///   { a, b.c.d, b.c.e, d.e,h }
/// ) = { b.c }
pub fn filter_proper_prefixes_of(left: &HashSet<vir::Place>, right: &HashSet<vir::Place>) -> HashSet<vir::Place> {
    let mut res = HashSet::new();
    for left_item in left.iter() {
        for right_item in right.iter() {
            if right_item.has_prefix(left_item) {
                res.insert(left_item.clone());
            }
        }
    }
    res
}

/// Returns the elements of A1 that are an extension of at least one element in A2.
///
/// e.g.
/// filter_extensions_of(
///   { a, b.c.d, b.c.e, d.e,h },
///   { a, b.c, d.e.f, d.g }
/// ) = { a, b.c.d, b.c.e }
pub fn filter_extensions_of(left: &HashSet<vir::Place>, right: &HashSet<vir::Place>) -> HashSet<vir::Place> {
    let mut res = HashSet::new();
    for left_item in left.iter() {
        for right_item in right.iter() {
            if left_item.has_prefix(right_item) {
                res.insert(left_item.clone());
            }
        }
    }
    res
}

/// Returns the elements of A1 that are a proper extension of at least one element in A2.
///
/// e.g.
/// filter_proper_extensions_of(
///   { a, b.c.d, b.c.e, d.e,h },
///   { a, b.c, d.e.f, d.g }
/// ) = { b.c.d, b.c.e }
pub fn filter_proper_extensions_of(left: &HashSet<vir::Place>, right: &HashSet<vir::Place>) -> HashSet<vir::Place> {
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

/// Returns the elements of A1 that are not a proper prefix of some elements in A2.
///
/// e.g.
/// filter_not_proper_prefix_of(
///   { a, b.c.d, b.c.e, d.e },
///   { a, b.c, d.e.f, d.g }
/// ) = { a, b.c.d }
pub fn filter_not_proper_prefix_of(left: &HashSet<vir::Place>, right: &HashSet<vir::Place>) -> HashSet<vir::Place> {
    let mut res = HashSet::new();
    for left_item in left.iter() {
        let mut keep: bool = true;
        for right_item in right.iter() {
            if right_item.has_proper_prefix(left_item) {
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

/// Returns the elements of A1 that are not a proper extension of some elements in A2.
///
/// e.g.
/// filter_not_proper_extensions_of(
///   { a, b.c.d, b.c.e, d.e },
///   { a, b.c, d.e.f, d.g }
/// ) = { a, d.e }
pub fn filter_not_proper_extensions_of(left: &HashSet<vir::Place>, right: &HashSet<vir::Place>) -> HashSet<vir::Place> {
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

/// Returns the common ancestors of A1 and A2.
///
/// e.g.
/// common_ancestors(
///   { a, b.c, d.e.g, d.g }
///   { a, b.c.d, b.c.e, d.e.f },
/// ) = { a, b.c, d }
pub fn common_ancestors(left: &HashSet<vir::Place>, right: &HashSet<vir::Place>) -> HashSet<vir::Place> {
    let mut intermediate = HashSet::new();
    for left_item in left.iter() {
        for candidate_ancestor in left_item.all_prefixes().into_iter().rev() {
            if right.iter().any(|right_item| right_item.has_prefix(candidate_ancestor)) {
                intermediate.insert(candidate_ancestor.clone());
                break;
            }
        }
    }
    let mut res = HashSet::new();
    // Filter paths that are an extension of some other path
    // This way, we avoid having both `d` and `d.g`
    for a in intermediate.iter() {
        let mut keep_a = true;
        for b in intermediate.iter() {
            if a.has_prefix(b) {
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

/// Returns the ancestors of A.
///
/// e.g.
/// ancestors(
///   { a, b.c, b.c.e, d.e.f },
/// ) = { a, b.c, d.e.f }
pub fn ancestors(initial: &HashSet<vir::Place>) -> HashSet<vir::Place> {
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

/// Returns the union of A1 and A2.
///
/// e.g.
/// union(
///   { a, b.c.d, b.c.e, d.e.f },
///   { a, b.c, d.e.g, d.g }
/// ) = { a, b.c, b.c.d, b.c.e, d.g, d.e.f, d.e.g }

pub fn union(left: &HashSet<vir::Place>, right: &HashSet<vir::Place>) -> HashSet<vir::Place> {
    left.clone().union(right).cloned().collect()
}
/// Returns the intersection of A1 and A2.
///
/// e.g.
/// intersection(
///   { a, b.c.d, b.c.e, d.e.f },
///   { a, b.c, d.e.g, d.g }
/// ) = { a }
pub fn intersection(left: &HashSet<vir::Place>, right: &HashSet<vir::Place>) -> HashSet<vir::Place> {
    left.clone().intersection(right).cloned().collect()
}
