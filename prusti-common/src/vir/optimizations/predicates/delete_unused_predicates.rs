// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::vir::{
    ast::*,
    cfg,
    cfg::CfgMethod,
    utils::{walk_functions, walk_methods},
    CfgBlock,
};
use std::collections::{BTreeMap, BTreeSet};

fn get_used_predicates_in_methods_and_functions(
    methods: &[CfgMethod],
    functions: &[Function],
) -> BTreeSet<String> {
    let mut collector = UsedPredicateCollector::new();
    walk_methods(methods, &mut collector);
    walk_functions(functions, &mut collector);

    // DeadBorrowToken$ is a used predicate but it does not appear in VIR
    // becaue it is only created when viper code is created from VIR
    collector
        .used_predicates
        .insert("DeadBorrowToken$".to_string());
    collector.used_predicates
}

fn get_used_predicates_in_predicate_map(
    predicates: &[Predicate],
) -> BTreeMap<String, BTreeSet<String>> {
    let mut collector = UsedPredicateCollector::new();
    let mut map = BTreeMap::new();

    for pred in predicates {
        match pred {
            Predicate::Struct(StructPredicate {
                name,
                body: Some(e),
                ..
            }) => {
                ExprWalker::walk(&mut collector, e);
                let mut res = BTreeSet::new();
                std::mem::swap(&mut res, &mut collector.used_predicates);
                map.insert(name.clone(), res);
            }
            Predicate::Struct(StructPredicate { body: None, .. }) => { /* ignore */ }
            Predicate::Enum(p) => {
                ExprWalker::walk(&mut collector, &p.discriminant);
                ExprWalker::walk(&mut collector, &p.discriminant_bounds);

                for (e, _, sp) in &p.variants {
                    ExprWalker::walk(&mut collector, e);
                    collector.used_predicates.insert(sp.name.to_string());
                    sp.body
                        .iter()
                        .for_each(|e| ExprWalker::walk(&mut collector, e))
                }

                let mut res = BTreeSet::new();
                std::mem::swap(&mut res, &mut collector.used_predicates);
                map.insert(p.name.clone(), res);
            }
            Predicate::Bodyless(_, _) => { /* ignore */ }
        }
    }
    return map;
}

/// Return the set of the predicates in the predicate map that are accutally
/// reachable from the provided set of predicates
fn compute_reachable_predicates(
    predicates_in_predicates: &BTreeMap<String, BTreeSet<String>>,
    used_predicates: &BTreeSet<String>,
) -> BTreeSet<String> {
    let mut visited = BTreeSet::new();
    for to_visit in used_predicates {
        visit_used_pred(to_visit, predicates_in_predicates, &mut visited);
    }

    visited
}

fn visit_used_pred(
    to_visit: &str,
    predicates_in_predicates: &BTreeMap<String, BTreeSet<String>>,
    visited: &mut BTreeSet<String>,
) {
    if visited.contains(to_visit) {
        return;
    }

    visited.insert(to_visit.to_string());

    if let Some(v) = predicates_in_predicates.get(to_visit) {
        for p in v {
            visit_used_pred(p, predicates_in_predicates, visited)
        }
    }
}

fn compute_used_predicates(
    methods: &[CfgMethod],
    functions: &[Function],
    predicates: &[Predicate],
) -> BTreeSet<String> {
    let used_preds_in_methods_and_functions =
        get_used_predicates_in_methods_and_functions(methods, functions);

    debug!(
        "The used predicates in functions and methods are {:?}",
        &used_preds_in_methods_and_functions
    );

    let predicates_in_predicates_map = get_used_predicates_in_predicate_map(predicates);

    debug!(
        "Map of predicates used in predicates {:?}",
        &predicates_in_predicates_map
    );

    let mut reachable_predicates_in_predicates = compute_reachable_predicates(
        &predicates_in_predicates_map,
        &used_preds_in_methods_and_functions,
    );

    reachable_predicates_in_predicates.extend(used_preds_in_methods_and_functions.iter().cloned());

    debug!(
        "All the used predicates are {:?}",
        &reachable_predicates_in_predicates
    );
    reachable_predicates_in_predicates
}

pub fn delete_unused_predicates(
    methods: &[CfgMethod],
    functions: &[Function],
    mut predicates: Vec<Predicate>,
) -> Vec<Predicate> {
    let mut has_changed = true;

    let used_predicates = compute_used_predicates(methods, functions, &predicates);
    predicates.retain(|p| used_predicates.contains(p.name()));

    predicates
}

struct UsedPredicateCollector {
    used_predicates: BTreeSet<String>,
}

impl UsedPredicateCollector {
    fn new() -> Self {
        UsedPredicateCollector {
            used_predicates: BTreeSet::new(),
        }
    }
}

impl ExprWalker for UsedPredicateCollector {
    fn walk_predicate_access_predicate(
        &mut self,
        name: &str,
        arg: &Expr,
        _perm_amount: PermAmount,
        _pos: &Position,
    ) {
        self.used_predicates.insert(name.to_string());
        ExprWalker::walk(self, arg);
    }

    fn walk_unfolding(
        &mut self,
        name: &str,
        args: &Vec<Expr>,
        body: &Expr,
        _perm: PermAmount,
        _variant: &MaybeEnumVariantIndex,
        _pos: &Position,
    ) {
        self.used_predicates.insert(name.to_string());
        for arg in args {
            ExprWalker::walk(self, arg);
        }
        ExprWalker::walk(self, body);
    }
}

impl StmtWalker for UsedPredicateCollector {
    fn walk_expr(&mut self, expr: &Expr) {
        ExprWalker::walk(self, expr);
    }
    fn walk_fold(
        &mut self,
        predicate_name: &str,
        args: &Vec<Expr>,
        _perm: &PermAmount,
        _variant: &MaybeEnumVariantIndex,
        _pos: &Position,
    ) {
        self.used_predicates.insert(predicate_name.to_string());
    }

    fn walk_unfold(
        &mut self,
        predicate_name: &str,
        args: &Vec<Expr>,
        _perm: &PermAmount,
        _variant: &MaybeEnumVariantIndex,
    ) {
        self.used_predicates.insert(predicate_name.to_string());
    }
}
