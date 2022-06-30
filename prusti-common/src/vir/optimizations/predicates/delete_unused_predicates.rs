// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::vir::polymorphic_vir::{
    ast::*,
    cfg::CfgMethod,
    utils::{walk_functions, walk_methods},
};
use log::debug;
use std::collections::{HashMap, HashSet};

fn collect_info_from_methods_and_functions(
    methods: &[CfgMethod],
    functions: &[Function],
) -> UsedPredicateCollector {
    let mut collector = UsedPredicateCollector::new();
    walk_methods(methods, &mut collector);
    walk_functions(functions, &mut collector);

    // DeadBorrowToken$ is a used predicate but it does not appear in VIR
    // becaue it is only created when viper code is created from VIR
    collector
        .used_predicates
        .insert(Type::typed_ref("DeadBorrowToken$"));
    collector
}

/// Computes a map of Predicate to the predicates used  in that predicate
fn get_used_predicates_in_predicate_map(predicates: &[Predicate]) -> HashMap<Type, HashSet<Type>> {
    let mut collector = UsedPredicateCollector::new();
    let mut map = HashMap::new();

    for pred in predicates {
        match pred {
            Predicate::Struct(StructPredicate {
                typ, body: Some(e), ..
            }) => {
                ExprWalker::walk(&mut collector, e);
                let mut res = HashSet::new();
                std::mem::swap(&mut res, &mut collector.used_predicates);
                map.insert(typ.clone(), res);
            }
            Predicate::Struct(StructPredicate { body: None, .. }) => { /* ignore */ }
            Predicate::Enum(p) => {
                let discriminant_loc =
                    Expr::from(p.this.clone()).field(p.discriminant_field.clone());
                ExprWalker::walk(&mut collector, &discriminant_loc);
                ExprWalker::walk(&mut collector, &p.discriminant_bounds);

                for (e, _, sp) in &p.variants {
                    ExprWalker::walk(&mut collector, e);
                    collector.used_predicates.insert(sp.typ.clone());
                    sp.body
                        .iter()
                        .for_each(|e| ExprWalker::walk(&mut collector, e))
                }

                let mut res = HashSet::new();
                std::mem::swap(&mut res, &mut collector.used_predicates);
                map.insert(p.typ.clone(), res);
            }
            Predicate::Bodyless(_, _) => { /* ignore */ }
        }
    }
    map
}

/// Return the set of the predicates in the predicate map that are actually
/// reachable from the provided set of predicates
fn compute_reachable_predicates(
    predicates_in_predicates: &HashMap<Type, HashSet<Type>>,
    used_predicates: &HashSet<Type>,
) -> HashSet<Type> {
    let mut visited = HashSet::new();
    for to_visit in used_predicates {
        visit_predicate(to_visit, predicates_in_predicates, &mut visited);
    }

    visited
}

/// Function used by compute_reachable_predicates to visit all the predicates
fn visit_predicate(
    to_visit: &Type,
    predicates_in_predicates: &HashMap<Type, HashSet<Type>>,
    visited: &mut HashSet<Type>,
) {
    if visited.contains(to_visit) {
        return;
    }

    visited.insert(to_visit.clone());

    if let Some(v) = predicates_in_predicates.get(to_visit) {
        for p in v {
            visit_predicate(p, predicates_in_predicates, visited)
        }
    }
}

/// Delete all unused predicates and eliminate bodies of predicates that are never folded or unfolded
pub fn delete_unused_predicates(
    methods: &[CfgMethod],
    functions: &[Function],
    mut predicates: Vec<Predicate>,
) -> Vec<Predicate> {
    let collector = collect_info_from_methods_and_functions(methods, functions);
    let used_predicates_in_functions_and_methods = collector.used_predicates;
    let folded_predicates = collector.folded_predicates;
    let mut predicates_in_predicates_map = get_used_predicates_in_predicate_map(&predicates);

    debug!(
        "The used predicates in functions and methods are {:?}",
        &used_predicates_in_functions_and_methods
    );

    // Remove the bodies of predicats that are never folded or unfolded
    predicates.iter_mut().for_each(|predicate| {
        let predicate_type = &predicate.get_type().clone();
        if !folded_predicates.contains(predicate_type) {
            if let Predicate::Struct(sp) = predicate {
                debug!("Removed body of {}", predicate_type);
                sp.body = None;

                // since the predicate now has no body update the predicate map accordingly
                predicates_in_predicates_map.remove(predicate_type);
            }
        }
    });

    debug!(
        "Map of predicates used in predicates {:?}",
        &predicates_in_predicates_map
    );

    let reachable_predicates = compute_reachable_predicates(
        &predicates_in_predicates_map,
        &used_predicates_in_functions_and_methods,
    );

    debug!("All the used predicates are {:?}", &reachable_predicates);

    predicates.retain(|p| reachable_predicates.contains(p.get_type()));

    predicates
}

struct UsedPredicateCollector {
    /// set of all predicates that are used
    used_predicates: HashSet<Type>,
    /// set of all predicates that are folded or unfolded
    folded_predicates: HashSet<Type>,
}

impl UsedPredicateCollector {
    fn new() -> Self {
        UsedPredicateCollector {
            used_predicates: HashSet::new(),
            folded_predicates: HashSet::new(),
        }
    }
}

impl ExprWalker for UsedPredicateCollector {
    fn walk_predicate_access_predicate(
        &mut self,
        PredicateAccessPredicate {
            predicate_type,
            argument,
            ..
        }: &PredicateAccessPredicate,
    ) {
        self.used_predicates.insert(predicate_type.clone());
        ExprWalker::walk(self, argument);
    }

    fn walk_unfolding(
        &mut self,
        Unfolding {
            predicate,
            arguments,
            base,
            ..
        }: &Unfolding,
    ) {
        self.used_predicates.insert(predicate.clone());
        self.folded_predicates.insert(predicate.clone());

        for arg in arguments {
            ExprWalker::walk(self, arg);
        }
        ExprWalker::walk(self, base);
    }
}

impl StmtWalker for UsedPredicateCollector {
    fn walk_expr(&mut self, expr: &Expr) {
        ExprWalker::walk(self, expr);
    }
    fn walk_fold(&mut self, Fold { predicate, .. }: &Fold) {
        self.folded_predicates.insert(predicate.clone());
        self.used_predicates.insert(predicate.clone());
    }

    fn walk_unfold(&mut self, Unfold { predicate, .. }: &Unfold) {
        self.folded_predicates.insert(predicate.clone());
        self.used_predicates.insert(predicate.clone());
    }
}
