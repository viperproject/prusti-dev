// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::vir::{ast::*, cfg, cfg::CfgMethod, CfgBlock};
use std::collections::BTreeSet;

fn get_used_predicates(methods: &[CfgMethod], functions: &[Function]) -> BTreeSet<String> {
    let mut collector = UsedPredicateCollector::new();
    super::walk_methods(methods, &mut collector);
    super::walk_functions(functions, &mut collector);

    // DeadBorrowToken$ is a used predicate but it does not appear in VIR
    // becaue it is only created when viper code is created from VIR
    collector
        .used_predicates
        .insert("DeadBorrowToken$".to_string());
    collector.used_predicates
}

fn get_used_predicates_in_predicates(predicates: &[Predicate]) -> BTreeSet<String> {
    let mut collector = UsedPredicateCollector::new();

    for pred in predicates {
        match pred {
            Predicate::Struct(StructPredicate { body: Some(e), .. }) => {
                ExprWalker::walk(&mut collector, e)
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
            }
            Predicate::Bodyless(_, _) => { /* ignore */ }
        }
    }
    collector.used_predicates
}

pub fn delete_unused_predicates(
    methods: &[CfgMethod],
    functions: &[Function],
    mut predicates: Vec<Predicate>,
) -> Vec<Predicate> {
    let mut has_changed = true;

    let used_preds = get_used_predicates(methods, functions);

    debug!(
        "The used predicates in functions and methods are {:?}",
        &used_preds
    );

    let mut count = 0;
    while has_changed {
        count += 1;
        has_changed = false;

        let predicates_used_in_predicates = get_used_predicates_in_predicates(&predicates);
        debug!(
            "The used predicates in predicates are {:?}",
            &predicates_used_in_predicates
        );
        predicates.retain(|p| {
            let name = p.name();
            let is_used_in_predicate = predicates_used_in_predicates.contains(name);
            let is_used_in_func_or_method = used_preds.contains(name);
            let is_used = is_used_in_predicate || is_used_in_func_or_method;
            if !is_used {
                debug!("The predicate {} was never used and thus removed", name);
                has_changed = true;
            }

            is_used
        });
    }

    debug!("Did {} iterations of predicate removal", count);
    assert!(count <= 2);

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
