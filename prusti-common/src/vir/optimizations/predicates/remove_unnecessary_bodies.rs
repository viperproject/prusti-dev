// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::collections::BTreeSet;
use vir::{ast::*, cfg::CfgMethod};

use crate::vir::utils::{walk_functions, walk_methods};

/// Returns the provided predicates but deletes the bodies of predicates where the body is not needed
pub fn remove_unnecessary_bodies(
    methods: &[CfgMethod],
    functions: &[Function],
    mut predicates: Vec<Predicate>,
) -> Vec<Predicate> {
    let folded_preds = get_folded_predicates(methods, functions);
    predicates.iter_mut().for_each(|predicate| {
        let name_tmp = predicate.name().to_string();
        if !folded_preds.contains(predicate.name()) {
            if let Predicate::Struct(sp) = predicate {
                debug!("Removed body of {}", name_tmp);

                sp.body = None;
            }
        }
    });

    predicates
}
/// Return the names of all predicates that are ever folded or unfolded in the given methods and functions
fn get_folded_predicates(methods: &[CfgMethod], functions: &[Function]) -> BTreeSet<String> {
    let mut collector = FoldedPredicateCollector::new();
    walk_methods(methods, &mut collector);
    walk_functions(functions, &mut collector);

    return collector.unfolded_predicates;
}

struct FoldedPredicateCollector {
    unfolded_predicates: BTreeSet<String>,
}

impl FoldedPredicateCollector {
    fn new() -> Self {
        FoldedPredicateCollector {
            unfolded_predicates: BTreeSet::new(),
        }
    }
}

impl ExprWalker for FoldedPredicateCollector {
    fn walk_unfolding(
        &mut self,
        name: &str,
        args: &Vec<Expr>,
        body: &Expr,
        _perm: PermAmount,
        _variant: &MaybeEnumVariantIndex,
        _pos: &Position,
    ) {
        self.unfolded_predicates.insert(name.to_string());
        for arg in args {
            ExprWalker::walk(self, arg);
        }
        ExprWalker::walk(self, body);
    }
}

impl StmtWalker for FoldedPredicateCollector {
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
        self.unfolded_predicates.insert(predicate_name.to_string());
    }

    fn walk_unfold(
        &mut self,
        predicate_name: &str,
        args: &Vec<Expr>,
        _perm: &PermAmount,
        _variant: &MaybeEnumVariantIndex,
    ) {
        self.unfolded_predicates.insert(predicate_name.to_string());
    }
}
