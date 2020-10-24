use std::collections::BTreeSet;
use vir::{ast::*, cfg::CfgMethod};

pub fn remove_not_needed_bodies(
    methods: &[CfgMethod],
    functions: &[Function],
    predicates: &[Predicate],
) -> Vec<Predicate> {
    let mut new_predicates = predicates.to_vec();
    let folded_preds = get_folded_predicates(methods, functions);
    new_predicates.iter_mut().for_each(|predicate| {
        let name_tmp = predicate.name().to_string();
        if !folded_preds.contains(predicate.name()) {
            if let Predicate::Struct(sp) = predicate {
                println!("removing body of {}", name_tmp);

                sp.body = None;
            }
        }
    });
    new_predicates
}
/// Return the names of all predicates that are ever folded or unfolded in the given methods and functions
fn get_folded_predicates(methods: &[CfgMethod], functions: &[Function]) -> BTreeSet<String> {
    let mut collector = FoldedPredicateCollector::new();
    super::walk_methods(methods, &mut collector);
    super::walk_functions(functions, &mut collector);

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
