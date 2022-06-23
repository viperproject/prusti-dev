use crate::vir::polymorphic_vir::{
    ast::*,
    cfg::CfgMethod,
    utils::{walk_functions, walk_methods},
};

fn matches_useless_predicate(typ: &Type, useless: &Vec<Predicate>) -> bool {
    for p in useless {
        if p.get_type() == typ {
            return true;
        }
    }
    false
}

pub fn delete_useless_predicates(
    methods: Vec<CfgMethod>,
    functions: &[Function],
    mut predicates: Vec<Predicate>,
) -> (Vec<Predicate>, Vec<CfgMethod>) {
    let (useless, remaining): (Vec<Predicate>, Vec<Predicate>) = predicates.into_iter().partition(|p| p.body() == Some(true.into()));
    let new_methods = methods.into_iter().map(|mut m| {
        m.retain_stmts(|stmt| match stmt {
            Stmt::Inhale(Inhale {
                expr:
                    Expr::PredicateAccessPredicate(p),
            }) => !matches_useless_predicate(&p.predicate_type, &useless),
            Stmt::Exhale(Exhale {
                expr:
                    Expr::PredicateAccessPredicate(p),
                ..
            }) => !matches_useless_predicate(&p.predicate_type, &useless),
            Stmt::Obtain(Obtain {
                expr:
                    Expr::PredicateAccessPredicate(p),
                ..
            }) => !matches_useless_predicate(&p.predicate_type, &useless),
            Stmt::Fold(Fold {
                predicate: p,
                ..
            }) => !matches_useless_predicate(p, &useless),
            _ => true
        });
        m
    });
    (remaining, new_methods.collect())
}
