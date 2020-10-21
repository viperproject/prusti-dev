use std::collections::BTreeSet;
use vir::{ast::*, cfg::CfgMethod};

use vir::CfgBlock;

use crate::vir::{cfg, Successor};

fn get_used_predicates(methods: &[CfgMethod], functions: &[Function]) -> BTreeSet<String> {
    let mut collector = UsedPredicateCollector::new();
    for method in methods {
        method.walk_statements(|stmt| {
            StmtWalker::walk(&mut collector, stmt);
        });
        method.walk_successors(|successor| match successor {
            cfg::Successor::Undefined | cfg::Successor::Return | cfg::Successor::Goto(_) => {}
            cfg::Successor::GotoSwitch(conditional_targets, _) => {
                for (expr, _) in conditional_targets {
                    ExprWalker::walk(&mut collector, expr);
                }
            }
        });
    }

    for function in functions {
        for e in &function.pres {
            ExprWalker::walk(&mut collector, e);
        }

        for e in &function.posts {
            ExprWalker::walk(&mut collector, e);
        }

        for e in &function.body {
            ExprWalker::walk(&mut collector, e);
        }
    }
    // DeadBorrowToken$ is a used predicate but it does not appear in VIR becaue it is only created when viper code is created from VIR
    collector
        .used_predicates
        .insert("DeadBorrowToken$".to_string());
    collector.used_predicates
}

fn get_used_predicates_old(methods: &[CfgMethod], functions: &[Function]) -> BTreeSet<String> {
    let mut used_preds = BTreeSet::new();
    // DeadBorrowToken$ is a used predicate but it does not appear in VIR becaue it is only created when viper code is created from VIR
    used_preds.insert("DeadBorrowToken$".to_string());
    methods.visit(&mut used_preds);
    functions.visit(&mut used_preds);
    used_preds
}

fn get_used_predicates_in_predicates(predicates: &[Predicate]) -> BTreeSet<String> {
    let mut collector = UsedPredicateCollector::new();

    for pred in predicates {
        match pred {
            Predicate::Struct(s) => s
                .body
                .iter()
                .for_each(|e| ExprWalker::walk(&mut collector, e)),
            Predicate::Enum(p) => {
                ExprWalker::walk(&mut collector, &p.discriminant);
                ExprWalker::walk(&mut collector, &p.discriminant_bounds);

                for (e, _, sp) in &p.variants {
                    ExprWalker::walk(&mut collector, e);
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

fn get_used_predicates_in_predicates_old(predicates: &[Predicate]) -> BTreeSet<String> {
    let mut predicates_used_in_predicates = BTreeSet::new();
    predicates.visit(&mut predicates_used_in_predicates);
    return predicates_used_in_predicates;
}

fn remove_body_of_predicates_if_never_unfolded(
    predicates: &[Predicate],
    predicates_only_used_in_predicates: &BTreeSet<String>,
) -> Vec<Predicate> {
    for predicate in predicates {
        {}
    }
    let mut new_predicates = predicates.to_vec();

    new_predicates.iter_mut().for_each(|predicate| {
        let predicates_used_in_this_predicate =
            get_used_predicates_in_predicates(&[predicate.clone()]);
        if predicates_used_in_this_predicate
            .intersection(&predicates_only_used_in_predicates)
            .next()
            .is_some()
        {
            if let Predicate::Struct(sp) = predicate {
                sp.body = None;
            }
        }
    });
    new_predicates
}

pub fn delete_unused_predicates(
    methods: &[CfgMethod],
    functions: &[Function],
    predicates: &[Predicate],
) -> Vec<Predicate> {
    let mut has_changed = true;
    let mut new_predicates: Vec<Predicate> = predicates.to_vec();

    let used_preds_new = get_used_predicates(methods, functions);
    let used_preds_old = get_used_predicates_old(methods, functions);

    assert_eq!(used_preds_new, used_preds_old);
    let used_preds = used_preds_new;
    dbg!(&used_preds);

    while has_changed {
        has_changed = false;
        let predicates_used_in_predicates_old =
            get_used_predicates_in_predicates_old(&new_predicates);

        let predicates_used_in_predicates_new = get_used_predicates_in_predicates(&new_predicates);
        assert_eq!(
            predicates_used_in_predicates_old,
            predicates_used_in_predicates_new
        );
        let predicates_used_in_predicates = predicates_used_in_predicates_new;
        dbg!(&predicates_used_in_predicates);
        new_predicates = new_predicates
            .into_iter()
            .filter(|p| {
                let name = p.name();
                let is_used_in_predicate = predicates_used_in_predicates.contains(name);
                let is_used_in_func_or_method = used_preds.contains(name);
                let is_used = is_used_in_predicate || is_used_in_func_or_method;
                if !is_used {
                    has_changed = true;
                }

                is_used
            })
            .collect();
    }

    let predicates_used_in_predicates = get_used_predicates_in_predicates(&new_predicates);
    let only_used_in_predicates: BTreeSet<String> = predicates_used_in_predicates
        .difference(&used_preds)
        .cloned()
        .collect();
    dbg!(&only_used_in_predicates);

    // FIXME: This acctually removes bodies that are needed
    /*new_predicates =
    remove_body_of_predicates_if_never_unfolded(&new_predicates, &only_used_in_predicates);*/
    return new_predicates;
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
pub trait UsedPredicates {
    fn visit(&self, set: &mut BTreeSet<String>);
}

impl<T> UsedPredicates for &[T]
where
    T: UsedPredicates,
{
    fn visit(&self, set: &mut BTreeSet<String>) {
        for e in *self {
            e.visit(set)
        }
    }
}

impl<T> UsedPredicates for Vec<T>
where
    T: UsedPredicates,
{
    fn visit(&self, set: &mut BTreeSet<String>) {
        for e in self {
            e.visit(set)
        }
    }
}

impl<T> UsedPredicates for Option<T>
where
    T: UsedPredicates,
{
    fn visit(&self, set: &mut BTreeSet<String>) {
        match self {
            Some(e) => e.visit(set),
            None => {}
        }
    }
}
impl UsedPredicates for CfgMethod {
    fn visit(&self, set: &mut BTreeSet<String>) {
        for block in &self.basic_blocks {
            block.visit(set);
        }
    }
}

impl UsedPredicates for CfgBlock {
    fn visit(&self, set: &mut BTreeSet<String>) {
        //FIXME: This is private?
        //for expr in self.invs {}

        self.stmts.visit(set);

        if let Successor::GotoSwitch(conds, _) = &self.successor {
            for (e, _) in conds {
                e.visit(set);
            }
        }
    }
}

impl UsedPredicates for Expr {
    fn visit(&self, set: &mut BTreeSet<String>) {
        match self {
            Expr::Cond(e1, e2, e3, _) => {
                e1.visit(set);
                e2.visit(set);
                e3.visit(set);
            }
            Expr::ForAll(_, triggers, e, _) => {
                e.visit(set);
                triggers.visit(set);
            }
            Expr::FuncApp(_, e, _, _, _) | Expr::DomainFuncApp(_, e, _) => {
                e.visit(set);
            }
            Expr::PredicateAccessPredicate(name, expr, _, _) => {
                expr.visit(set);
                set.insert(name.clone());
            }
            Expr::LabelledOld(_, e, _)
            | Expr::FieldAccessPredicate(e, _, _)
            | Expr::AddrOf(e, _, _)
            | Expr::Variant(e, _, _)
            | Expr::Field(e, _, _)
            | Expr::UnaryOp(_, e, _) => e.visit(set),

            Expr::Unfolding(name, e1, e2, _, _, _) => {
                set.insert(name.clone());
                e1.visit(set);
                e2.visit(set);
            }

            Expr::LetExpr(_, e1, e2, _)
            | Expr::MagicWand(e1, e2, _, _)
            | Expr::InhaleExhale(e1, e2, _)
            | Expr::BinOp(_, e1, e2, _) => {
                e1.visit(set);
                e2.visit(set);
            }
            Expr::Const(_, _) | Expr::Local(_, _) => { /*ignore*/ }
        }
    }
}

impl UsedPredicates for Trigger {
    fn visit(&self, set: &mut BTreeSet<String>) {
        self.elements().visit(set);
    }
}

impl UsedPredicates for Stmt {
    fn visit(&self, set: &mut BTreeSet<String>) {
        match self {
            Stmt::PackageMagicWand(e, stmts, _, _, _) => {
                e.visit(set);
                stmts.visit(set);
            }
            Stmt::ExpireBorrows(eb) => {
                println!("ignoring {:?} because cannot access", eb)
                /*FIXME*/
            }
            Stmt::If(e, s1, s2) => {
                e.visit(set);
                s1.visit(set);
                s2.visit(set);
            }
            Stmt::ApplyMagicWand(e, _)
            | Stmt::Obtain(e, _)
            | Stmt::Exhale(e, _)
            | Stmt::Inhale(e, _)
            | Stmt::Assert(e, _, _) => e.visit(set),

            Stmt::MethodCall(_, e, _) => e.visit(set),
            Stmt::TransferPerm(e1, e2, _) | Stmt::Assign(e1, e2, _) => {
                e1.visit(set);
                e2.visit(set);
            }
            Stmt::Fold(name, e, _, _, _) | Stmt::Unfold(name, e, _, _) => {
                set.insert(name.clone());
                e.visit(set);
            }

            Stmt::Label(_) | Stmt::Comment(_) | Stmt::BeginFrame | Stmt::EndFrame => { /* ignore */
            }
        }
    }
}

impl UsedPredicates for Predicate {
    fn visit(&self, set: &mut BTreeSet<String>) {
        match self {
            Predicate::Struct(s) => s.body.visit(set),
            Predicate::Enum(p) => {
                p.discriminant.visit(set);
                p.discriminant_bounds.visit(set);
                for (e, _, sp) in &p.variants {
                    e.visit(set);
                    sp.body.visit(set);
                }
            }
            Predicate::Bodyless(_, _) => { /* ignore */ }
        }
    }
}

impl UsedPredicates for Function {
    fn visit(&self, set: &mut BTreeSet<String>) {
        self.pres.visit(set);
        self.posts.visit(set);
        self.body.visit(set);
    }
}
