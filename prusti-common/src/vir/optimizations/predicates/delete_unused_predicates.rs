use std::collections::BTreeSet;
use vir::{ast::*, cfg::CfgMethod};

use vir::CfgBlock;

use crate::vir::Successor;

pub fn delete_unused_predicates(
    methods: &[CfgMethod],
    functions: &[Function],
    predicates: &[Predicate],
) -> Vec<Predicate> {
    let mut has_changed = true;
    let mut new_predicates: Vec<Predicate> = predicates.to_vec();

    let mut used_preds = BTreeSet::new();
    // DeadBorrowToken$ is a used predicate but it does not appear in VIR becaue it is only created when viper code is created from VIR
    used_preds.insert("DeadBorrowToken$".to_string());
    methods.visit(&mut used_preds);
    functions.visit(&mut used_preds);
    dbg!(&used_preds);

    while has_changed {
        has_changed = false;

        let mut predicates_used_in_predicates = BTreeSet::new();
        new_predicates.visit(&mut predicates_used_in_predicates);

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

    return new_predicates;
}

pub trait UsedPredicates {
    /// Simplify by doing constant evaluation.
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
