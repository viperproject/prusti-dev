use crate::vir::{ast::*, cfg, cfg::CfgMethod, utils::walk_method, CfgBlock, Type};
use log::debug;
use std::collections::{BTreeMap, BTreeSet, HashMap};

/// This purifies local variables in a method body
pub fn purify_methods(mut methods: Vec<CfgMethod>) -> Vec<CfgMethod> {
    for method in &mut methods {
        purify_method(method);
    }

    methods
}

fn translate_type(typ: &Type) -> Type {
    match &typ {
        Type::TypedRef(name) => match name.as_str() {
            "i32" | "usize" | "u32" => Type::Int,
            "bool" => Type::Bool,
            _ => todo!("{:?}", typ),
        },
        _ => todo!(),
    }
}

static SUPPORTED_TYPES: &'static [&str] = &["bool", "i32", "usize", "u32"];

fn purify_method(method: &mut CfgMethod) {
    let mut candidates = HashMap::new();
    for var in &method.local_vars {
        match &var.typ {
            &Type::TypedRef(ref t) if SUPPORTED_TYPES.contains(&t.as_str()) => {
                candidates.insert(var.name.clone(), var.typ.clone());
            }
            _ => {}
        };
    }
    let mut collector = PurifiableVariableCollector::new(candidates);

    debug!(
        "PurifiableVariableCollector for method {} before filtering {:?}",
        method.name(),
        collector
    );
    walk_method(method, &mut collector);
    debug!(
        "PurifiableVariableCollector for method {} after filterng {:?}",
        method.name(),
        collector
    );

    for var in &mut method.local_vars {
        if collector.vars.contains_key(&var.name) {
            var.typ = translate_type(&var.typ);
        }
    }
    let mut p = Purifier::new(collector);

    //for stmt in method
    for block in &mut method.basic_blocks {
        block.stmts = block
            .stmts
            .clone()
            .into_iter()
            .map(|stmt| StmtFolder::fold(&mut p, stmt))
            .collect();
    }
}

/// This is a ExprWalkerand StmtWalker used to collect information about which local variables can be purified.
///
/// The current implementation is only for ints/bools. So to check if a reference is borrowed
/// we simple check if a variable is ever mentioned without a field access.
#[derive(Debug)]
struct PurifiableVariableCollector {
    vars: HashMap<String, Type>,
}

impl PurifiableVariableCollector {
    fn new(initial_vars: HashMap<String, Type>) -> Self {
        PurifiableVariableCollector { vars: initial_vars }
    }
}

impl ExprWalker for PurifiableVariableCollector {
    fn walk_local(&mut self, local_var: &LocalVar, _pos: &Position) {
        if self.vars.remove(&local_var.name).is_some() {
            debug!("Will not purify the variable {:?} ", local_var)
        }
    }

    fn walk_field(&mut self, receiver: &Expr, _field: &Field, _pos: &Position) {
        match receiver {
            Expr::Local(_, _) => {}
            _ => ExprWalker::walk(self, receiver),
        }
    }
}

impl StmtWalker for PurifiableVariableCollector {
    fn walk_expr(&mut self, expr: &Expr) {
        ExprWalker::walk(self, expr);
    }
}

/// StmtFolder and ExprFolder used to purify local variables
#[derive(Debug)]
struct Purifier {
    /// names of local variables that can be purified
    targets: BTreeSet<String>,
}

impl Purifier {
    fn new(c: PurifiableVariableCollector) -> Self {
        let mut targets = BTreeSet::new();
        for (k, v) in c.vars {
            targets.insert(k);
        }

        Purifier { targets }
    }
}

impl StmtFolder for Purifier {
    fn fold_expr(&mut self, expr: Expr) -> Expr {
        ExprFolder::fold(self, expr)
    }

    fn fold_method_call(&mut self, name: String, args: Vec<Expr>, targets: Vec<LocalVar>) -> Stmt {
        if name.starts_with("builtin$havoc")
            && targets.len() == 1
            && self.targets.contains(&targets[0].name)
        {
            Stmt::Comment(format!("replaced havoc call for {:?}", targets))
        } else {
            Stmt::MethodCall(
                name,
                args.into_iter().map(|e| self.fold_expr(e)).collect(),
                targets,
            )
        }
    }

    fn fold_fold(
        &mut self,
        predicate_name: String,
        args: Vec<Expr>,
        perm_amount: PermAmount,
        variant: MaybeEnumVariantIndex,
        pos: Position,
    ) -> Stmt {
        if let [Expr::Local(l, _)] = &*args.clone() {
            if self.targets.contains(&l.name) {
                return Stmt::Comment(format!("replaced fold"));
            }
        }
        Stmt::Fold(
            predicate_name,
            args.into_iter().map(|e| self.fold_expr(e)).collect(),
            perm_amount,
            variant,
            pos,
        )
    }

    fn fold_unfold(
        &mut self,
        predicate_name: String,
        args: Vec<Expr>,
        perm_amount: PermAmount,
        variant: MaybeEnumVariantIndex,
    ) -> Stmt {
        if let [Expr::Local(l, _)] = &*args.clone() {
            if self.targets.contains(&l.name) {
                return Stmt::Comment(format!("replaced unfold"));
            }
        }

        Stmt::Unfold(
            predicate_name,
            args.into_iter().map(|e| self.fold_expr(e)).collect(),
            perm_amount,
            variant,
        )
    }
}

impl ExprFolder for Purifier {
    fn fold_field(&mut self, receiver: Box<Expr>, field: Field, pos: Position) -> Expr {
        let rec = self.fold_boxed(receiver);

        if let Expr::Local(l, lp) = *rec.clone() {
            if self.targets.contains(&l.name) {
                return Expr::Local(LocalVar::new(l.name, translate_type(&l.typ)), lp);
            }
        }

        Expr::Field(rec, field, pos)
    }

    fn fold_predicate_access_predicate(
        &mut self,
        name: String,
        arg: Box<Expr>,
        perm_amount: PermAmount,
        pos: Position,
    ) -> Expr {
        if let Expr::Local(local, _) = *arg.clone() {
            if self.targets.contains(&local.name) {
                return true.into();
            }
        }

        Expr::PredicateAccessPredicate(name, self.fold_boxed(arg), perm_amount, pos)
    }

    fn fold_field_access_predicate(
        &mut self,
        receiver: Box<Expr>,
        perm_amount: PermAmount,
        pos: Position,
    ) -> Expr {
        if let Expr::Field(a, _field, _) = *receiver.clone() {
            if let Expr::Local(l, _) = *a {
                if self.targets.contains(&l.name) {
                    return true.into();
                }
            }
        }

        Expr::FieldAccessPredicate(receiver, perm_amount, pos)
    }

    fn fold_unfolding(
        &mut self,
        name: String,
        args: Vec<Expr>,
        expr: Box<Expr>,
        perm: PermAmount,
        variant: MaybeEnumVariantIndex,
        pos: Position,
    ) -> Expr {
        if let [Expr::Local(local, _)] = &*args.clone() {
            if self.targets.contains(&local.name) {
                return true.into();
            }
        }

        Expr::Unfolding(
            name,
            args.into_iter()
                .map(|e| ExprFolder::fold(self, e))
                .collect(),
            self.fold_boxed(expr),
            perm,
            variant,
            pos,
        )
    }
}
