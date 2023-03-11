use crate::vir::polymorphic_vir::{
    ast, cfg, utils::walk_method, Expr, Field, LocalVar, Stmt, Type,
};
use log::debug;
use rustc_hash::FxHashSet;
use std::collections::BTreeSet;

/// This purifies local variables in a method body
#[tracing::instrument(level = "debug", skip_all)]
pub fn purify_methods(
    mut methods: Vec<cfg::CfgMethod>,
    predicates: &[ast::Predicate],
) -> Vec<cfg::CfgMethod> {
    for method in &mut methods {
        purify_method(method, predicates);
    }

    methods
}

pub fn is_purifiable_type(ty: &Type) -> bool {
    debug_assert!(crate::config::enable_purification_optimization());
    SUPPORTED_TYPES.contains(&ty.name().as_str())
}

fn translate_type(typ: &Type) -> Type {
    match typ {
        Type::TypedRef(..) => match typ.name().as_str() {
            "i32" | "isize" | "usize" | "u32" => Type::Int,
            "bool" => Type::Bool,
            _ => todo!("{:?}", typ),
        },
        // The type is already translated.
        typ => typ.clone(),
    }
}

static SUPPORTED_TYPES: &[&str] = &["bool", "i32", "isize", "usize", "u32"];

#[tracing::instrument(level = "debug", skip(method, predicates))]
fn purify_method(method: &mut cfg::CfgMethod, predicates: &[ast::Predicate]) {
    let mut candidates = FxHashSet::default();
    for var in &method.local_vars {
        match &var.typ {
            Type::TypedRef(..) if SUPPORTED_TYPES.contains(&var.typ.name().as_str()) => {
                candidates.insert(var.name.clone());
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
        if collector.vars.contains(&var.name) {
            var.typ = translate_type(&var.typ);
        }
    }
    let mut p = Purifier::new(collector, predicates);

    for block in &mut method.basic_blocks {
        let stmts = std::mem::take(&mut block.stmts);
        for stmt in stmts {
            if let Stmt::Inhale(mut inhale) = stmt {
                assert!(p.purified_predicates.is_none());
                p.purified_predicates = Some(BTreeSet::new());
                inhale.expr = ast::ExprFolder::fold(&mut p, inhale.expr);
                block.stmts.push(Stmt::Inhale(inhale));
                for variable in p.purified_predicates.take().unwrap() {
                    block.stmts.push(generate_havoc(variable.clone()));
                    let predicate_type = variable.typ.clone();
                    if let Some(predicate) = p.find_predicate(&predicate_type) {
                        let purified_predicate = predicate
                            .clone()
                            .replace_place(
                                &LocalVar::new("self", predicate_type).into(),
                                &variable.clone().into(),
                            )
                            .purify();
                        block.stmts.push(Stmt::Inhale(ast::Inhale {
                            expr: ast::ExprFolder::fold(&mut p, purified_predicate),
                        }));
                    }
                }
            } else {
                block.stmts.push(ast::StmtFolder::fold(&mut p, stmt));
            };
        }
    }
}

/// This is a ExprWalkerand StmtWalker used to collect information about which
/// local variables can be purified.
///
/// The current implementation is only for ints/bools. So to check if a
/// reference is borrowed we simple check if a variable is ever mentioned
/// without a field access.
#[derive(Debug)]
struct PurifiableVariableCollector {
    vars: FxHashSet<String>,
}

impl PurifiableVariableCollector {
    fn new(initial_vars: FxHashSet<String>) -> Self {
        PurifiableVariableCollector { vars: initial_vars }
    }
}

impl ast::ExprWalker for PurifiableVariableCollector {
    #[tracing::instrument(level = "debug", skip(self, variable))]
    fn walk_local(&mut self, ast::Local { variable, .. }: &ast::Local) {
        if self.vars.remove(&variable.name) {
            debug!("Will not purify the variable {:?} ", variable)
        }
    }

    fn walk_field(&mut self, ast::FieldExpr { box base, .. }: &ast::FieldExpr) {
        match base {
            Expr::Local(_) => {}
            _ => ast::ExprWalker::walk(self, base),
        }
    }
}

impl ast::StmtWalker for PurifiableVariableCollector {
    fn walk_assign(&mut self, ast::Assign { source, .. }: &ast::Assign) {
        ast::ExprWalker::walk(self, source);
    }
}

/// StmtFolder and ExprFolder used to purify local variables
#[derive(Debug)]
struct Purifier<'a> {
    /// names of local variables that can be purified
    targets: BTreeSet<String>,
    /// Viper predicates.
    predicates: &'a [ast::Predicate],
    /// Purified PredicateAccessPredicates within an expression.
    purified_predicates: Option<BTreeSet<LocalVar>>,
}

impl<'a> Purifier<'a> {
    fn new(c: PurifiableVariableCollector, predicates: &'a [ast::Predicate]) -> Self {
        let mut targets = BTreeSet::new();
        for var in c.vars {
            targets.insert(var);
        }

        Purifier {
            targets,
            predicates,
            purified_predicates: None,
        }
    }
    /// Get the body of the struct predicate. If the predicate does not exist,
    /// or is a non-struct predicate, returns `None`.
    fn find_predicate(&self, predicate_type: &Type) -> Option<&Expr> {
        // TODO: Replace with a HashMap or some more performant data structure.
        for predicate in self.predicates {
            match predicate {
                ast::Predicate::Struct(predicate) if &predicate.typ == predicate_type => {
                    return predicate.body.as_ref();
                }
                _ => {}
            }
        }
        None
    }
}

impl<'a> ast::StmtFolder for Purifier<'a> {
    fn fold_expr(&mut self, expr: Expr) -> Expr {
        ast::ExprFolder::fold(self, expr)
    }

    fn fold_assign(
        &mut self,
        ast::Assign {
            target,
            mut source,
            kind,
        }: ast::Assign,
    ) -> Stmt {
        if let Expr::Local(ast::Local {
            variable: local, ..
        }) = &target
        {
            if self.targets.contains(&local.name) {
                assert!(matches!(source.get_type(), Type::TypedRef(..)));
                let source_name = source.get_type().name();
                match source_name.as_str() {
                    "bool" => {
                        source = source.field(Field {
                            name: "val_bool".into(),
                            typ: Type::Bool,
                        });
                    }
                    "i32" | "isize" | "usize" | "u32" => {
                        source = source.field(Field {
                            name: "val_int".into(),
                            typ: Type::Int,
                        });
                    }
                    x => unreachable!("{}", x),
                }
            }
        }
        Stmt::Assign(ast::Assign {
            target: ast::ExprFolder::fold(self, target),
            source: ast::ExprFolder::fold(self, source),
            kind,
        })
    }

    fn fold_method_call(
        &mut self,
        ast::MethodCall {
            method_name,
            arguments,
            mut targets,
        }: ast::MethodCall,
    ) -> Stmt {
        if method_name.starts_with("builtin$havoc")
            && targets.len() == 1
            && self.targets.contains(&targets[0].name)
        {
            generate_havoc(targets.pop().unwrap())
        } else {
            Stmt::MethodCall(ast::MethodCall {
                method_name,
                arguments: arguments.into_iter().map(|e| self.fold_expr(e)).collect(),
                targets,
            })
        }
    }

    fn fold_fold(
        &mut self,
        ast::Fold {
            predicate: predicate_type,
            arguments,
            permission,
            enum_variant,
            position,
        }: ast::Fold,
    ) -> Stmt {
        if let [Expr::Local(ast::Local { variable: l, .. })] = arguments.as_slice() {
            if self.targets.contains(&l.name) {
                if let Some(predicate) = self.find_predicate(&predicate_type) {
                    let purified_predicate = predicate
                        .clone()
                        .replace_place(
                            &LocalVar::new("self", predicate_type).into(),
                            &l.clone().into(),
                        )
                        .purify();
                    return Stmt::Assert(ast::Assert {
                        expr: self.fold_expr(purified_predicate),
                        position,
                    });
                } else {
                    return Stmt::comment("replaced fold".to_string());
                }
            }
        }

        Stmt::Fold(ast::Fold {
            predicate: predicate_type,
            arguments: arguments.into_iter().map(|e| self.fold_expr(e)).collect(),
            permission,
            enum_variant,
            position,
        })
    }

    fn fold_unfold(
        &mut self,
        ast::Unfold {
            predicate: predicate_type,
            arguments,
            permission,
            enum_variant,
        }: ast::Unfold,
    ) -> Stmt {
        if let [Expr::Local(ast::Local { variable: l, .. })] = arguments.as_slice() {
            if self.targets.contains(&l.name) {
                if let Some(predicate) = self.find_predicate(&predicate_type) {
                    let purified_predicate = predicate
                        .clone()
                        .replace_place(
                            &LocalVar::new("self", predicate_type).into(),
                            &l.clone().into(),
                        )
                        .purify();
                    return Stmt::Inhale(ast::Inhale {
                        expr: self.fold_expr(purified_predicate),
                    });
                } else {
                    return Stmt::comment("replaced unfold".to_string());
                }
            }
        }

        Stmt::Unfold(ast::Unfold {
            predicate: predicate_type,
            arguments: arguments.into_iter().map(|e| self.fold_expr(e)).collect(),
            permission,
            enum_variant,
        })
    }
}

impl<'a> ast::ExprFolder for Purifier<'a> {
    fn fold_local(&mut self, ast::Local { variable, position }: ast::Local) -> Expr {
        if self.targets.contains(&variable.name) {
            Expr::local_with_pos(
                LocalVar::new(variable.name, translate_type(&variable.typ)),
                position,
            )
        } else {
            Expr::local_with_pos(variable, position)
        }
    }

    fn fold_field(
        &mut self,
        ast::FieldExpr {
            base,
            field,
            position,
        }: ast::FieldExpr,
    ) -> Expr {
        let rec = self.fold_boxed(base);

        if let Expr::Local(ast::Local {
            variable: l,
            position: lp,
        }) = *rec.clone()
        {
            if self.targets.contains(&l.name) {
                return Expr::local_with_pos(LocalVar::new(l.name, translate_type(&l.typ)), lp);
            }
        }

        Expr::Field(ast::FieldExpr {
            base: rec,
            field,
            position,
        })
    }

    fn fold_predicate_access_predicate(
        &mut self,
        ast::PredicateAccessPredicate {
            predicate_type,
            argument,
            permission,
            position,
        }: ast::PredicateAccessPredicate,
    ) -> Expr {
        if let Expr::Local(ast::Local {
            variable: local, ..
        }) = *argument.clone()
        {
            if self.targets.contains(&local.name) {
                if let Some(purified_predicates) = &mut self.purified_predicates {
                    purified_predicates.insert(local);
                }
                return true.into();
            }
        }

        Expr::PredicateAccessPredicate(ast::PredicateAccessPredicate {
            predicate_type,
            argument: self.fold_boxed(argument),
            permission,
            position,
        })
    }

    fn fold_field_access_predicate(
        &mut self,
        ast::FieldAccessPredicate {
            base: receiver,
            permission,
            position,
        }: ast::FieldAccessPredicate,
    ) -> Expr {
        if let Expr::Field(ast::FieldExpr { base, .. }) = *receiver.clone() {
            if let Expr::Local(ast::Local { variable: l, .. }) = *base {
                if self.targets.contains(&l.name) {
                    return true.into();
                }
            }
        }

        Expr::FieldAccessPredicate(ast::FieldAccessPredicate {
            base: receiver,
            permission,
            position,
        })
    }

    fn fold_unfolding(
        &mut self,
        ast::Unfolding {
            predicate,
            arguments,
            base,
            permission,
            variant,
            position,
        }: ast::Unfolding,
    ) -> Expr {
        if let [Expr::Local(ast::Local {
            variable: local, ..
        })] = arguments.as_slice()
        {
            if self.targets.contains(&local.name) {
                return ast::ExprFolder::fold(self, *base);
            }
        }

        Expr::Unfolding(ast::Unfolding {
            predicate,
            arguments: arguments
                .into_iter()
                .map(|e| ast::ExprFolder::fold(self, e))
                .collect(),
            base: self.fold_boxed(base),
            permission,
            variant,
            position,
        })
    }

    fn fold_labelled_old(
        &mut self,
        ast::LabelledOld {
            label,
            base,
            position,
        }: ast::LabelledOld,
    ) -> Expr {
        let folded_body = self.fold_boxed(base);
        if folded_body.is_heap_dependent() {
            Expr::LabelledOld(ast::LabelledOld {
                label,
                base: folded_body,
                position,
            })
        } else {
            *folded_body
        }
    }
}

fn generate_havoc(variable: LocalVar) -> Stmt {
    assert!(matches!(variable.typ, Type::TypedRef(..)));
    let target_name = variable.typ.name();
    match target_name.as_str() {
        "bool" => Stmt::MethodCall(ast::MethodCall {
            method_name: "builtin$havoc_bool".to_string(),
            arguments: Vec::new(),
            targets: vec![ast::LocalVar::new(variable.name, Type::Bool)],
        }),
        "i32" | "isize" | "usize" | "u32" => Stmt::MethodCall(ast::MethodCall {
            method_name: "builtin$havoc_int".to_string(),
            arguments: Vec::new(),
            targets: vec![ast::LocalVar::new(variable.name, Type::Int)],
        }),
        x => unreachable!("{}", x),
    }
}
