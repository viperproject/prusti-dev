use crate::vir::polymorphic_vir::{ast, cfg, utils::walk_method, Expr, Stmt, Position, Type, LocalVar, Field};
use prusti_utils::force_matches;
use log::debug;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

/// This purifies local variables in a method body
pub fn purify_methods(
    mut methods: Vec<cfg::CfgMethod>,
    predicates: &[ast::Predicate]
) -> Vec<cfg::CfgMethod> {
    for method in &mut methods {
        purify_method(method, predicates);
    }

    methods
}

fn translate_type(typ: &Type) -> Type {
    match typ {
        Type::TypedRef(..) => match typ.name().as_str() {
            "i32" | "usize" | "u32" => Type::Int,
            "bool" => Type::Bool,
            _ => todo!("{:?}", typ),
        },
        // The type is already translated.
        typ => typ.clone(),
    }
}

static SUPPORTED_TYPES: &'static [&str] = &["bool", "i32", "usize", "u32"];

fn purify_method(method: &mut cfg::CfgMethod, predicates: &[ast::Predicate]) {
    let mut candidates = HashSet::new();
    for var in &method.local_vars {
        match &var.typ {
            &Type::TypedRef(..) if SUPPORTED_TYPES.contains(&var.typ.name().as_str()) => {
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

    //for stmt in method
    for block in &mut method.basic_blocks {
        block.stmts = block
            .stmts
            .clone()
            .into_iter()
            .map(|stmt| ast::StmtFolder::fold(&mut p, stmt))
            .collect();
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
    vars: HashSet<String>,
}

impl PurifiableVariableCollector {
    fn new(initial_vars: HashSet<String>) -> Self {
        PurifiableVariableCollector { vars: initial_vars }
    }
}

impl ast::ExprWalker for PurifiableVariableCollector {
    fn walk_local(&mut self, local_var: &LocalVar, _pos: &Position) {
        if self.vars.remove(&local_var.name) {
            debug!("Will not purify the variable {:?} ", local_var)
        }
    }

    fn walk_field(&mut self, receiver: &Expr, _field: &Field, _pos: &Position) {
        match receiver {
            Expr::Local(_) => {}
            _ => ast::ExprWalker::walk(self, receiver),
        }
    }
}

impl ast::StmtWalker for PurifiableVariableCollector {
    fn walk_assign(&mut self, _target: &Expr, expr: &Expr, _kind: &ast::AssignKind) {
        ast::ExprWalker::walk(self, expr);
    }
}

/// StmtFolder and ExprFolder used to purify local variables
#[derive(Debug)]
struct Purifier<'a> {
    /// names of local variables that can be purified
    targets: BTreeSet<String>,
    /// Viper predicates.
    predicates: &'a [ast::Predicate],
}

impl<'a> Purifier<'a> {
    fn new(c: PurifiableVariableCollector, predicates: &'a [ast::Predicate]) -> Self {
        let mut targets = BTreeSet::new();
        for var in c.vars {
            targets.insert(var);
        }

        Purifier { targets, predicates }
    }
    /// Get the body of the struct predicate. If the predicate does not exist,
    /// or is a non-struct predicate, returns `None`.
    fn find_predicate(&self, predicate_name: &str) -> Option<&Expr> {
        // TODO: Replace with a HashMap or some more performant data structure.
        for predicate in self.predicates {
            match predicate {
                ast::Predicate::Struct(predicate)
                        if predicate.typ.name() == predicate_name => {
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

    fn fold_assign(&mut self, target: Expr, mut source: Expr, kind: ast::AssignKind) -> Stmt {
        if let Expr::Local( ast::Local {variable: local, ..}) = &target {
            if self.targets.contains(&local.name) {
                let source_name = force_matches!(source.get_type(), Type::TypedRef(..) => source.get_type().name());
                match source_name.as_str() {
                    "bool" => {
                        source = source.field(Field {
                            name: "val_bool".into(),
                            typ: Type::Bool,
                        });
                    }
                    "i32" | "usize" | "u32" => {
                        source = source.field(Field {
                            name: "val_int".into(),
                            typ: Type::Int,
                        });
                    }
                    x => unreachable!("{}", x),
                }
            }
        }
        Stmt::Assign( ast::Assign {
            target: ast::ExprFolder::fold(self, target),
            source: ast::ExprFolder::fold(self, source),
            kind,
        })
    }

    fn fold_method_call(&mut self, name: String, args: Vec<Expr>, targets: Vec<LocalVar>) -> Stmt {
        if name.starts_with("builtin$havoc")
            && targets.len() == 1
            && self.targets.contains(&targets[0].name)
        {
            Stmt::comment(format!("replaced havoc call for {:?}", targets))
        } else {
            Stmt::MethodCall( ast::MethodCall {
                method_name: name,
                arguments: args.into_iter().map(|e| self.fold_expr(e)).collect(),
                targets,
            })
        }
    }

    fn fold_fold(
        &mut self,
        predicate_name: String,
        args: Vec<Expr>,
        perm_amount: ast::PermAmount,
        variant: ast::MaybeEnumVariantIndex,
        pos: Position,
    ) -> Stmt {
        if let [Expr::Local( ast::Local {variable: l, ..} )] = args.as_slice() {
            if self.targets.contains(&l.name) {
                if let Some(predicate) = self.find_predicate(&predicate_name) {
                    let purified_predicate = predicate.clone().replace_place(
                        &LocalVar::new("self", Type::typed_ref(predicate_name)).into(),
                        &l.clone().into()
                    ).purify();
                    return Stmt::Assert( ast::Assert {
                        expr: self.fold_expr(purified_predicate),
                        position: pos
                    })
                } else {
                    return Stmt::comment(format!("replaced fold"));
                }
            }
        }

        Stmt::Fold( ast::Fold {
            predicate_name,
            arguments: args.into_iter().map(|e| self.fold_expr(e)).collect(),
            permission: perm_amount,
            enum_variant: variant,
            position: pos,
        })
    }

    fn fold_unfold(
        &mut self,
        predicate_name: String,
        args: Vec<Expr>,
        perm_amount: ast::PermAmount,
        variant: ast::MaybeEnumVariantIndex,
    ) -> Stmt {
        if let [Expr::Local( ast::Local {variable: l, ..} )] = args.as_slice() {
            if self.targets.contains(&l.name) {
                if let Some(predicate) = self.find_predicate(&predicate_name) {
                    let purified_predicate = predicate.clone().replace_place(
                        &LocalVar::new("self", Type::typed_ref(predicate_name)).into(),
                        &l.clone().into()
                    ).purify();
                    return Stmt::Inhale( ast::Inhale {
                        expr: self.fold_expr(purified_predicate),
                    })
                } else {
                    return Stmt::comment(format!("replaced unfold"));
                }
            }
        }

        Stmt::Unfold( ast::Unfold {
            predicate_name,
            arguments: args.into_iter().map(|e| self.fold_expr(e)).collect(),
            permission: perm_amount,
            enum_variant: variant,
        })
    }
}

impl<'a> ast::ExprFolder for Purifier<'a> {

    fn fold_local(&mut self, local: LocalVar, pos: Position) -> Expr {
        if self.targets.contains(&local.name) {
            Expr::Local( ast::Local {variable: LocalVar::new(local.name, translate_type(&local.typ)), position: pos} )
        } else {
            Expr::Local( ast::Local {variable: local, position: pos} )
        }
    }

    fn fold_field(&mut self, receiver: Box<Expr>, field: Field, pos: Position) -> Expr {
        let rec = self.fold_boxed(receiver);

        if let Expr::Local( ast::Local {variable: l, position: lp} ) = *rec.clone() {
            if self.targets.contains(&l.name) {
                return Expr::Local( ast::Local {variable: LocalVar::new(l.name, translate_type(&l.typ)), position: lp} );
            }
        }

        Expr::Field( ast::FieldExpr {
            base: rec,
            field,
            position: pos,
        })
    }

    fn fold_predicate_access_predicate(
        &mut self,
        typ: Type,
        arg: Box<Expr>,
        perm_amount: ast::PermAmount,
        pos: Position,
    ) -> Expr {
        if let Expr::Local( ast::Local {variable: local, ..} ) = *arg.clone() {
            if self.targets.contains(&local.name) {
                return true.into();
            }
        }

        Expr::PredicateAccessPredicate( ast::PredicateAccessPredicate {
            predicate_type: typ,
            argument: self.fold_boxed(arg),
            permission: perm_amount,
            position: pos,
        })
    }

    fn fold_field_access_predicate(
        &mut self,
        receiver: Box<Expr>,
        perm_amount: ast::PermAmount,
        pos: Position,
    ) -> Expr {
        if let Expr::Field( ast::FieldExpr {base, ..} ) = *receiver.clone() {
            if let Expr::Local( ast::Local {variable: l, ..} ) = *base {
                if self.targets.contains(&l.name) {
                    return true.into();
                }
            }
        }

        Expr::FieldAccessPredicate( ast::FieldAccessPredicate {
            base: receiver,
            permission: perm_amount,
            position: pos,
        })
    }

    fn fold_unfolding(
        &mut self,
        name: String,
        args: Vec<Expr>,
        expr: Box<Expr>,
        perm: ast::PermAmount,
        variant: ast::MaybeEnumVariantIndex,
        pos: Position,
    ) -> Expr {
        if let [Expr::Local( ast::Local {variable: local, ..} )] = args.as_slice() {
            if self.targets.contains(&local.name) {
                return ast::ExprFolder::fold(self, *expr);
            }
        }

        Expr::Unfolding( ast::Unfolding {
            predicate_name: name,
            arguments: args.into_iter()
                .map(|e| ast::ExprFolder::fold(self, e))
                .collect(),
            base: self.fold_boxed(expr),
            permission: perm,
            variant,
            position: pos,
        })
    }

    fn fold_labelled_old(&mut self, label: String, body: Box<Expr>, pos: Position) -> Expr {
        let folded_body = self.fold_boxed(body);
        if folded_body.is_heap_dependent() {
            Expr::LabelledOld( ast::LabelledOld {
                label: label,
                base: folded_body,
                position: pos,
            })
        } else {
            *folded_body
        }
    }
}
