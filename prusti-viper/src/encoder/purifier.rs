// This file should be in `prusti-common/src/vir/optimizations/purification/`,
// but it depends on encoder…
// TODO: add a vir::Type::SnapOf(t: Box<vir::Type>) variant to vir::Type to
// represent types like "snapshot of X". Resolve SnapOf in snapshot patcher.

use vir_crate::polymorphic::{self as polymorphic_vir, ExprWalker, ExprFolder, StmtWalker, StmtFolder};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use log::{debug, trace};
use crate::encoder::Encoder;

/// Replaces shared references to pure Viper variables.
pub fn purify_method(
    encoder: &Encoder,
    method: &mut polymorphic_vir::CfgMethod
) {
    // A set of candidate references to be purified.
    let mut candidates = HashSet::new();
    debug!("method: {}", method.name());
    for var in &method.local_vars {
        match &var.typ {
            &polymorphic_vir::Type::TypedRef(ref typed_ref) if typed_ref.label.starts_with("ref$") => {
                trace!("  candidate: {}: {}", var.name, var.typ);
                candidates.insert(var.name.clone());
            }
            _ => {}
        };
    }
    if candidates.is_empty() {
        return;
    }

    // Collect variables that are dereferenced.
    let mut collector = VarDependencyCollector::default();
    polymorphic_vir::utils::walk_method(method, &mut collector);
    debug!(
        "VarDependencyCollector for method {} after collection {:?}",
        method.name(),
        collector
    );
    collector.compute_dereferenced_variables_fixpoint();
    debug!(
        "Dereferenced variables for method {} after fixpoint {:?}",
        method.name(),
        collector.dereferenced_variables
    );
    collector.compute_borrowing_variables_fixpoint();
    debug!(
        "Borrowing variables for method {} after fixpoint {:?}",
        method.name(),
        collector.borrowing_variables
    );
    // Filter out variables that are dereferenced.
    candidates.retain(|var| !collector.dereferenced_variables.contains(var));
    candidates.retain(|var| !collector.borrowing_variables.contains(var));
    debug!(
        "Variables in method {} to be purified {:?}",
        method.name(),
        candidates
    );

    let mut purifier = Purifier::new(encoder, candidates);

    for block in &mut method.basic_blocks {
        block.stmts = block
            .stmts
            .clone()
            .into_iter()
            .map(|stmt| StmtFolder::fold(&mut purifier, stmt))
            .collect();
    }

    for var in &mut method.local_vars {
        if purifier.vars.contains(&var.name) {
            let typ = std::mem::replace(&mut var.typ, polymorphic_vir::Type::Bool);
            var.typ = translate_type(encoder, typ);
        } else if let Some(typ) = purifier.change_var_types.remove(&var.name) {
            var.typ = translate_type(encoder, typ);
        }
    }

    method.local_vars.extend(purifier.fresh_variables);
}

/// This is a ExprWalkerand StmtWalker used to collect information about which
/// local variables can be purified.
#[derive(Debug, Default)]
struct VarDependencyCollector {
    /// (Potentially) references that are dereferenced.
    dereferenced_variables: HashSet<String>,
    /// (Potentially) references that borrow other variables.
    borrowing_variables: HashSet<String>,
    /// Variables that are potentially reborrowed.
    dependencies: HashMap<String, HashSet<String>>,
    /// Variables that are potentially reborrowed.
    dependents: HashMap<String, HashSet<String>>,
}

impl VarDependencyCollector {
    /// Compute the fix-point of all dereferenced variables: dependencies of all
    /// dereferenced variables are also dereferenced variables.
    fn compute_dereferenced_variables_fixpoint(&mut self) {
        let mut changed = true;
        while changed {
            let mut add_queue = Vec::new();
            for var in &self.dereferenced_variables {
                if let Some(dependencies) = self.dependencies.remove(var) {
                    add_queue.push(dependencies);
                }
            }
            changed = !add_queue.is_empty();
            for dependencies in add_queue {
                self.dereferenced_variables.extend(dependencies);
            }
        }
    }
    /// Compute the fix-point of all borrowing variables: dependents of all
    /// borrowing variables are also borrowing variables.
    fn compute_borrowing_variables_fixpoint(&mut self) {
        let mut changed = true;
        while changed {
            let mut add_queue = Vec::new();
            for var in &self.borrowing_variables {
                if let Some(dependents) = self.dependents.remove(var) {
                    add_queue.push(dependents);
                }
            }
            changed = !add_queue.is_empty();
            for dependents in add_queue {
                self.borrowing_variables.extend(dependents);
            }
        }
    }
}

impl ExprWalker for VarDependencyCollector {
    fn walk_field(&mut self, receiver: &polymorphic_vir::Expr, _field: &polymorphic_vir::Field, _pos: &polymorphic_vir::Position) {
        match receiver {
            // If we have a variable that is accessed two levels down, we assume
            // that it is dereferenced without checking the actual type.
            polymorphic_vir::Expr::Field( polymorphic_vir::FieldExpr {base: box polymorphic_vir::Expr::Local( polymorphic_vir::Local {variable: local_var, ..}), ..} ) => {
                self.dereferenced_variables.insert(local_var.name.clone());
            }
            _ => ExprWalker::walk(self, receiver),
        }
    }
}

impl StmtWalker for VarDependencyCollector {
    fn walk_expr(&mut self, expr: &polymorphic_vir::Expr) {
        ExprWalker::walk(self, expr);
    }
    fn walk_assign(&mut self, target: &polymorphic_vir::Expr, source: &polymorphic_vir::Expr, kind: &polymorphic_vir::AssignKind) {
        let dependencies = collect_variables(source);
        let dependents = collect_variables(target);
        for dependent in &dependents {
            let entry = self.dependencies.entry(dependent.clone()).or_insert(HashSet::new());
            entry.extend(dependencies.iter().cloned());
        }
        for dependency in dependencies {
            let entry = self.dependents.entry(dependency).or_insert(HashSet::new());
            entry.extend(dependents.iter().cloned());
        }
        match kind {
            polymorphic_vir::AssignKind::SharedBorrow(_) |
            polymorphic_vir::AssignKind::MutableBorrow(_) => {
                match target {
                    polymorphic_vir::Expr::Field( polymorphic_vir::FieldExpr {base: box polymorphic_vir::Expr::Local( polymorphic_vir::Local {variable: local_var, ..} ), ..} ) => {
                        match source {
                            polymorphic_vir::Expr::Field( polymorphic_vir::FieldExpr {base: box polymorphic_vir::Expr::Local(_), field: polymorphic_vir::Field { name, .. }, ..} )
                                if name == "val_ref" => {
                                // Reborrowing is fine.
                            }
                            _ => {
                                self.borrowing_variables.insert(local_var.name.clone());
                            }
                        }
                    }
                    _ => {},
                }
            }
            _ => {}
        }
        self.walk_expr(target);
        self.walk_expr(source);
    }
}

fn collect_variables(expr: &polymorphic_vir::Expr) -> HashSet<String> {
    let mut collector = VariableCollector { vars: HashSet::new() };
    ExprWalker::walk(&mut collector, expr);
    collector.vars
}

struct VariableCollector {
    vars: HashSet<String>,
}

impl ExprWalker for VariableCollector {
    fn walk_local(&mut self, local_var: &polymorphic_vir::LocalVar, _pos: &polymorphic_vir::Position) {
        if !self.vars.contains(&local_var.name) {
            self.vars.insert(local_var.name.clone());
        }
    }
}

fn translate_type(encoder: &Encoder, typ: polymorphic_vir::Type) -> polymorphic_vir::Type {
    match typ {
        polymorphic_vir::Type::Int
        | polymorphic_vir::Type::Bool
        | polymorphic_vir::Type::Snapshot(_)
        | polymorphic_vir::Type::Domain(_) => typ,
        polymorphic_vir::Type::TypedRef(_) | polymorphic_vir::Type::TypeVar(_) => {
            let mir_typ = encoder.decode_type_predicate_type(&typ).unwrap(); // FIXME: unwrap
            encoder.encode_snapshot_type(mir_typ).unwrap() // FIXME: unwrap
        }
        polymorphic_vir::Type::Seq(_) => unreachable!(),
    }
}

struct Purifier<'p, 'v: 'p, 'tcx: 'v> {
    encoder: &'p Encoder<'v, 'tcx>,
    vars: HashSet<String>,
    fresh_variables: Vec<polymorphic_vir::LocalVar>,
    change_var_types: HashMap<String, polymorphic_vir::Type>,
}

impl<'p, 'v: 'p, 'tcx: 'v> Purifier<'p, 'v, 'tcx> {
    fn new(encoder: &'p Encoder<'v, 'tcx>, vars: HashSet<String>) -> Self {
        Self {
            encoder,
            vars,
            fresh_variables: Vec::new(),
            change_var_types: HashMap::new(),
        }
    }
    fn fresh_variable(&mut self, typ: &polymorphic_vir::Type) -> polymorphic_vir::LocalVar {
        let name = format!("havoc${}", self.fresh_variables.len());
        let var = polymorphic_vir::LocalVar {
            name,
            typ: translate_type(self.encoder, typ.clone()),
        };
        self.fresh_variables.push(var.clone());
        var
    }
}

impl StmtFolder for Purifier<'_, '_, '_> {
    fn fold_expr(&mut self, expr: polymorphic_vir::Expr) -> polymorphic_vir::Expr {
        ExprFolder::fold(self, expr)
    }
    fn fold_method_call(
        &mut self,
        name: String,
        args: Vec<polymorphic_vir::Expr>,
        targets: Vec<polymorphic_vir::LocalVar>
    ) -> polymorphic_vir::Stmt {
        match targets.as_slice() {
            [local_var] if self.vars.contains(&local_var.name) => {
                return polymorphic_vir::Stmt::Assign( polymorphic_vir::Assign {
                    target: polymorphic_vir::LocalVar {
                        name: local_var.name.clone(),
                        typ: translate_type(self.encoder, local_var.typ.clone()),
                    }.into(),
                    source: self.fresh_variable(&local_var.typ).into(),
                    kind: polymorphic_vir::AssignKind::Ghost,
                });
            }
            _ => {}
        }
        polymorphic_vir::Stmt::MethodCall( polymorphic_vir::MethodCall {
            method_name: name,
            arguments: args.into_iter().map(|e| self.fold_expr(e)).collect(),
            targets
        })
    }
    fn fold_assign(
        &mut self,
        target: polymorphic_vir::Expr,
        source: polymorphic_vir::Expr,
        kind: polymorphic_vir::AssignKind,
    ) -> polymorphic_vir::Stmt {
        let mut target = self.fold_expr(target);
        let mut source = self.fold_expr(source);
        match (&mut target, &mut source) {
            (polymorphic_vir::Expr::Local( polymorphic_vir::Local {variable: target_var, ..} ), polymorphic_vir::Expr::Local( polymorphic_vir::Local {variable: source_var, ..} ))
                    if (target_var.name.starts_with("_preserve") ||
                        target_var.name.starts_with("_old$")
                        ) && self.vars.contains(&source_var.name) => {
                target_var.typ = translate_type(self.encoder, source_var.typ.clone());
                self.change_var_types.insert(target_var.name.clone(), source_var.typ.clone());
            }
            _ => {}
        }
        polymorphic_vir::Stmt::Assign( polymorphic_vir::Assign {target, source, kind} )
    }
}

impl ExprFolder for Purifier<'_, '_, '_> {
    fn fold_field_access_predicate(
        &mut self,
        receiver: Box<polymorphic_vir::Expr>,
        perm_amount: polymorphic_vir::PermAmount,
        pos: polymorphic_vir::Position
    ) -> polymorphic_vir::Expr {
        match &*receiver {
            polymorphic_vir::Expr::Field( polymorphic_vir::FieldExpr {base: box polymorphic_vir::Expr::Local ( polymorphic_vir::Local {variable: local_var, ..} ), ..} )
                    if self.vars.contains(&local_var.name) => {
                return true.into();
            }
            _ => {}
        }
        polymorphic_vir::Expr::FieldAccessPredicate( polymorphic_vir::FieldAccessPredicate {
            base: receiver,
            permission: perm_amount,
            position: pos,
        })
    }
    fn fold_predicate_access_predicate(
        &mut self,
        typ: polymorphic_vir::Type,
        arg: Box<polymorphic_vir::Expr>,
        perm_amount: polymorphic_vir::PermAmount,
        pos: polymorphic_vir::Position
    ) -> polymorphic_vir::Expr {
        let arg = self.fold_boxed(arg);
        match &*arg {
            polymorphic_vir::Expr::Local( polymorphic_vir::Local {variable: local_var, ..})
                    if self.vars.contains(&local_var.name) ||
                        self.change_var_types.contains_key(&local_var.name) => {
                return true.into();
            }
            _ => {}
        }
        polymorphic_vir::Expr::PredicateAccessPredicate( polymorphic_vir::PredicateAccessPredicate {
            predicate_type: typ,
            argument: arg,
            permission: perm_amount,
            position: pos,
        })
    }
    fn fold_labelled_old(
        &mut self,
        label: String,
        body: Box<polymorphic_vir::Expr>,
        pos: polymorphic_vir::Position
    ) -> polymorphic_vir::Expr {
        let body = self.fold_boxed(body);
        if !body.is_heap_dependent() {
            return *body;
        }
        polymorphic_vir::Expr::LabelledOld( polymorphic_vir::LabelledOld {
            label,
            base: body,
            position: pos,
        })
    }
    fn fold_local(
        &mut self,
        mut var: polymorphic_vir::LocalVar,
        pos: polymorphic_vir::Position,
    ) -> polymorphic_vir::Expr {
        if let Some(new_type) = self.change_var_types.get(&var.name) {
            var.typ = translate_type(self.encoder, new_type.clone());
        }
        polymorphic_vir::Expr::Local( polymorphic_vir::Local {
            variable: var,
            position: pos,
        })
    }
    fn fold_field(
        &mut self,
        receiver: Box<polymorphic_vir::Expr>,
        field: polymorphic_vir::Field,
        pos: polymorphic_vir::Position,
    ) -> polymorphic_vir::Expr {
        match receiver {
            box polymorphic_vir::Expr::Local( polymorphic_vir::Local {variable: local_var, ..} ) if self.vars.contains(&local_var.name) => {
                return polymorphic_vir::LocalVar {
                    name: local_var.name,
                    typ: translate_type(self.encoder, local_var.typ),
                }.into();
            }
            _ => {}
        }
        polymorphic_vir::Expr::Field( polymorphic_vir::FieldExpr {
            base: receiver,
            field,
            position: pos,
        })
    }
    fn fold_func_app(
        &mut self,
        name: String,
        args: Vec<polymorphic_vir::Expr>,
        formal_args: Vec<polymorphic_vir::LocalVar>,
        return_type: polymorphic_vir::Type,
        pos: polymorphic_vir::Position
    ) -> polymorphic_vir::Expr {
        let args: Vec<_> = args.into_iter().map(|e| ExprFolder::fold(self, e)).collect();
        match args.as_slice() {
            [polymorphic_vir::Expr::Local( polymorphic_vir::Local {variable: local_var, position: local_pos} )] => {
                if self.vars.contains(&local_var.name) ||
                        self.change_var_types.contains_key(&local_var.name) {
                    if name.starts_with("snap$") {
                        return polymorphic_vir::Expr::Local( polymorphic_vir::Local {
                            variable: local_var.clone(),
                            position: local_pos.clone(),
                        });
                    }
                    if name.ends_with("$$discriminant$$") {
                        let predicate_name = formal_args[0].typ.name();
                        let domain_name = format!("Snap${}", predicate_name);
                        let arg_dom_expr = polymorphic_vir::Expr::Local( polymorphic_vir::Local {
                            variable: local_var.clone(),
                            position: local_pos.clone(),
                        });
                        let discriminant_func = polymorphic_vir::DomainFunc {
                            name: "discriminant$".to_string(),
                            formal_args: vec![local_var.clone()],
                            return_type: polymorphic_vir::Type::Int,
                            unique: false,
                            domain_name: domain_name.to_string(),
                        };
                        return discriminant_func.apply(vec![arg_dom_expr.clone()]);
                    }
                }
            }
            _ => {}
        }
        polymorphic_vir::Expr::FuncApp( polymorphic_vir::FuncApp {
            function_name: name,
            arguments: args,
            formal_arguments: formal_args,
            return_type,
            position: pos
        })
    }
}
