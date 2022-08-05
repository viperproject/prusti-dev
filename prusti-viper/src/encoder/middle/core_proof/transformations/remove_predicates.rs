use rustc_hash::FxHashSet;
use vir_crate::low as vir_low;
use vir_low::expression::visitors::ExpressionFolder;

pub(in super::super) fn remove_predicates(
    procedure: &mut vir_low::ProcedureDecl,
    methods: &mut Vec<vir_low::MethodDecl>,
    removed_functions: &FxHashSet<String>,
) {
    let removed_methods = from_methods(methods, removed_functions);
    from_procedure(procedure, &removed_methods, removed_functions);
}

fn from_procedure(
    procedure: &mut vir_low::ProcedureDecl,
    removed_methods: &FxHashSet<String>,
    removed_functions: &FxHashSet<String>,
) {
    for block in &mut procedure.basic_blocks {
        from_statements(&mut block.statements, removed_methods, removed_functions);
    }
}

fn from_methods(
    methods: &mut Vec<vir_low::MethodDecl>,
    removed_functions: &FxHashSet<String>,
) -> FxHashSet<String> {
    let removed_methods = methods
        .drain_filter(|method| match method.kind {
            vir_low::MethodKind::LowMemoryOperation => true,
            vir_low::MethodKind::MirOperation | vir_low::MethodKind::Havoc => false,
        })
        .map(|method| method.name)
        .collect();
    for method in methods {
        method.body = None;
        from_expressions(&mut method.pres, removed_functions);
        from_expressions(&mut method.posts, removed_functions);
    }
    removed_methods
}

fn from_statements(
    statements: &mut Vec<vir_low::Statement>,
    removed_methods: &FxHashSet<String>,
    removed_functions: &FxHashSet<String>,
) {
    let mut remover = PredicateRemover::new(removed_functions);
    let mut sentinel = true.into();
    for statement in std::mem::take(statements) {
        match statement {
            vir_low::Statement::Comment(_)
            | vir_low::Statement::LogEvent(_)
            | vir_low::Statement::Assume(_)
            | vir_low::Statement::Assert(_)
            | vir_low::Statement::Assign(_) => {
                statements.push(statement);
            }
            vir_low::Statement::MethodCall(method) => {
                if !removed_methods.contains(&method.method_name) {
                    statements.push(vir_low::Statement::MethodCall(method));
                }
            }
            vir_low::Statement::Inhale(mut inhale) => {
                sentinel =
                    remover.fold_expression(std::mem::replace(&mut inhale.expression, sentinel));
                std::mem::swap(&mut inhale.expression, &mut sentinel);
                statements.push(vir_low::Statement::Inhale(inhale));
            }
            vir_low::Statement::Exhale(mut exhale) => {
                sentinel =
                    remover.fold_expression(std::mem::replace(&mut exhale.expression, sentinel));
                std::mem::swap(&mut exhale.expression, &mut sentinel);
                statements.push(vir_low::Statement::Exhale(exhale));
            }
            vir_low::Statement::Fold(_)
            | vir_low::Statement::Unfold(_)
            | vir_low::Statement::ApplyMagicWand(_)
            | vir_low::Statement::Conditional(_) => {}
        }
    }
}

fn from_expressions(
    expressions: &mut Vec<vir_low::Expression>,
    removed_functions: &FxHashSet<String>,
) {
    let mut remover = PredicateRemover::new(removed_functions);
    for expression in std::mem::take(expressions) {
        expressions.push(remover.fold_expression(expression));
    }
}

struct PredicateRemover<'a> {
    removed_functions: &'a FxHashSet<String>,
    drop_parent_binary_op: bool,
}

impl<'a> PredicateRemover<'a> {
    fn new(removed_functions: &'a FxHashSet<String>) -> Self {
        Self {
            removed_functions,
            drop_parent_binary_op: false,
        }
    }
}

impl<'a> ExpressionFolder for PredicateRemover<'a> {
    fn fold_predicate_access_predicate_enum(
        &mut self,
        _predicate: vir_low::expression::PredicateAccessPredicate,
    ) -> vir_low::Expression {
        true.into()
    }
    fn fold_func_app(
        &mut self,
        func_app: vir_low::expression::FuncApp,
    ) -> vir_low::expression::FuncApp {
        if self.removed_functions.contains(&func_app.function_name) {
            self.drop_parent_binary_op = true;
        }
        func_app
    }
    fn fold_binary_op_enum(
        &mut self,
        binary_op: vir_low::expression::BinaryOp,
    ) -> vir_low::Expression {
        let binary_op = self.fold_binary_op(binary_op);
        if self.drop_parent_binary_op {
            self.drop_parent_binary_op = false;
            true.into()
        } else {
            vir_low::Expression::BinaryOp(binary_op)
        }
    }
}
