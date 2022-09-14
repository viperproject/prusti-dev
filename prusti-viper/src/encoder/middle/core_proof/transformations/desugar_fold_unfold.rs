use crate::encoder::middle::core_proof::predicates::OwnedPredicateInfo;
use rustc_hash::FxHashMap;
use std::collections::BTreeMap;
use vir_crate::{
    common::graphviz::ToGraphviz,
    low::{self as vir_low, expression::visitors::ExpressionFolder},
};

pub(in super::super) fn desugar_fold_unfold(
    source_filename: &str,
    mut program: vir_low::Program,
    predicates_info: &BTreeMap<String, OwnedPredicateInfo>,
) -> vir_low::Program {
    let predicate_decls = program
        .predicates
        .iter()
        .map(|predicate| (predicate.name.clone(), predicate))
        .collect();
    let function_decls = program
        .functions
        .iter()
        .map(|function| (function.name.clone(), function))
        .collect();
    for procedure in std::mem::take(&mut program.procedures) {
        if prusti_common::config::dump_debug_info() {
            prusti_common::report::log::report_with_writer(
                "graphviz_method_vir_low_before_desugar_fold_unfold",
                format!("{}.{}.dot", source_filename, procedure.name),
                |writer| procedure.to_graphviz(writer).unwrap(),
            );
        }
        let new_procedure = desugar_fold_unfold_in_procedure(
            procedure,
            &predicate_decls,
            &function_decls,
            predicates_info,
        );
        if prusti_common::config::dump_debug_info() {
            prusti_common::report::log::report_with_writer(
                "graphviz_method_vir_low_after_desugar_fold_unfold",
                format!("{}.{}.dot", source_filename, new_procedure.name),
                |writer| new_procedure.to_graphviz(writer).unwrap(),
            );
        }
        program.procedures.push(new_procedure);
    }
    program
}

fn desugar_fold_unfold_in_procedure(
    mut procedure: vir_low::ProcedureDecl,
    predicate_decls: &BTreeMap<String, &vir_low::PredicateDecl>,
    function_decls: &BTreeMap<String, &vir_low::FunctionDecl>,
    predicates_info: &BTreeMap<String, OwnedPredicateInfo>,
) -> vir_low::ProcedureDecl {
    let mut label_counter = 0;
    for block in procedure.basic_blocks.values_mut() {
        desugar_fold_unfold_in_statements(
            std::mem::take(&mut block.statements),
            &mut block.statements,
            &mut procedure.custom_labels,
            &mut label_counter,
            predicate_decls,
            function_decls,
            predicates_info,
        );
    }
    procedure
}

fn desugar_fold_unfold_in_statements(
    original_statements: Vec<vir_low::Statement>,
    new_statements: &mut Vec<vir_low::Statement>,
    custom_labels: &mut Vec<vir_low::Label>,
    label_counter: &mut u32,
    predicate_decls: &BTreeMap<String, &vir_low::PredicateDecl>,
    function_decls: &BTreeMap<String, &vir_low::FunctionDecl>,
    predicates_info: &BTreeMap<String, OwnedPredicateInfo>,
) {
    for statement in original_statements {
        match statement {
            vir_low::Statement::Fold(statement) => {
                new_statements.push(vir_low::Statement::comment(format!("{statement}")));
                let old_label = new_label(
                    new_statements,
                    custom_labels,
                    label_counter,
                    statement.position,
                );
                let predicate = extract_predicate(&statement.expression);
                // assert!(
                //     predicate.permission.is_full_permission(),
                //     "unimplemented: {predicate}"
                // );
                let predicate_info = predicates_info.get(&predicate.name).unwrap();
                let predicate_decl = predicate_decls.get(&predicate.name).unwrap();
                let body = get_predicate_body(&statement.expression, predicate_decls);
                new_statements.push(vir_low::Statement::exhale(body, statement.position));
                new_statements.push(vir_low::Statement::inhale(
                    statement.expression.clone(),
                    statement.position,
                ));
                let (result, snapshot_call) = construct_snapshot_call_replacement(
                    &statement.expression,
                    predicates_info,
                    function_decls,
                );
                let new_state_label = new_label(
                    new_statements,
                    custom_labels,
                    label_counter,
                    statement.position,
                );
                let snapshot_call = vir_low::Expression::labelled_old(
                    Some(new_state_label),
                    snapshot_call,
                    statement.position,
                );
                let mut replacements =
                    create_parameter_replacements(&predicate_decl.parameters, &predicate.arguments);
                replacements.insert(&result, &snapshot_call);
                let mut snapshot_postcondition = Vec::new();
                for assertion in &predicate_info.current_snapshot_function.postconditions {
                    snapshot_postcondition
                        .push(assertion.clone().substitute_variables(&replacements));
                }
                for assertion in &predicate_info.current_snapshot_function.body {
                    let assertion = wrap_heap_dependent_calls_in_old(
                        assertion.clone(),
                        &old_label,
                        statement.position,
                    );
                    snapshot_postcondition
                        .push(assertion.clone().substitute_variables(&replacements));
                }

                for assertion in snapshot_postcondition {
                    new_statements.push(vir_low::Statement::inhale(assertion, statement.position));
                }
            }
            vir_low::Statement::Unfold(statement) => {
                new_statements.push(vir_low::Statement::comment(format!("{statement}")));
                let old_label = new_label(
                    new_statements,
                    custom_labels,
                    label_counter,
                    statement.position,
                );
                let body = get_predicate_body(&statement.expression, predicate_decls);
                let predicate = extract_predicate(&statement.expression);
                // assert!(
                //     predicate.permission.is_full_permission(),
                //     "unimplemented: {predicate}"
                // );
                let predicate_info = predicates_info.get(&predicate.name).unwrap();
                let (result, snapshot_call) = construct_snapshot_call_replacement(
                    &statement.expression,
                    predicates_info,
                    function_decls,
                );
                let snapshot_call = vir_low::Expression::labelled_old(
                    Some(old_label),
                    snapshot_call,
                    statement.position,
                );
                let predicate_decl = predicate_decls.get(&predicate.name).unwrap();
                let mut replacements =
                    create_parameter_replacements(&predicate_decl.parameters, &predicate.arguments);
                replacements.insert(&result, &snapshot_call);
                let mut snapshot_postcondition = Vec::new();
                for assertion in &predicate_info.current_snapshot_function.postconditions {
                    snapshot_postcondition
                        .push(assertion.clone().substitute_variables(&replacements));
                }
                for assertion in &predicate_info.current_snapshot_function.body {
                    snapshot_postcondition
                        .push(assertion.clone().substitute_variables(&replacements));
                }
                new_statements.push(vir_low::Statement::exhale(
                    statement.expression,
                    statement.position,
                ));
                new_statements.push(vir_low::Statement::inhale(body, statement.position));
                for assertion in snapshot_postcondition {
                    new_statements.push(vir_low::Statement::inhale(assertion, statement.position));
                }
            }
            vir_low::Statement::Conditional(mut statement) => {
                desugar_fold_unfold_in_statements(
                    std::mem::take(&mut statement.then_branch),
                    &mut statement.then_branch,
                    custom_labels,
                    label_counter,
                    predicate_decls,
                    function_decls,
                    predicates_info,
                );
                desugar_fold_unfold_in_statements(
                    std::mem::take(&mut statement.else_branch),
                    &mut statement.else_branch,
                    custom_labels,
                    label_counter,
                    predicate_decls,
                    function_decls,
                    predicates_info,
                );
                new_statements.push(vir_low::Statement::Conditional(statement));
            }
            _ => {
                new_statements.push(statement);
            }
        };
    }
}

fn wrap_heap_dependent_calls_in_old(
    expression: vir_low::Expression,
    old_label: &str,
    position: vir_low::Position,
) -> vir_low::Expression {
    struct Wrapper<'a> {
        old_label: &'a str,
        position: vir_low::Position,
    }
    impl<'a> ExpressionFolder for Wrapper<'a> {
        fn fold_func_app_enum(
            &mut self,
            func_app: vir_low::expression::FuncApp,
        ) -> vir_low::Expression {
            let func_app = self.fold_func_app(func_app);
            let expression = vir_low::Expression::FuncApp(func_app);
            vir_low::Expression::labelled_old(
                Some(self.old_label.to_string()),
                expression,
                self.position,
            )
        }
    }
    let mut wrapper = Wrapper {
        old_label,
        position,
    };
    wrapper.fold_expression(expression)
}

fn new_label(
    statements: &mut Vec<vir_low::Statement>,
    custom_labels: &mut Vec<vir_low::Label>,
    label_counter: &mut u32,
    position: vir_low::Position,
) -> String {
    let old_label = format!("fold_unfold_label${label_counter}");
    custom_labels.push(vir_low::Label::new(old_label.clone()));
    *label_counter += 1;
    statements.push(vir_low::Statement::label(old_label.clone(), position));
    old_label
}

fn extract_predicate(
    expression: &vir_low::Expression,
) -> &vir_low::ast::expression::PredicateAccessPredicate {
    let vir_low::Expression::PredicateAccessPredicate(predicate) = &expression else {
        unreachable!("{expression}")
    };
    predicate
}

fn create_parameter_replacements<'a>(
    parameters: &'a [vir_low::VariableDecl],
    arguments: &'a [vir_low::Expression],
) -> FxHashMap<&'a vir_low::VariableDecl, &'a vir_low::Expression> {
    assert_eq!(arguments.len(), parameters.len());
    parameters.iter().zip(arguments.iter()).collect()
}

fn get_predicate_body(
    expression: &vir_low::Expression,
    predicate_decls: &BTreeMap<String, &vir_low::PredicateDecl>,
) -> vir_low::Expression {
    let predicate = extract_predicate(expression);
    let predicate_permission = &predicate.permission;
    let predicate_decl = predicate_decls.get(&predicate.name).unwrap();
    let body = predicate_decl.body.as_ref().unwrap().clone();
    let replacements =
        create_parameter_replacements(&predicate_decl.parameters, &predicate.arguments);
    body.substitute_variables(&replacements)
        .replace_predicate_permissions(predicate_permission)
}

fn construct_snapshot_call_replacement(
    expression: &vir_low::Expression,
    predicates_info: &BTreeMap<String, OwnedPredicateInfo>,
    function_decls: &BTreeMap<String, &vir_low::FunctionDecl>,
) -> (vir_low::VariableDecl, vir_low::Expression) {
    let predicate = extract_predicate(expression);
    let predicate_info = predicates_info.get(&predicate.name).unwrap();
    let snapshot_function_name = &predicate_info.current_snapshot_function.function_name;
    let function_decl = function_decls.get(snapshot_function_name).unwrap();
    assert!(
        function_decl.body.is_none(),
        "Snapshot functions are expected to be bodyless?"
    );
    let call = vir_low::Expression::function_call(
        snapshot_function_name.clone(),
        predicate.arguments.clone(),
        function_decl.return_type.clone(),
    );
    let result = function_decl.result_variable();
    (result, call)
}
