use rustc_hash::FxHashMap;
use vir_crate::{
    common::{expression::ExpressionIterator, graphviz::ToGraphviz},
    low::{self as vir_low},
};

pub(in super::super) fn desugar_method_calls(
    source_filename: &str,
    mut program: vir_low::Program,
) -> vir_low::Program {
    let mut procedures = Vec::new();
    let methods: FxHashMap<_, _> = program
        .methods
        .iter()
        .map(|procedure| (&procedure.name, procedure))
        .collect();
    for procedure in std::mem::take(&mut program.procedures) {
        let procedure = desugar_method_calls_for_procedure(source_filename, &methods, procedure);
        procedures.push(procedure);
    }
    program.procedures = procedures;
    program
}

pub(in super::super) fn desugar_method_calls_for_procedure(
    source_filename: &str,
    methods: &FxHashMap<&String, &vir_low::MethodDecl>,
    mut procedure: vir_low::ProcedureDecl,
) -> vir_low::ProcedureDecl {
    let mut label_counter = 0;
    for block in procedure.basic_blocks.values_mut() {
        block.statements = desugar_method_calls_for_statements(
            methods,
            &mut label_counter,
            &mut procedure.custom_labels,
            std::mem::take(&mut block.statements),
        );
    }
    if prusti_common::config::dump_debug_info() {
        prusti_common::report::log::report_with_writer(
            "graphviz_method_vir_low_after_desugar_method_calls",
            format!("{}.{}.dot", source_filename, procedure.name),
            |writer| procedure.to_graphviz(writer).unwrap(),
        );
    }
    procedure
}

pub(in super::super) fn desugar_method_calls_for_statements(
    methods: &FxHashMap<&String, &vir_low::MethodDecl>,
    label_counter: &mut usize,
    custom_labels: &mut Vec<vir_low::Label>,
    original_statements: Vec<vir_low::Statement>,
) -> Vec<vir_low::Statement> {
    let mut statements = Vec::new();
    for statement in original_statements {
        match statement {
            vir_low::Statement::MethodCall(statement) => {
                statements.push(vir_low::Statement::comment(format!("{statement}")));
                let old_label = format!("method_call_label${label_counter}");
                custom_labels.push(vir_low::Label::new(old_label.clone()));
                *label_counter += 1;
                statements.push(vir_low::Statement::label(
                    old_label.clone(),
                    statement.position,
                ));
                let method = methods.get(&statement.method_name).unwrap_or_else(|| {
                    panic!(
                        "Method `{}` not found in the list of methods: {:?}",
                        statement.method_name,
                        methods.keys()
                    )
                });
                let arguments: Vec<_> = statement
                    .arguments
                    .iter()
                    .map(|argument| {
                        vir_low::Expression::labelled_old(
                            Some(old_label.clone()),
                            argument.clone(),
                            statement.position,
                        )
                    })
                    .collect();
                let mut replacements = method.parameters.iter().zip(arguments.iter()).collect();
                let assertion = method
                    .pres
                    .clone()
                    .into_iter()
                    .conjoin()
                    .substitute_variables(&replacements)
                    .remove_unnecessary_old();
                statements.push(
                    vir_low::Statement::exhale_no_pos(assertion)
                        .set_default_position(statement.position),
                );
                replacements.extend(method.targets.iter().zip(statement.targets.iter()));
                let assertion = method
                    .posts
                    .clone()
                    .into_iter()
                    .conjoin()
                    .substitute_variables(&replacements)
                    .set_old_label(&old_label)
                    .remove_unnecessary_old();
                statements.push(
                    vir_low::Statement::inhale_no_pos(assertion)
                        .set_default_position(statement.position),
                );
            }
            vir_low::Statement::Conditional(mut statement) => {
                statement.then_branch = desugar_method_calls_for_statements(
                    methods,
                    label_counter,
                    custom_labels,
                    std::mem::take(&mut statement.then_branch),
                );
                statement.else_branch = desugar_method_calls_for_statements(
                    methods,
                    label_counter,
                    custom_labels,
                    std::mem::take(&mut statement.else_branch),
                );
                statements.push(vir_low::Statement::Conditional(statement));
            }
            _ => {
                statements.push(statement);
            }
        }
    }
    statements
}
