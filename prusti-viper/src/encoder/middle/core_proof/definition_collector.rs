use std::collections::BTreeMap;

use vir_crate::{
    common::identifier::WithIdentifier,
    middle::{
        self as vir_mid, ast::statement::visitors::StatementWalker, visitors::ExpressionWalker,
    },
};

pub(super) fn collect_predicates(
    procedure: &vir_mid::cfg::ProcedureDecl,
) -> Vec<vir_mid::Predicate> {
    let mut collector = PredicateCollector::default();
    procedure.walk(&mut collector);
    collector.predicates.into_values().collect()
}

#[derive(Default)]
struct PredicateCollector {
    predicates: BTreeMap<String, vir_mid::Predicate>,
}

impl StatementWalker for PredicateCollector {
    fn walk_predicate(&mut self, predicate: &vir_mid::Predicate) {
        self.predicates
            .insert(predicate.get_identifier(), predicate.clone());
    }
}

impl ExpressionWalker for PredicateCollector {}

pub(super) fn collect_functions(
    procedure: &vir_mid::cfg::ProcedureDecl,
) -> Vec<vir_mid::FunctionDecl> {
    let mut collector = FunctionCollector::default();
    procedure.walk_expressions(&mut collector);
    collector.functions.into_values().collect()
}

#[derive(Default)]
struct FunctionCollector {
    functions: BTreeMap<String, vir_mid::FunctionDecl>,
}

impl ExpressionWalker for FunctionCollector {
    fn walk_func_app(&mut self, func_app: &vir_mid::expression::FuncApp) {
        let identifier = func_app.get_identifier();
        let entry = self.functions.entry(identifier);
        entry.or_insert_with(|| {
            vir_mid::FunctionDecl {
                name: func_app.function_name.clone(),
                type_arguments: func_app.type_arguments.clone(),
                parameters: func_app.parameters.clone(),
                return_type: func_app.return_type.clone(),
                pres: Vec::new(),  // FIXME
                posts: Vec::new(), // FIXME
                body: None,        // FIXME
            }
        });
    }
}
