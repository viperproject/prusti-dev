use super::super::ast::{
    expression::{visitors::ExpressionWalker, Expression},
    position::Position,
    ty::*,
    variable::*,
};
use std::collections::BTreeSet;

#[derive(Default)]
pub struct BoundVariableStack {
    stack: Vec<BTreeSet<String>>,
}

impl BoundVariableStack {
    pub fn contains_name(&self, variable_name: &str) -> bool {
        self.stack.iter().any(|set| set.contains(variable_name))
    }

    pub fn contains(&self, variable: &VariableDecl) -> bool {
        self.contains_name(&variable.name)
    }

    pub fn push_names(&mut self, variable_names: BTreeSet<String>) {
        self.stack.push(variable_names);
    }

    pub fn push(&mut self, variables: &[VariableDecl]) {
        self.push_names(
            variables
                .iter()
                .map(|variable| variable.name.clone())
                .collect(),
        )
    }

    pub fn push_single(&mut self, variable: &VariableDecl) {
        self.push_names(std::iter::once(variable.name.clone()).collect())
    }

    pub fn pop_names(&mut self) {
        assert!(self.stack.pop().is_some());
    }

    pub fn pop(&mut self) {
        self.pop_names();
    }

    pub fn expressions_contains_bound_variables(&self, expressions: &[Expression]) -> bool {
        struct Walker<'a> {
            bound_variable_stack: &'a BoundVariableStack,
            contains_bound_variables: bool,
        }
        impl<'a> ExpressionWalker for Walker<'a> {
            fn walk_variable_decl(&mut self, variable: &VariableDecl) {
                if self.bound_variable_stack.contains(variable) {
                    self.contains_bound_variables = true;
                }
            }
        }
        let mut walker = Walker {
            bound_variable_stack: self,
            contains_bound_variables: false,
        };
        for expression in expressions {
            walker.walk_expression(expression);
        }
        walker.contains_bound_variables
    }
}

impl Drop for BoundVariableStack {
    fn drop(&mut self) {
        // Check when not panicking.
        if !std::thread::panicking() {
            assert!(self.stack.is_empty());
        }
    }
}
