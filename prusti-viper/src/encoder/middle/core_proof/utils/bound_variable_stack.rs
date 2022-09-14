use rustc_hash::FxHashSet;
use vir_crate::{
    low::{
        expression::visitors::ExpressionWalker,
        {self as vir_low},
    },
    middle::{self as vir_mid},
};

#[derive(Default)]
pub(in super::super) struct BoundVariableStack {
    stack: Vec<FxHashSet<String>>,
}

pub(in super::super) trait BoundVariableStackMiddle {
    fn contains(&self, variable: &vir_mid::VariableDecl) -> bool;
    fn push(&mut self, variables: &[vir_mid::VariableDecl]);
    fn pop(&mut self);
}

pub(in super::super) trait BoundVariableStackLow {
    fn contains(&self, variable: &vir_low::VariableDecl) -> bool;
    fn push(&mut self, variables: &[vir_low::VariableDecl]);
    fn pop(&mut self);
    fn expressions_contains_bound_variables(&self, expressions: &[vir_low::Expression]) -> bool;
}

impl BoundVariableStack {
    pub(in super::super) fn contains_name(&self, variable_name: &str) -> bool {
        self.stack.iter().any(|set| set.contains(variable_name))
    }

    pub(in super::super) fn push_names(&mut self, variable_names: FxHashSet<String>) {
        self.stack.push(variable_names);
    }

    pub(in super::super) fn pop_names(&mut self) {
        assert!(self.stack.pop().is_some());
    }
}

impl BoundVariableStackMiddle for BoundVariableStack {
    fn contains(&self, variable: &vir_mid::VariableDecl) -> bool {
        self.contains_name(&variable.name)
    }

    fn push(&mut self, variables: &[vir_mid::VariableDecl]) {
        self.push_names(
            variables
                .iter()
                .map(|variable| variable.name.clone())
                .collect(),
        )
    }

    fn pop(&mut self) {
        self.pop_names();
    }
}

impl BoundVariableStackLow for BoundVariableStack {
    fn contains(&self, variable: &vir_low::VariableDecl) -> bool {
        self.contains_name(&variable.name)
    }

    fn push(&mut self, variables: &[vir_low::VariableDecl]) {
        self.push_names(
            variables
                .iter()
                .map(|variable| variable.name.clone())
                .collect(),
        )
    }

    fn pop(&mut self) {
        self.pop_names();
    }

    fn expressions_contains_bound_variables(&self, expressions: &[vir_low::Expression]) -> bool {
        struct Walker<'a> {
            bound_variable_stack: &'a BoundVariableStack,
            contains_bound_variables: bool,
        }
        impl<'a> ExpressionWalker for Walker<'a> {
            fn walk_variable_decl(&mut self, variable: &vir_low::VariableDecl) {
                if BoundVariableStackLow::contains(self.bound_variable_stack, variable) {
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
