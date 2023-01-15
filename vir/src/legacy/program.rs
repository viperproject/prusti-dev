use crate::legacy::{ast::*, cfg::CfgMethod};

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize, Hash, Eq, PartialEq)]
pub struct Program {
    pub name: String,
    pub domains: Vec<Domain>,
    pub backend_types: Vec<BackendType>,
    pub fields: Vec<Field>,
    pub builtin_methods: Vec<BodylessMethod>,
    pub methods: Vec<CfgMethod>,
    pub functions: Vec<Function>,
    pub viper_predicates: Vec<Predicate>,
}

impl Program {
    /// Visit each expression.
    /// Note: sub-expressions of expressions will not be visited.
    pub fn visit_expressions<F: FnMut(&Expr)>(&self, mut visitor: F) {
        for method in &self.methods {
            method.walk_expressions(&mut visitor);
        }
        for function in &self.functions {
            function.visit_expressions(&mut visitor);
        }
        for predicate in &self.viper_predicates {
            predicate.visit_expressions(&mut visitor);
        }
    }

    /// Mutably visit each expression.
    /// Note: sub-expressions of expressions will not be visited.
    pub fn visit_expressions_mut<F: FnMut(&mut Expr)>(&mut self, mut visitor: F) {
        for method in self.methods.iter_mut() {
            method.walk_expressions_mut(&mut visitor);
        }
        for function in self.functions.iter_mut() {
            function.visit_expressions_mut(&mut visitor);
        }
        for predicate in self.viper_predicates.iter_mut() {
            predicate.visit_expressions_mut(&mut visitor);
        }
    }

    /// Visit each statement.
    pub fn visit_statements<F: FnMut(&Stmt)>(&self, mut visitor: F) {
        for method in &self.methods {
            method.walk_statements(&mut visitor);
        }
    }

    /// Mutably visit each statement.
    pub fn visit_statements_mut<F: FnMut(&mut Stmt)>(&mut self, mut visitor: F) {
        for method in self.methods.iter_mut() {
            method.walk_statements_mut(&mut visitor);
        }
    }

    /// Visit each position.
    pub fn visit_positions<F: FnMut(&Position)>(&self, mut visitor: F) {
        self.visit_expressions(|e| e.visit_positions(&mut visitor));
        self.visit_statements(|s| s.visit_positions(&mut visitor));
    }

    /// Mutably visit each position.
    pub fn visit_positions_mut<F: FnMut(&mut Position)>(&mut self, mut visitor: F) {
        self.visit_expressions_mut(|e| e.visit_positions_mut(&mut visitor));
        self.visit_statements_mut(|s| s.visit_positions_mut(&mut visitor));
    }
}
