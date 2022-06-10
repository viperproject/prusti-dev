use crate::legacy::{ast::*, cfg::CfgMethod};

#[derive(Debug, Clone, Serialize, Deserialize, Hash, Eq, PartialEq)]
pub struct Program {
    pub name: String,
    pub domains: Vec<Domain>,
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
        self.methods
            .iter()
            .for_each(|m| m.walk_expressions(&mut visitor));
        self.functions
            .iter()
            .for_each(|f| f.visit_expressions(&mut visitor));
        self.viper_predicates
            .iter()
            .for_each(|p| p.visit_expressions(&mut visitor));
    }

    /// Mutably visit each expression.
    /// Note: sub-expressions of expressions will not be visited.
    pub fn visit_expressions_mut<F: FnMut(&mut Expr)>(&mut self, mut visitor: F) {
        self.methods
            .iter_mut()
            .for_each(|m| m.walk_expressions_mut(&mut visitor));
        self.functions
            .iter_mut()
            .for_each(|f| f.visit_expressions_mut(&mut visitor));
        self.viper_predicates
            .iter_mut()
            .for_each(|p| p.visit_expressions_mut(&mut visitor));
    }

    /// Visit each statement.
    pub fn visit_statements<F: FnMut(&Stmt)>(&self, mut visitor: F) {
        self.methods
            .iter()
            .for_each(|m| m.walk_statements(&mut visitor));
    }

    /// Mutably visit each statement.
    pub fn visit_statements_mut<F: FnMut(&mut Stmt)>(&mut self, mut visitor: F) {
        self.methods
            .iter_mut()
            .for_each(|m| m.walk_statements_mut(&mut visitor));
    }

    /// Visit each position.
    pub fn visit_positions<F: FnMut(&Position)>(&self, mut visitor: F) {
        self.visit_expressions(|e| e.visit_positions(&mut visitor));
        self.visit_statements(|s| s.pos().into_iter().for_each(&mut visitor));
    }

    /// Mutably visit each position.
    pub fn visit_positions_mut<F: FnMut(&mut Position)>(&mut self, mut visitor: F) {
        self.visit_expressions_mut(|e| e.visit_positions_mut(&mut visitor));
        self.visit_statements_mut(|s| s.pos_mut().into_iter().for_each(&mut visitor));
    }
}
