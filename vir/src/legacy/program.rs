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
            .for_each(|m| m.walk_expressions(|e| visitor(e)));
        self.functions
            .iter()
            .for_each(|f| f.visit_expressions(|e| visitor(e)));
        self.viper_predicates
            .iter()
            .for_each(|p| p.visit_expressions(|e| visitor(e)));
    }

    /// Mutably visit each expression.
    /// Note: sub-expressions of expressions will not be visited.
    pub fn visit_expressions_mut<F: FnMut(&mut Expr)>(&mut self, mut visitor: F) {
        self.methods
            .iter_mut()
            .for_each(|m| m.walk_expressions_mut(|e| visitor(e)));
        self.functions
            .iter_mut()
            .for_each(|f| f.visit_expressions_mut(|e| visitor(e)));
        self.viper_predicates
            .iter_mut()
            .for_each(|p| p.visit_expressions_mut(|e| visitor(e)));
    }
}
