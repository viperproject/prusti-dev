use super::super::{
    ast::expression::{Expression, Trigger},
    cfg::{BasicBlock, Label, ProcedureDecl},
    domain::{DomainAxiomDecl, DomainDecl, DomainFunctionDecl, DomainRewriteRuleDecl},
};
use crate::common::{
    cfg::Cfg,
    expression::{BinaryOperationHelpers, QuantifierHelpers},
};
use std::collections::BTreeMap;

impl DomainRewriteRuleDecl {
    pub fn convert_into_axiom(&self) -> DomainAxiomDecl {
        let triggers = if let Some(triggers) = &self.triggers {
            triggers.clone()
        } else {
            vec![Trigger::new(vec![self.source.clone()])]
        };
        let body = Expression::forall(
            self.variables.clone(),
            triggers,
            Expression::equals(self.source.clone(), self.target.clone()),
        );
        DomainAxiomDecl {
            comment: self.comment.clone(),
            name: self.name.clone(),
            body,
        }
    }
}
