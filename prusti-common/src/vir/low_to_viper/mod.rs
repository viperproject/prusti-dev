use rustc_hash::FxHashMap;
use viper::AstFactory;
use vir::{common::traits::HashWithPosition, low as vir_low};

mod ast;
mod cfg;
mod domain;
mod program;

#[derive(Clone, Default)]
pub struct Context<'v> {
    inside_trigger: bool,
    expression_cache: FxHashMap<u64, viper::Expr<'v>>,
    expression_cache_validation: FxHashMap<u64, vir_low::Expression>,
    statement_cache: FxHashMap<u64, viper::Stmt<'v>>,
    statement_cache_validation: FxHashMap<u64, vir_low::Statement>,
}

impl<'v> Context<'v> {
    pub fn set_inside_trigger(&mut self) -> bool {
        let old_value = self.inside_trigger;
        self.inside_trigger = true;
        old_value
    }

    pub fn reset_inside_trigger(&mut self, old_value: bool) {
        self.inside_trigger = old_value;
    }

    pub fn get_cached_expression(
        &self,
        expression_hash: u64,
        expression: &vir_low::Expression,
    ) -> Option<viper::Expr<'v>> {
        let viper_expression = self.expression_cache.get(&expression_hash).cloned();
        if cfg!(debug_assertions) && viper_expression.is_some() {
            let cached_expression = self
                .expression_cache_validation
                .get(&expression_hash)
                .unwrap();
            assert_eq!(cached_expression, expression);
        }
        viper_expression
    }

    fn cache_expression(
        &mut self,
        expression_hash: u64,
        expression: &vir_low::Expression,
        viper_expression: viper::Expr<'v>,
    ) {
        if cfg!(debug_assertions) {
            assert!(self
                .expression_cache_validation
                .insert(expression_hash, expression.clone())
                .is_none());
        }
        assert!(self
            .expression_cache
            .insert(expression_hash, viper_expression)
            .is_none());
    }

    pub fn get_cached_statement(
        &self,
        statement_hash: u64,
        statement: &vir_low::Statement,
    ) -> Option<viper::Stmt<'v>> {
        let viper_statement = self.statement_cache.get(&statement_hash).cloned();
        if cfg!(debug_assertions) && viper_statement.is_some() {
            let cached_statement = self
                .statement_cache_validation
                .get(&statement_hash)
                .unwrap();
            assert_eq!(cached_statement, statement);
        }
        viper_statement
    }

    fn cache_statement(
        &mut self,
        statement_hash: u64,
        statement: &vir_low::Statement,
        viper_statement: viper::Stmt<'v>,
    ) {
        if cfg!(debug_assertions) {
            assert!(self
                .statement_cache_validation
                .insert(statement_hash, statement.clone())
                .is_none());
        }
        assert!(self
            .statement_cache
            .insert(statement_hash, viper_statement)
            .is_none());
    }
}

pub trait ToViper<'v, T> {
    fn to_viper(&self, context: &mut Context<'v>, ast: &AstFactory<'v>) -> T;
}

pub trait ToViperDecl<'v, T> {
    fn to_viper_decl(&self, context: &mut Context<'v>, ast: &AstFactory<'v>) -> T;
}

pub(super) fn calculate_hash_with_position<T: HashWithPosition>(t: &T) -> u64 {
    let mut s = std::collections::hash_map::DefaultHasher::new();
    HashWithPosition::hash(t, &mut s);
    std::hash::Hasher::finish(&s)
}
