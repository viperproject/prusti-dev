use super::super::ast::{
    expression::Expression,
    position::Position,
    predicate::Predicate,
    rvalue::Rvalue,
    statement::{
        visitors::{StatementFolder, StatementWalker},
        *,
    },
};

impl Statement {
    #[must_use]
    pub fn set_default_position(self, new_position: Position) -> Self {
        struct DefaultPositionReplacer {
            new_position: Position,
        }
        impl StatementFolder for DefaultPositionReplacer {
            fn fold_position(&mut self, position: Position) -> Position {
                if position.is_default() {
                    self.new_position
                } else {
                    position
                }
            }
            fn fold_expression(&mut self, expression: Expression) -> Expression {
                expression.set_default_position(self.new_position)
            }
        }
        DefaultPositionReplacer { new_position }.fold_statement(self)
    }
    pub fn check_no_default_position(&self) {
        struct Checker;
        impl StatementWalker for Checker {
            fn walk_position(&mut self, position: &Position) {
                assert!(!position.is_default());
            }
            fn walk_expression(&mut self, expression: &Expression) {
                expression.check_no_default_position();
            }
            fn walk_predicate(&mut self, predicate: &Predicate) {
                predicate.check_no_default_position();
            }
            fn walk_rvalue(&mut self, rvalue: &Rvalue) {
                rvalue.check_no_default_position();
            }
            fn walk_operand(&mut self, operand: &Operand) {
                operand.expression.check_no_default_position();
            }
        }
        Checker.walk_statement(self)
    }
}
