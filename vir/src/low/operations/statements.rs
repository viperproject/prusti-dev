use crate::low::ast::{
    expression::Expression,
    position::Position,
    statement::{visitors::StatementFolder, *},
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
}
