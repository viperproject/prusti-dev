use super::super::ast::{
    expression::Expression,
    position::Position,
    rvalue::{visitors::RvalueWalker, *},
    ty::*,
    variable::*,
};

impl Rvalue {
    pub fn check_no_default_position(&self) {
        struct Checker;
        impl RvalueWalker for Checker {
            fn walk_expression(&mut self, expression: &Expression) {
                expression.check_no_default_position();
            }
        }
        Checker.walk_rvalue(self)
    }
}
