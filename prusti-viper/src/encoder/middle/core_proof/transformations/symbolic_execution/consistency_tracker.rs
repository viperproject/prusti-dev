//! Tracks the values of boolean variables to catch when we enter an
//! inconsistent state.

use crate::encoder::{
    errors::SpannedEncodingResult, middle::core_proof::snapshots::SnapshotDomainInfo,
};
use std::collections::BTreeMap;
use vir_crate::{
    common::expression::SyntacticEvaluation,
    low::{self as vir_low, operations::ty::Typed},
};

#[derive(Clone)]
pub(super) struct ConsistencyTracker {
    /// The current values of the boolean variables.
    variables: BTreeMap<String, bool>,
    is_inconsistent: bool,
    bool_type: vir_low::Type,
    bool_domain_info: SnapshotDomainInfo,
}

impl ConsistencyTracker {
    pub(super) fn new(bool_type: vir_low::Type, bool_domain_info: SnapshotDomainInfo) -> Self {
        Self {
            variables: BTreeMap::new(),
            is_inconsistent: false,
            bool_type,
            bool_domain_info,
        }
    }

    fn is_bool_constructor_name(&self, function_name: &str) -> bool {
        if let Some(constant_constructor_name) = &self.bool_domain_info.constant_constructor_name {
            function_name == constant_constructor_name
        } else {
            false
        }
    }

    fn is_bool_destructor_name(&self, function_name: &str) -> bool {
        if let Some(constant_destructor_name) = &self.bool_domain_info.constant_destructor_name {
            function_name == constant_destructor_name
        } else {
            false
        }
    }

    pub(super) fn is_inconsistent(&self) -> SpannedEncodingResult<bool> {
        Ok(self.is_inconsistent)
    }

    pub(super) fn try_assume(&mut self, term: &vir_low::Expression) -> SpannedEncodingResult<()> {
        assert!(term.get_type().is_bool(), "term: {term} {term:?}");
        if term.is_false() {
            self.is_inconsistent = true;
        } else if Some(false) == self.try_eval(term)? {
            self.is_inconsistent = true;
        } else {
            self.try_assume_value(term, true)?;
        }
        Ok(())
    }

    fn try_assume_value(
        &mut self,
        term: &vir_low::Expression,
        value: bool,
    ) -> SpannedEncodingResult<()> {
        match term {
            vir_low::Expression::Local(local) => {
                self.set_variable_bool(&local.variable.name, value)?;
            }
            vir_low::Expression::UnaryOp(vir_low::UnaryOp {
                op_kind: vir_low::UnaryOpKind::Not,
                argument,
                ..
            }) => {
                self.try_assume_value(argument, !value)?;
            }
            vir_low::Expression::BinaryOp(vir_low::BinaryOp {
                op_kind: vir_low::BinaryOpKind::EqCmp,
                left,
                right,
                ..
            }) => {
                self.try_assume_equal(left, right)?;
            }
            vir_low::Expression::DomainFuncApp(domain_function_app)
                if self.is_bool_destructor_name(&domain_function_app.function_name) =>
            {
                assert!(domain_function_app.arguments.len() == 1);
                self.try_assume_value(&domain_function_app.arguments[0], value)?;
            }
            _ => (),
        }
        Ok(())
    }

    pub(super) fn try_assume_equal(
        &mut self,
        left: &vir_low::Expression,
        right: &vir_low::Expression,
    ) -> SpannedEncodingResult<()> {
        if !(left.get_type().is_bool() || left.get_type() == &self.bool_type) {
            return Ok(());
        }
        match (left, right) {
            (vir_low::Expression::Local(local), vir_low::Expression::Constant(constant))
            | (vir_low::Expression::Constant(constant), vir_low::Expression::Local(local)) => {
                self.set_variable(local, constant)?;
            }
            (vir_low::Expression::Local(left_local), vir_low::Expression::Local(right_local)) => {
                if let Some(left_value) = self.variables.get(&left_local.variable.name) {
                    self.set_variable_bool(&right_local.variable.name, *left_value)?;
                }
                if let Some(right_value) = self.variables.get(&right_local.variable.name) {
                    self.set_variable_bool(&left_local.variable.name, *right_value)?;
                }
            }
            (
                vir_low::Expression::Local(local),
                vir_low::Expression::DomainFuncApp(domain_function_app),
            )
            | (
                vir_low::Expression::DomainFuncApp(domain_function_app),
                vir_low::Expression::Local(local),
            ) if self.is_bool_constructor_name(&domain_function_app.function_name) => {
                assert!(domain_function_app.arguments.len() == 1);
                if let vir_low::Expression::Constant(constant) = &domain_function_app.arguments[0] {
                    self.set_variable(local, constant)?;
                }
            }
            _ => {}
        }
        Ok(())
    }

    fn set_variable(
        &mut self,
        local: &vir_low::Local,
        constant: &vir_low::Constant,
    ) -> SpannedEncodingResult<()> {
        let vir_low::ConstantValue::Bool(value) = &constant.value else {
            unreachable!("local: {local:?} constant: {constant:?}");
        };
        self.set_variable_bool(&local.variable.name, *value)?;
        Ok(())
    }

    fn set_variable_bool(&mut self, variable_name: &str, value: bool) -> SpannedEncodingResult<()> {
        if let Some(current_value) = self.variables.get(variable_name) {
            if value != *current_value {
                self.is_inconsistent = true;
            }
        } else {
            self.variables.insert(variable_name.to_string(), value);
        }
        Ok(())
    }

    fn try_eval(&self, term: &vir_low::Expression) -> SpannedEncodingResult<Option<bool>> {
        let result = match term {
            vir_low::Expression::Local(local) => self.variables.get(&local.variable.name).cloned(),
            vir_low::Expression::Constant(constant) => match constant.value {
                vir_low::ConstantValue::Bool(value) => Some(value),
                _ => None,
            },
            vir_low::Expression::UnaryOp(vir_low::UnaryOp {
                op_kind: vir_low::UnaryOpKind::Not,
                argument,
                ..
            }) => self.try_eval(argument)?.map(|value| !value),
            vir_low::Expression::BinaryOp(vir_low::BinaryOp {
                op_kind: vir_low::BinaryOpKind::And,
                left,
                right,
                ..
            }) => match (self.try_eval(left)?, self.try_eval(right)?) {
                (Some(left_value), Some(right_value)) => Some(left_value && right_value),
                (Some(false), _) | (_, Some(false)) => Some(false),
                _ => None,
            },
            vir_low::Expression::BinaryOp(vir_low::BinaryOp {
                op_kind: vir_low::BinaryOpKind::Or,
                left,
                right,
                ..
            }) => match (self.try_eval(left)?, self.try_eval(right)?) {
                (Some(left_value), Some(right_value)) => Some(left_value || right_value),
                (Some(true), _) | (_, Some(true)) => Some(true),
                _ => None,
            },
            _ => None,
        };
        Ok(result)
    }
}
