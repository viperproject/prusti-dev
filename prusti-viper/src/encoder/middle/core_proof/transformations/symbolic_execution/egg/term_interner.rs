use super::language::ExpressionLanguage;
use crate::encoder::errors::SpannedEncodingResult;
use egg::{EGraph, Id, RecExpr, Symbol};
use rustc_hash::FxHashSet;
use std::collections::BTreeMap;
use vir_crate::low::{self as vir_low};

pub(super) trait TermInterner {
    fn try_intern_term(
        &mut self,
        term: &vir_low::Expression,
        true_id: Id,
        false_id: Id,
    ) -> SpannedEncodingResult<Option<Id>>;

    fn intern_term(
        &mut self,
        term: &vir_low::Expression,
        true_id: Id,
        false_id: Id,
    ) -> SpannedEncodingResult<Id>;

    fn intern_pattern(
        &mut self,
        term: &vir_low::Expression,
        true_id: Id,
        false_id: Id,
        variables: &BTreeMap<String, Id>,
    ) -> SpannedEncodingResult<Id>;

    fn add(&mut self, term: ExpressionLanguage) -> Id;
}

impl TermInterner for EGraph<ExpressionLanguage, ()> {
    fn try_intern_term(
        &mut self,
        term: &vir_low::Expression,
        true_id: Id,
        false_id: Id,
    ) -> SpannedEncodingResult<Option<Id>> {
        Ok(try_intern_term_rec(
            self,
            true_id,
            false_id,
            &BTreeMap::new(),
            &mut Vec::new(),
            term,
        ))
    }

    fn intern_term(
        &mut self,
        term: &vir_low::Expression,
        true_id: Id,
        false_id: Id,
    ) -> SpannedEncodingResult<Id> {
        Ok(try_intern_term_rec(
            self,
            true_id,
            false_id,
            &BTreeMap::new(),
            &mut Vec::new(),
            term,
        )
        .unwrap_or_else(|| panic!("Failed to intern term: {term}")))
    }

    fn intern_pattern(
        &mut self,
        term: &vir_low::Expression,
        true_id: Id,
        false_id: Id,
        variables: &BTreeMap<String, Id>,
    ) -> SpannedEncodingResult<Id> {
        Ok(
            try_intern_term_rec(self, true_id, false_id, variables, &mut Vec::new(), term)
                .unwrap_or_else(|| panic!("Failed to intern term: {term}")),
        )
    }

    fn add(&mut self, term: ExpressionLanguage) -> Id {
        self.add(term)
    }
}

impl TermInterner for RecExpr<egg::ENodeOrVar<ExpressionLanguage>> {
    fn try_intern_term(
        &mut self,
        term: &vir_low::Expression,
        true_id: Id,
        false_id: Id,
    ) -> SpannedEncodingResult<Option<Id>> {
        Ok(try_intern_term_rec(
            self,
            true_id,
            false_id,
            &BTreeMap::new(),
            &mut Vec::new(),
            term,
        ))
    }

    fn intern_term(
        &mut self,
        term: &vir_low::Expression,
        true_id: Id,
        false_id: Id,
    ) -> SpannedEncodingResult<Id> {
        Ok(try_intern_term_rec(
            self,
            true_id,
            false_id,
            &BTreeMap::new(),
            &mut Vec::new(),
            term,
        )
        .unwrap_or_else(|| panic!("Failed to intern term: {term}")))
    }

    fn intern_pattern(
        &mut self,
        term: &vir_low::Expression,
        true_id: Id,
        false_id: Id,
        variables: &BTreeMap<String, Id>,
    ) -> SpannedEncodingResult<Id> {
        Ok(
            try_intern_term_rec(self, true_id, false_id, variables, &mut Vec::new(), term)
                .unwrap_or_else(|| panic!("Failed to intern term: {term}")),
        )
    }

    fn add(&mut self, term: ExpressionLanguage) -> Id {
        self.add(egg::ENodeOrVar::ENode(term))
    }
}

/// This method must be called only through `intern_term` that checks its
/// precondition. That is the reason why this method is private and not part of
/// `TermInterner`.
fn try_intern_term_rec(
    egraph: &mut impl TermInterner,
    true_id: Id,
    false_id: Id,
    variables: &BTreeMap<String, Id>,
    bound_variables: &mut Vec<FxHashSet<String>>,
    term: &vir_low::Expression,
) -> Option<Id> {
    let id = match term {
        vir_low::Expression::Local(expression) => {
            for frame in bound_variables {
                if frame.contains(&expression.variable.name) {
                    return None;
                }
            }
            if let Some(variable_id) = variables.get(&expression.variable.name) {
                *variable_id
            } else {
                let symbol = Symbol::from(&expression.variable.name);
                egraph.add(ExpressionLanguage::Variable(symbol))
            }
        }
        vir_low::Expression::Constant(expression) => match &expression.value {
            vir_low::ConstantValue::Bool(true) => true_id,
            vir_low::ConstantValue::Bool(false) => false_id,
            vir_low::ConstantValue::Int(value) => egraph.add(ExpressionLanguage::Int(*value)),
            vir_low::ConstantValue::BigInt(value) => {
                if let Ok(value_int) = std::str::FromStr::from_str(value) {
                    egraph.add(ExpressionLanguage::Int(value_int))
                } else {
                    egraph.add(ExpressionLanguage::BigInt(Symbol::from(value)))
                }
            }
        },
        vir_low::Expression::UnaryOp(expression) => {
            let operand_id = try_intern_term_rec(
                egraph,
                true_id,
                false_id,
                variables,
                bound_variables,
                &expression.argument,
            )?;
            match expression.op_kind {
                vir_low::UnaryOpKind::Not => egraph.add(ExpressionLanguage::Not(operand_id)),
                vir_low::UnaryOpKind::Minus => egraph.add(ExpressionLanguage::Minus(operand_id)),
            }
        }
        vir_low::Expression::BinaryOp(expression) => {
            let left_id = try_intern_term_rec(
                egraph,
                true_id,
                false_id,
                variables,
                bound_variables,
                &expression.left,
            )?;
            let right_id = try_intern_term_rec(
                egraph,
                true_id,
                false_id,
                variables,
                bound_variables,
                &expression.right,
            )?;
            match expression.op_kind {
                vir_low::BinaryOpKind::EqCmp => {
                    egraph.add(ExpressionLanguage::EqCmp([left_id, right_id]))
                }
                vir_low::BinaryOpKind::NeCmp => {
                    egraph.add(ExpressionLanguage::NeCmp([left_id, right_id]))
                }
                vir_low::BinaryOpKind::GtCmp => {
                    egraph.add(ExpressionLanguage::GtCmp([left_id, right_id]))
                }
                vir_low::BinaryOpKind::GeCmp => {
                    egraph.add(ExpressionLanguage::GeCmp([left_id, right_id]))
                }
                vir_low::BinaryOpKind::LtCmp => {
                    egraph.add(ExpressionLanguage::LtCmp([left_id, right_id]))
                }
                vir_low::BinaryOpKind::LeCmp => {
                    egraph.add(ExpressionLanguage::LeCmp([left_id, right_id]))
                }
                vir_low::BinaryOpKind::Add => {
                    egraph.add(ExpressionLanguage::Add([left_id, right_id]))
                }
                vir_low::BinaryOpKind::Sub => {
                    egraph.add(ExpressionLanguage::Sub([left_id, right_id]))
                }
                vir_low::BinaryOpKind::Mul => {
                    egraph.add(ExpressionLanguage::Mul([left_id, right_id]))
                }
                vir_low::BinaryOpKind::Div => {
                    egraph.add(ExpressionLanguage::Div([left_id, right_id]))
                }
                vir_low::BinaryOpKind::Mod => {
                    egraph.add(ExpressionLanguage::Mod([left_id, right_id]))
                }
                vir_low::BinaryOpKind::And => {
                    egraph.add(ExpressionLanguage::And([left_id, right_id]))
                }
                vir_low::BinaryOpKind::Or => {
                    egraph.add(ExpressionLanguage::Or([left_id, right_id]))
                }
                vir_low::BinaryOpKind::Implies => {
                    egraph.add(ExpressionLanguage::Implies([left_id, right_id]))
                }
            }
        }
        vir_low::Expression::PermBinaryOp(expression) => {
            let left_id = try_intern_term_rec(
                egraph,
                true_id,
                false_id,
                variables,
                bound_variables,
                &expression.left,
            )?;
            let right_id = try_intern_term_rec(
                egraph,
                true_id,
                false_id,
                variables,
                bound_variables,
                &expression.right,
            )?;
            match expression.op_kind {
                vir_low::expression::PermBinaryOpKind::Add => {
                    egraph.add(ExpressionLanguage::Add([left_id, right_id]))
                }
                vir_low::expression::PermBinaryOpKind::Sub => {
                    egraph.add(ExpressionLanguage::Sub([left_id, right_id]))
                }
                vir_low::expression::PermBinaryOpKind::Mul => {
                    egraph.add(ExpressionLanguage::Mul([left_id, right_id]))
                }
                vir_low::expression::PermBinaryOpKind::Div => {
                    egraph.add(ExpressionLanguage::Div([left_id, right_id]))
                }
            }
        }
        vir_low::Expression::ContainerOp(expression) => {
            let mut operands = Vec::new();
            for operand in &expression.operands {
                let operand_id = try_intern_term_rec(
                    egraph,
                    true_id,
                    false_id,
                    variables,
                    bound_variables,
                    operand,
                )?;
                operands.push(operand_id);
            }
            egraph.add(ExpressionLanguage::BuiltinFuncApp(
                Symbol::from(format!("{:?}", expression.kind)),
                operands,
            ))
        }
        vir_low::Expression::DomainFuncApp(expression) => {
            let symbol = Symbol::from(&expression.function_name);
            let arguments = expression
                .arguments
                .iter()
                .map(|argument| {
                    try_intern_term_rec(
                        egraph,
                        true_id,
                        false_id,
                        variables,
                        bound_variables,
                        argument,
                    )
                })
                .collect::<Option<Vec<_>>>()?;
            egraph.add(ExpressionLanguage::FuncApp(symbol, arguments))
        }
        vir_low::Expression::LabelledOld(expression) => try_intern_term_rec(
            egraph,
            true_id,
            false_id,
            variables,
            bound_variables,
            &expression.base,
        )?,
        // FIXME: It does not make sense to intern the contents of these
        // expressions because in the interning table we store only the id of
        // the root.
        vir_low::Expression::Conditional(_)
        | vir_low::Expression::Quantifier(_)
        | vir_low::Expression::LetExpr(_) => {
            return None;
        }
        // vir_low::Expression::Conditional(expression) => {
        //     try_intern_term_rec(egraph, true_id, false_id, variables, bound_variables,&expression.guard)?;
        //     try_intern_term_rec(egraph, true_id, false_id, variables, bound_variables,&expression.then_expr)?;
        //     try_intern_term_rec(egraph, true_id, false_id, variables, bound_variables,&expression.else_expr)?;
        //     return None;
        // }
        // vir_low::Expression::Quantifier(expression) => {
        //     bound_variables.push(expression.variables.iter().map(|variable| variable.name.clone()).collect());
        //     try_intern_term_rec(egraph, true_id, false_id, variables, bound_variables, &expression.body)?;
        //     for trigger in &expression.triggers {
        //         for term in &trigger.terms {
        //             try_intern_term_rec(egraph, true_id, false_id, variables, bound_variables, term)?;
        //         }
        //     }
        //     bound_variables.pop();
        //     return None;
        // }
        // vir_low::Expression::LetExpr(expression) => {
        //     try_intern_term_rec(egraph, true_id, false_id, variables, bound_variables, &expression.def)?;
        //     bound_variables.push(vec![expression.variable.name.clone()].into_iter().collect());
        //     try_intern_term_rec(egraph, true_id, false_id, variables, bound_variables, &expression.body)?;
        //     bound_variables.pop();
        //     return None;
        // }
        vir_low::Expression::MagicWand(_)
        | vir_low::Expression::PredicateAccessPredicate(_)
        | vir_low::Expression::FieldAccessPredicate(_)
        | vir_low::Expression::Unfolding(_)
        | vir_low::Expression::FuncApp(_)
        | vir_low::Expression::InhaleExhale(_)
        | vir_low::Expression::Field(_) => {
            unreachable!("term: {}", term);
        }
    };
    Some(id)
}
