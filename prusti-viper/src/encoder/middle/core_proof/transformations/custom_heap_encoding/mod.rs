use std::collections::BTreeMap;

use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        lowerer::LoweringResult,
        snapshots::{AllVariablesMap, VariableVersionMap},
    },
};
use rustc_hash::FxHashMap;
use vir_crate::{
    common::{
        cfg::Cfg,
        check_mode::CheckMode,
        expression::{
            BinaryOperationHelpers, ExpressionIterator, QuantifierHelpers, UnaryOperationHelpers,
        },
        graphviz::ToGraphviz,
    },
    low::{self as vir_low, operations::ty::Typed},
    middle as vir_mid,
};

pub(in super::super) fn custom_heap_encoding(
    result: &mut LoweringResult,
) -> SpannedEncodingResult<()> {
    // let mut procedures = Vec::new();
    // let mut heap_encoder = HeapEncoder::new(std::mem::take(&mut result.predicates));
    // for mut procedure in std::mem::take(&mut result.procedures) {
    //     let traversal_order = procedure.get_topological_sort();
    //     for label in &traversal_order {
    //         let mut statements = Vec::new();
    //         let block = procedure.basic_blocks.get_mut(label).unwrap();
    //         for statement in std::mem::take(&mut block.statements) {
    //             heap_encoder.encode_statement(&mut statements, statement)?;
    //         }
    //     }
    //     procedure
    //         .locals
    //         .extend(heap_encoder.new_variables.drain(..));
    //     procedures.push(procedure);
    // }
    Ok(())
}

struct HeapEncoder {
    new_variables: Vec<vir_low::VariableDecl>,
    predicates: FxHashMap<String, vir_low::PredicateDecl>,
    ssa_state: vir_low::ssa::SSAState<usize>,
}

impl HeapEncoder {
    fn new(predicates: Vec<vir_low::PredicateDecl>) -> Self {
        Self {
            new_variables: Vec::new(),
            predicates: predicates
                .into_iter()
                .map(|predicate| (predicate.name.clone(), predicate))
                .collect(),
            ssa_state: Default::default(),
        }
    }

    fn encode_statement(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        statement: vir_low::Statement,
    ) -> SpannedEncodingResult<()> {
        match statement {
            vir_low::Statement::Comment(_)
            | vir_low::Statement::LogEvent(_)
            | vir_low::Statement::Assume(_)
            | vir_low::Statement::Assert(_)
            | vir_low::Statement::Assign(_) => {
                statements.push(statement);
            }
            vir_low::Statement::Label(_) => {
                unimplemented!("Save the values of all heap variables");
            }
            vir_low::Statement::Inhale(inhale) => {
                self.encode_expression_inhale(statements, inhale.expression, inhale.position)?;
            }
            vir_low::Statement::Exhale(_) => todo!(),
            vir_low::Statement::Fold(_) => todo!(),
            vir_low::Statement::Unfold(_) => todo!(),
            vir_low::Statement::ApplyMagicWand(_) => {
                unimplemented!("magic wands are not supported yet");
            }
            vir_low::Statement::MethodCall(_) => todo!(),
            vir_low::Statement::Conditional(mut conditional) => {
                let mut then_statements = Vec::new();
                for statement in std::mem::take(&mut conditional.then_branch) {
                    self.encode_statement(&mut then_statements, statement)?;
                }
                let mut else_statements = Vec::new();
                for statement in std::mem::take(&mut conditional.else_branch) {
                    self.encode_statement(&mut else_statements, statement)?;
                }
                statements.push(vir_low::Statement::Conditional(
                    vir_low::ast::statement::Conditional {
                        then_branch: then_statements,
                        else_branch: else_statements,
                        ..conditional
                    },
                ));
            }
        }
        Ok(())
    }

    fn encode_pure_expression(
        &mut self,
        expression: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        Ok(expression)
    }

    fn encode_expression_inhale(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        expression: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        // if expression.is_pure() {
        //     statements.push(vir_low::Statement::assume(self.encode_pure_expression(expression)?, position));
        // } else {
        //     match expression {
        //         vir_low::Expression::PredicateAccessPredicate(expression) => {
        //             let old_permission_mask = self.get_current_permission_mask_for(&expression.name);
        //             let new_permission_mask = self.get_new_permission_mask_for(&expression.name);
        //             let perm_function_name = self.get_perm_function_name_for(&expression.name);
        //             let predicate_parameters = self.get_predicate_parameters_for(&expression.name);
        //             // assume perm<P>(r1, r2, v_new) == perm<P>(r1, r2, v_old) + p
        //             let mut arguments = Vec::new();
        //             for argument in expression.arguments {
        //                 arguments.push(self.encode_pure_expression(argument)?);
        //             }
        //             let mut old_permission_arguments = arguments.clone();
        //             let mut new_permission_arguments = arguments;
        //             old_permission_arguments.push(old_permission_mask);
        //             new_permission_arguments.push(new_permission_mask);
        //             statements.push(vir_low::Statement::assume(
        //                 vir_low::Expression::equals(
        //                     vir_low::Expression::domain_function_call(
        //                         "Perm",
        //                         perm_function_name.clone(),
        //                         new_permission_arguments,
        //                         vir_low::Type::Perm,
        //                     ),
        //                     vir_low::Expression::add(
        //                         vir_low::Expression::domain_function_call(
        //                             "Perm",
        //                             perm_function_name,
        //                             old_permission_arguments,
        //                             vir_low::Type::Perm,
        //                         ),
        //                         *expression.permission,
        //                     ),
        //                 ),
        //                 expression.position,
        //             ));
        //             // assume forall arg1: Ref, arg2: Ref ::
        //             //     {perm<P>(arg1, arg2, v_new)}
        //             //     r1 != arg1 && r2 != arg2 ==>
        //             //     perm<P>(arg1, arg2, v_new) == perm<P>(arg1, arg2, v_old)
        //             let predicate_arguments: Vec<vir_low::Expression> = predicate_parameters
        //                 .iter()
        //                 .map(|parameter| parameter.clone().into())
        //                 .collect();
        //             let old_permission_arguments = predicate_arguments.clone();
        //             let new_permission_arguments = predicate_arguments;
        //             old_permission_arguments.push(old_permission_mask);
        //             new_permission_arguments.push(new_permission_mask);
        //             let perm_new = vir_low::Expression::domain_function_call(
        //                 "Perm",
        //                 perm_function_name.clone(),
        //                 new_permission_arguments,
        //                 vir_low::Type::Perm,
        //             );
        //             let perm_old = vir_low::Expression::domain_function_call(
        //                 "Perm",
        //                 perm_function_name.clone(),
        //                 old_permission_arguments,
        //                 vir_low::Type::Perm,
        //             );
        //             let triggers = vec![vir_low::Trigger::new(vec![perm_new.clone()])];
        //             let guard = predicate_arguments.into_iter().zip(arguments).map(|(parameter, argument)|
        //                 vir_low::Expression::not(vir_low::Expression::equals(parameter, argument))
        //             ).conjoin();
        //             let body = vir_low::Expression::implies(
        //                 guard,
        //                 vir_low::Expression::equals(perm_new, perm_old),
        //             );
        //             statements.push(vir_low::Statement::assume(
        //                 vir_low::Expression::forall(predicate_parameters, triggers, body),
        //                 position,
        //             ));
        //         },
        //         vir_low::Expression::Unfolding(_) => todo!(),
        //         vir_low::Expression::LabelledOld(_) => todo!(),
        //         vir_low::Expression::BinaryOp(_) => todo!(),
        //         vir_low::Expression::Conditional(_) => todo!(),
        //         vir_low::Expression::FuncApp(_) => todo!(),
        //         vir_low::Expression::DomainFuncApp(_) => todo!(),
        //         _ => {
        //             unimplemented!("expression: {:?}", expression);
        //         }
        //     }
        // }
        Ok(())
    }

    fn get_current_permission_mask_for(&self, predicate_name: &str) -> vir_low::Expression {
        todo!()
    }

    fn get_new_permission_mask_for(&self, predicate_name: &str) -> vir_low::Expression {
        todo!()
    }

    fn get_perm_function_name_for(&self, predicate_name: &str) -> String {
        todo!()
    }

    fn get_predicate_parameters_for(&self, predicate_name: &str) -> &[vir_low::VariableDecl] {
        todo!()
    }
}
