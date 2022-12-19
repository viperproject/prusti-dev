use std::collections::{BTreeMap, BTreeSet};
use crate::encoder::{
    errors::{SpannedEncodingResult, ErrorCtxt},
    middle::core_proof::{
        lowerer::LoweringResult,
        snapshots::{AllVariablesMap, VariableVersionMap},
    }, Encoder, mir::errors::ErrorInterface,
};
use rustc_hash::{FxHashMap, FxHashSet};
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

pub(in super::super) fn custom_heap_encoding<'p, 'v: 'p, 'tcx: 'v>(
    encoder: &'p mut Encoder<'v, 'tcx>,
    result: &mut LoweringResult,
) -> SpannedEncodingResult<()> {
    let mut procedures = Vec::new();
    let mut heap_encoder = HeapEncoder::new(encoder, std::mem::take(&mut result.predicates));
    for mut procedure in std::mem::take(&mut result.procedures) {
        let predecessors = procedure.predecessors_owned();
        let traversal_order = procedure.get_topological_sort();
        let mut basic_block_edges = BTreeMap::new();
        for label in &traversal_order {
            heap_encoder.prepare_new_current_block(&label, &predecessors, &mut basic_block_edges)?;
            let mut statements = Vec::new();
            let block = procedure.basic_blocks.get_mut(label).unwrap();
            for statement in std::mem::take(&mut block.statements) {
                heap_encoder.encode_statement(&mut statements, statement)?;
            }
            heap_encoder.finish_current_block(label.clone())?;
        }
        for label in traversal_order {
            if let Some(intermediate_blocks) = basic_block_edges.remove(&label) {
                let mut block = procedure.basic_blocks.remove(&label).unwrap();
                for (successor_label, equalities) in intermediate_blocks {
                    let intermediate_block_label = vir_low::Label::new(format!(
                        "label__from__{}__to__{}",
                        label.name, successor_label.name
                    ));
                    block.successor.replace_label(&successor_label, intermediate_block_label.clone());
                    let mut successor_statements = Vec::new();
                    for (variable_name, ty, position, old_version, new_version) in equalities {
                        let new_variable = heap_encoder.new_variables.create_variable(
                            &variable_name,
                            ty.clone(),
                            new_version,
                        )?;
                        let old_variable = heap_encoder.new_variables.create_variable(
                            &variable_name,
                            ty.clone(),
                            old_version,
                        )?;
                        let position = heap_encoder.encoder.change_error_context(
                            // FIXME: Get a more precise span.
                            position,
                            ErrorCtxt::Unexpected,
                        );
                        let statement = vir_low::macros::stmtp! {
                            position => assume (new_variable == old_variable)
                        };
                        successor_statements.push(statement);
                    }
                    procedure.basic_blocks.insert(
                        intermediate_block_label,
                        vir_low::BasicBlock {
                            statements: successor_statements,
                            successor: vir_low::Successor::Goto(successor_label),
                        },
                    );
                }
                procedure.basic_blocks.insert(label, block);
            }
        }
        procedure
            .locals
            .extend(std::mem::take(&mut heap_encoder.new_variables.variables));
        procedures.push(procedure);
    }
    Ok(())
}

#[derive(Default)]
struct VariableDeclarations {
    variables: FxHashSet<vir_low::VariableDecl>,
}

impl VariableDeclarations {
    fn create_variable(&mut self, variable_name: &str, ty: vir_low::Type, version: u64) -> SpannedEncodingResult<vir_low::VariableDecl> {
        let variable = vir_low::VariableDecl::new(
            format!("{}_{}", variable_name, version),
            ty,
        );
        self.variables.insert(variable.clone());
        Ok(variable)
    }
}

struct HeapEncoder<'p, 'v: 'p, 'tcx: 'v> {
    encoder: &'p mut Encoder<'v, 'tcx>,
    new_variables:VariableDeclarations,
    predicates: FxHashMap<String, vir_low::PredicateDecl>,
    ssa_state: vir_low::ssa::SSAState<vir_low::Label>,
    permission_mask_names: FxHashMap<String, String>,
}

impl<'p, 'v: 'p, 'tcx: 'v> HeapEncoder<'p, 'v, 'tcx> {
    fn new(encoder: &'p mut Encoder<'v, 'tcx>, predicates: Vec<vir_low::PredicateDecl>) -> Self {
        Self {
            encoder,
            new_variables: Default::default(),
            permission_mask_names: predicates.iter().map(|predicate| {
                let mask_name = format!("perm${}", predicate.name);
                (predicate.name.clone(), mask_name)
            }).collect(),
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
            vir_low::Statement::MethodCall(statement) => {
                unimplemented!("method: {}", statement);
            },
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
        if expression.is_pure() {
            statements.push(vir_low::Statement::assume(self.encode_pure_expression(expression)?, position));
        } else {
            match expression {
                vir_low::Expression::PredicateAccessPredicate(expression) => {
                    let old_permission_mask = self.get_current_permission_mask_for(&expression.name)?;
                    let new_permission_mask = self.get_new_permission_mask_for(&expression.name, position)?;
                    let perm_function_name = self.get_perm_function_name_for(&expression.name);
                    let predicate_parameters = self.get_predicate_parameters_for(&expression.name).to_owned();
                    // assume perm<P>(r1, r2, v_new) == perm<P>(r1, r2, v_old) + p
                    let mut arguments = Vec::new();
                    for argument in expression.arguments {
                        arguments.push(self.encode_pure_expression(argument)?);
                    }
                    let mut old_permission_arguments = arguments.clone();
                    let mut new_permission_arguments = arguments.clone();
                    old_permission_arguments.push(old_permission_mask.clone());
                    new_permission_arguments.push(new_permission_mask.clone());
                    statements.push(vir_low::Statement::assume(
                        vir_low::Expression::equals(
                            vir_low::Expression::domain_function_call(
                                "Perm",
                                perm_function_name.clone(),
                                new_permission_arguments,
                                vir_low::Type::Perm,
                            ),
                            vir_low::Expression::add(
                                vir_low::Expression::domain_function_call(
                                    "Perm",
                                    perm_function_name.clone(),
                                    old_permission_arguments,
                                    vir_low::Type::Perm,
                                ),
                                *expression.permission,
                            ),
                        ),
                        expression.position,
                    ));
                    // assume forall arg1: Ref, arg2: Ref ::
                    //     {perm<P>(arg1, arg2, v_new)}
                    //     r1 != arg1 && r2 != arg2 ==>
                    //     perm<P>(arg1, arg2, v_new) == perm<P>(arg1, arg2, v_old)
                    let predicate_arguments: Vec<vir_low::Expression> = predicate_parameters
                        .iter()
                        .map(|parameter| parameter.clone().into())
                        .collect();
                    let mut old_permission_arguments = predicate_arguments.clone();
                    let mut new_permission_arguments = predicate_arguments.clone();
                    old_permission_arguments.push(old_permission_mask);
                    new_permission_arguments.push(new_permission_mask);
                    let perm_new = vir_low::Expression::domain_function_call(
                        "Perm",
                        perm_function_name.clone(),
                        new_permission_arguments,
                        vir_low::Type::Perm,
                    );
                    let perm_old = vir_low::Expression::domain_function_call(
                        "Perm",
                        perm_function_name.clone(),
                        old_permission_arguments,
                        vir_low::Type::Perm,
                    );
                    let triggers = vec![vir_low::Trigger::new(vec![perm_new.clone()])];
                    let guard = predicate_arguments.into_iter().zip(arguments).map(|(parameter, argument)|
                        vir_low::Expression::not(vir_low::Expression::equals(parameter, argument))
                    ).conjoin();
                    let body = vir_low::Expression::implies(
                        guard,
                        vir_low::Expression::equals(perm_new, perm_old),
                    );
                    statements.push(vir_low::Statement::assume(
                        vir_low::Expression::forall(predicate_parameters, triggers, body),
                        position,
                    ));
                },
                vir_low::Expression::Unfolding(_) => todo!(),
                vir_low::Expression::LabelledOld(_) => todo!(),
                vir_low::Expression::BinaryOp(_) => todo!(),
                vir_low::Expression::Conditional(_) => todo!(),
                vir_low::Expression::FuncApp(_) => todo!(),
                vir_low::Expression::DomainFuncApp(_) => todo!(),
                _ => {
                    unimplemented!("expression: {:?}", expression);
                }
            }
        }
        Ok(())
    }

    fn get_current_permission_mask_for(&mut self, predicate_name: &str) -> SpannedEncodingResult<vir_low::Expression> {
        let variable_name = self.permission_mask_names.get(predicate_name).unwrap();
        let version = self.ssa_state.current_variable_version(variable_name);
        let ty = vir_low::Type::Perm;
        Ok(self.new_variables.create_variable(variable_name, ty, version)?.into())
    }

    fn get_new_permission_mask_for(&mut self, predicate_name: &str, position: vir_low::Position) -> SpannedEncodingResult<vir_low::Expression> {
        let variable_name = self.permission_mask_names.get(predicate_name).unwrap();
        let ty = vir_low::Type::Perm;
        let version = self.ssa_state.new_variable_version(variable_name, &ty, position);
        Ok(self.new_variables.create_variable(variable_name, ty, version)?.into())
    }

    fn get_perm_function_name_for(&self, predicate_name: &str) -> String {
        format!("perm${}", predicate_name)
    }

    fn get_predicate_parameters_for(&self, predicate_name: &str) -> &[vir_low::VariableDecl] {
        self.predicates.get(predicate_name).unwrap().parameters.as_slice()
    }

    fn prepare_new_current_block(&mut self, label: &vir_low::Label, predecessors: &BTreeMap<vir_low::Label, Vec<vir_low::Label>>, basic_block_edges: &mut BTreeMap<
        vir_low::Label,
        BTreeMap<
            vir_low::Label,
            Vec<(String, vir_low::Type, vir_low::Position, u64, u64)>,
        >,
    >) -> SpannedEncodingResult<()> {
        self.ssa_state.prepare_new_current_block(
            label,
            predecessors,
            basic_block_edges,
        );
        Ok(())
    }

    fn finish_current_block(&mut self, label: vir_low::Label) -> SpannedEncodingResult<()> {
        self.ssa_state.finish_current_block(label);
        Ok(())
    }

}
