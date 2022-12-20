use crate::encoder::{
    errors::{ErrorCtxt, SpannedEncodingError, SpannedEncodingResult},
    middle::core_proof::{
        lowerer::LoweringResult,
        snapshots::{AllVariablesMap, VariableVersionMap},
    },
    mir::errors::ErrorInterface,
    Encoder,
};
use rustc_hash::{FxHashMap, FxHashSet};
use std::collections::{BTreeMap, BTreeSet};
use vir_crate::{
    common::{
        cfg::Cfg,
        check_mode::CheckMode,
        expression::{
            BinaryOperationHelpers, ExpressionIterator, QuantifierHelpers, UnaryOperationHelpers,
        },
        graphviz::ToGraphviz,
    },
    low::{
        self as vir_low,
        expression::visitors::{ExpressionFallibleFolder, ExpressionFolder},
        operations::ty::Typed,
    },
    middle as vir_mid,
};

pub(in super::super) fn custom_heap_encoding<'p, 'v: 'p, 'tcx: 'v>(
    encoder: &'p mut Encoder<'v, 'tcx>,
    result: &mut LoweringResult,
    predicate_info: BTreeMap<String, (String, vir_low::Type)>,
) -> SpannedEncodingResult<()> {
    let mut procedures = Vec::new();
    let mut heap_encoder = HeapEncoder::new(
        encoder,
        &result.predicates,
        predicate_info,
        &result.functions,
        &result.methods,
    );
    for mut procedure in std::mem::take(&mut result.procedures) {
        let predecessors = procedure.predecessors_owned();
        let traversal_order = procedure.get_topological_sort();
        let mut basic_block_edges = BTreeMap::new();
        for label in &traversal_order {
            heap_encoder.prepare_new_current_block(
                &label,
                &predecessors,
                &mut basic_block_edges,
            )?;
            let mut statements = Vec::new();
            let block = procedure.basic_blocks.get_mut(label).unwrap();
            for statement in std::mem::take(&mut block.statements) {
                heap_encoder.encode_statement(&mut statements, statement)?;
            }
            block.statements = statements;
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
                    block
                        .successor
                        .replace_label(&successor_label, intermediate_block_label.clone());
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
        let init_permissions_to_zero =
            heap_encoder.generate_init_permissions_to_zero(procedure.position)?;
        procedure
            .locals
            .extend(std::mem::take(&mut heap_encoder.new_variables.variables));
        procedure
            .basic_blocks
            .get_mut(&procedure.entry)
            .unwrap()
            .statements
            .splice(0..0, init_permissions_to_zero);
        procedures.push(procedure);
    }
    result.procedures = procedures;
    result
        .domains
        .extend(heap_encoder.generate_necessary_domains()?);
    Ok(())
}

#[derive(Default)]
struct VariableDeclarations {
    variables: FxHashSet<vir_low::VariableDecl>,
}

impl VariableDeclarations {
    fn create_variable(
        &mut self,
        variable_name: &str,
        ty: vir_low::Type,
        version: u64,
    ) -> SpannedEncodingResult<vir_low::VariableDecl> {
        let variable = vir_low::VariableDecl::new(format!("{}_{}", variable_name, version), ty);
        self.variables.insert(variable.clone());
        Ok(variable)
    }
}

struct HeapEncoder<'p, 'v: 'p, 'tcx: 'v> {
    encoder: &'p mut Encoder<'v, 'tcx>,
    new_variables: VariableDeclarations,
    predicates: FxHashMap<String, &'p vir_low::PredicateDecl>,
    snapshot_functions_to_predicates: BTreeMap<String, String>,
    predicates_to_snapshot_types: BTreeMap<String, vir_low::Type>,
    functions: FxHashMap<String, &'p vir_low::FunctionDecl>,
    methods: FxHashMap<String, &'p vir_low::MethodDecl>,
    ssa_state: vir_low::ssa::SSAState<vir_low::Label>,
    permission_mask_names: FxHashMap<String, String>,
    heap_names: FxHashMap<String, String>,
    /// A counter used for generating fresh labels.
    fresh_label_counter: u64,
}

impl<'p, 'v: 'p, 'tcx: 'v> HeapEncoder<'p, 'v, 'tcx> {
    fn new(
        encoder: &'p mut Encoder<'v, 'tcx>,
        predicates: &'p [vir_low::PredicateDecl],
        predicate_info: BTreeMap<String, (String, vir_low::Type)>,
        functions: &'p [vir_low::FunctionDecl],
        methods: &'p [vir_low::MethodDecl],
    ) -> Self {
        let mut snapshot_functions_to_predicates = BTreeMap::new();
        let mut predicates_to_snapshot_types = BTreeMap::new();
        for (predicate_name, (snapshot_function_name, snapshot_type)) in predicate_info {
            snapshot_functions_to_predicates.insert(snapshot_function_name, predicate_name.clone());
            predicates_to_snapshot_types.insert(predicate_name, snapshot_type);
        }
        Self {
            encoder,
            new_variables: Default::default(),
            permission_mask_names: predicates
                .iter()
                .map(|predicate| {
                    let mask_name = format!("perm${}", predicate.name);
                    (predicate.name.clone(), mask_name)
                })
                .collect(),
            heap_names: predicates
                .iter()
                .map(|predicate| {
                    let heap_name = format!("heap${}", predicate.name);
                    (predicate.name.clone(), heap_name)
                })
                .collect(),
            predicates: predicates
                .iter()
                .map(|predicate| (predicate.name.clone(), predicate))
                .collect(),
            snapshot_functions_to_predicates,
            predicates_to_snapshot_types,
            functions: functions
                .iter()
                .map(|function| (function.name.clone(), function))
                .collect(),
            methods: methods
                .iter()
                .map(|method| (method.name.clone(), method))
                .collect(),
            ssa_state: Default::default(),
            fresh_label_counter: 0,
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
            | vir_low::Statement::Assign(_) => {
                statements.push(statement);
            }
            vir_low::Statement::Label(statement) => {
                self.ssa_state.save_state_at_label(statement.label.clone());
                statements.push(vir_low::Statement::Label(statement));
            }
            vir_low::Statement::Assume(statement) => {
                assert!(statement.expression.is_pure());
                statements.push(vir_low::Statement::assume(
                    self.encode_pure_expression(statement.expression, None, &None)?,
                    statement.position,
                ));
            }
            vir_low::Statement::Assert(statement) => {
                unimplemented!("statement: {}", statement);
            }
            vir_low::Statement::Inhale(statement) => {
                statements.push(vir_low::Statement::comment(format!("{}", statement)));
                self.encode_expression_inhale(
                    statements,
                    statement.expression,
                    statement.position,
                    &None,
                )?;
            }
            vir_low::Statement::Exhale(statement) => {
                statements.push(vir_low::Statement::comment(format!("{}", statement)));
                let evaluation_state = self.fresh_label();
                self.ssa_state.save_state_at_label(evaluation_state.clone());
                self.encode_expression_exhale(
                    statements,
                    statement.expression,
                    statement.position,
                    &evaluation_state,
                    &None,
                )?;
            }
            vir_low::Statement::Fold(_) => todo!(),
            vir_low::Statement::Unfold(_) => todo!(),
            vir_low::Statement::ApplyMagicWand(_) => {
                unimplemented!("magic wands are not supported yet");
            }
            vir_low::Statement::MethodCall(statement) => {
                statements.push(vir_low::Statement::comment(format!("{}", statement)));
                let old_label = self.fresh_label();
                self.ssa_state.save_state_at_label(old_label.clone());
                let method = self.methods[&statement.method_name];
                let mut replacements = method
                    .parameters
                    .iter()
                    .zip(statement.arguments.iter())
                    .collect();
                let maybe_old_label = Some(old_label.clone());
                for assertion in &method.pres {
                    let assertion = assertion.clone().substitute_variables(&replacements);
                    self.encode_expression_exhale(
                        statements,
                        assertion,
                        statement.position,
                        &old_label,
                        &maybe_old_label,
                    )?;
                }
                replacements.extend(method.targets.iter().zip(statement.targets.iter()));
                for assertion in &method.posts {
                    let assertion = assertion.clone().substitute_variables(&replacements);
                    self.encode_expression_inhale(
                        statements,
                        assertion,
                        statement.position,
                        &maybe_old_label,
                    )?;
                }
            }
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
        current_state_label: Option<&str>,
        old_state_label: &Option<String>,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        struct Purifier<'e, 'p, 'v: 'p, 'tcx: 'v> {
            current_state_label: Option<&'e str>,
            old_state_label: &'e Option<String>,
            heap_encoder: &'e mut HeapEncoder<'p, 'v, 'tcx>,
        }
        impl<'e, 'p, 'v: 'p, 'tcx: 'v> ExpressionFallibleFolder for Purifier<'e, 'p, 'v, 'tcx> {
            type Error = SpannedEncodingError;

            fn fallible_fold_func_app_enum(
                &mut self,
                func_app: vir_low::expression::FuncApp,
            ) -> Result<vir_low::Expression, Self::Error> {
                let mut arguments = func_app
                    .arguments
                    .into_iter()
                    .map(|argument| self.fallible_fold_expression(argument))
                    .collect::<Result<Vec<_>, _>>()?;
                let predicate_name = self
                    .heap_encoder
                    .get_predicate_name_for_function(&func_app.function_name)?;
                let heap_version = if let Some(current_state_label) = self.current_state_label {
                    self.heap_encoder
                        .get_heap_version_at_label(&predicate_name, current_state_label)?
                } else {
                    self.heap_encoder
                        .get_current_heap_version_for(&predicate_name)?
                };
                arguments.push(heap_version);
                let heap_function_name = self
                    .heap_encoder
                    .get_heap_function_name_for(&predicate_name);
                let return_type = self
                    .heap_encoder
                    .get_snapshot_type_for_predicate(&predicate_name)
                    .unwrap();
                Ok(vir_low::Expression::domain_function_call(
                    "HeapFunctions",
                    heap_function_name,
                    arguments,
                    return_type,
                ))
            }
        }
        let mut purifier = Purifier {
            current_state_label,
            old_state_label,
            heap_encoder: self,
        };
        purifier.fallible_fold_expression(expression)
    }

    fn predicate_arguments(
        &mut self,
        predicate: &vir_low::ast::expression::PredicateAccessPredicate,
        old_label: &Option<String>,
    ) -> SpannedEncodingResult<Vec<vir_low::Expression>> {
        let mut arguments = Vec::new();
        for argument in &predicate.arguments {
            arguments.push(self.encode_pure_expression(argument.clone(), None, old_label)?);
        }
        Ok(arguments)
    }

    fn predicate_parameters(
        &mut self,
        predicate: &vir_low::ast::expression::PredicateAccessPredicate,
    ) -> SpannedEncodingResult<Vec<vir_low::Expression>> {
        let predicate_parameters = self
            .get_predicate_parameters_for(&predicate.name)
            .to_owned();
        Ok(predicate_parameters
            .iter()
            .map(|parameter| parameter.clone().into())
            .collect())
    }

    fn perm_call(
        &mut self,
        predicate: &vir_low::ast::expression::PredicateAccessPredicate,
        mut arguments: Vec<vir_low::Expression>,
        permission_mask: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let perm_function_name = self.get_perm_function_name_for(&predicate.name);
        arguments.push(permission_mask);
        Ok(vir_low::Expression::domain_function_call(
            "PermFunctions",
            perm_function_name.clone(),
            arguments,
            vir_low::Type::Perm,
        ))
    }

    fn perm_call_for_predicate_use(
        &mut self,
        predicate: &vir_low::ast::expression::PredicateAccessPredicate,
        permission_mask: vir_low::Expression,
        old_label: &Option<String>,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let arguments = self.predicate_arguments(predicate, old_label)?;
        self.perm_call(predicate, arguments, permission_mask)
    }

    fn perm_call_for_predicate_def(
        &mut self,
        predicate: &vir_low::ast::expression::PredicateAccessPredicate,
        permission_mask: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let arguments = self.predicate_parameters(predicate)?;
        self.perm_call(predicate, arguments, permission_mask)
    }

    fn encode_perm_unchanged_quantifier(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        predicate: &vir_low::ast::expression::PredicateAccessPredicate,
        old_permission_mask: vir_low::Expression,
        new_permission_mask: vir_low::Expression,
        position: vir_low::Position,
        old_label: &Option<String>,
    ) -> SpannedEncodingResult<()> {
        let perm_new = self.perm_call_for_predicate_def(&predicate, new_permission_mask.clone())?;
        let perm_old = self.perm_call_for_predicate_def(&predicate, old_permission_mask.clone())?;
        let predicate_parameters = self
            .get_predicate_parameters_for(&predicate.name)
            .to_owned();
        let predicate_arguments = self.predicate_parameters(predicate)?;
        let arguments = self.predicate_arguments(predicate, old_label)?;
        let triggers = vec![vir_low::Trigger::new(vec![perm_new.clone()])];
        let guard = predicate_arguments
            .into_iter()
            .zip(arguments)
            .map(|(parameter, argument)| vir_low::Expression::equals(parameter, argument))
            .conjoin();
        let body = vir_low::Expression::implies(
            vir_low::Expression::not(guard),
            vir_low::Expression::equals(perm_new, perm_old),
        );
        statements.push(vir_low::Statement::assume(
            vir_low::Expression::forall(predicate_parameters, triggers, body),
            position,
        ));
        Ok(())
    }

    fn heap_call(
        &mut self,
        predicate: &vir_low::ast::expression::PredicateAccessPredicate,
        mut arguments: Vec<vir_low::Expression>,
        heap_version: vir_low::Expression,
    ) -> SpannedEncodingResult<Option<vir_low::Expression>> {
        let call =
            if let Some(snapshot_type) = self.get_snapshot_type_for_predicate(&predicate.name) {
                let heap_function_name = self.get_heap_function_name_for(&predicate.name);
                arguments.push(heap_version);
                Some(vir_low::Expression::domain_function_call(
                    "HeapFunctions",
                    heap_function_name,
                    arguments,
                    snapshot_type,
                ))
            } else {
                None
            };
        Ok(call)
    }

    fn heap_call_for_predicate_def(
        &mut self,
        predicate: &vir_low::ast::expression::PredicateAccessPredicate,
        heap_version: vir_low::Expression,
    ) -> SpannedEncodingResult<Option<vir_low::Expression>> {
        let arguments = self.predicate_parameters(predicate)?;
        self.heap_call(predicate, arguments, heap_version)
    }

    fn encode_heap_unchanged_quantifier(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        predicate: &vir_low::ast::expression::PredicateAccessPredicate,
        new_permission_mask: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        let heap_version_old = self.get_current_heap_version_for(&predicate.name)?;
        if let Some(heap_old) =
            self.heap_call_for_predicate_def(&predicate, heap_version_old.clone())?
        {
            let heap_version_new = self.get_new_heap_version_for(&predicate.name, position)?;
            let heap_new = self
                .heap_call_for_predicate_def(&predicate, heap_version_new.clone())?
                .unwrap();
            let perm_new =
                self.perm_call_for_predicate_def(&predicate, new_permission_mask.clone())?;
            let predicate_parameters = self
                .get_predicate_parameters_for(&predicate.name)
                .to_owned();
            let triggers = vec![vir_low::Trigger::new(vec![heap_new.clone()])];
            let guard =
                vir_low::Expression::greater_than(perm_new, vir_low::Expression::no_permission());
            let body = vir_low::Expression::implies(
                guard,
                vir_low::Expression::equals(heap_old, heap_new),
            );
            statements.push(vir_low::Statement::assume(
                vir_low::Expression::forall(predicate_parameters, triggers, body),
                position,
            ));
        }
        Ok(())
    }

    fn encode_expression_inhale(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        expression: vir_low::Expression,
        position: vir_low::Position,
        old_label: &Option<String>,
    ) -> SpannedEncodingResult<()> {
        if expression.is_pure() {
            statements.push(vir_low::Statement::assume(
                self.encode_pure_expression(expression, None, old_label)?,
                position,
            ));
        } else {
            match expression {
                vir_low::Expression::PredicateAccessPredicate(expression) => {
                    let old_permission_mask =
                        self.get_current_permission_mask_for(&expression.name)?;
                    let new_permission_mask =
                        self.get_new_permission_mask_for(&expression.name, position)?;
                    let perm_old = self.perm_call_for_predicate_use(
                        &expression,
                        old_permission_mask.clone(),
                        old_label,
                    )?;
                    let perm_new = self.perm_call_for_predicate_use(
                        &expression,
                        new_permission_mask.clone(),
                        old_label,
                    )?;
                    statements.push(vir_low::Statement::assume(
                        vir_low::Expression::equals(
                            perm_new.clone(),
                            vir_low::Expression::perm_binary_op_no_pos(
                                vir_low::ast::expression::PermBinaryOpKind::Add,
                                perm_old.clone(),
                                (*expression.permission).clone(),
                            ),
                        ),
                        position, // FIXME: use position of expression.permission with proper ErrorCtxt.
                    ));
                    // assume forall arg1: Ref, arg2: Ref ::
                    //     {perm<P>(arg1, arg2, v_new)}
                    //     !(r1 == arg1 && r2 == arg2) ==>
                    //     perm<P>(arg1, arg2, v_new) == perm<P>(arg1, arg2, v_old)
                    self.encode_perm_unchanged_quantifier(
                        statements,
                        &expression,
                        old_permission_mask,
                        new_permission_mask,
                        position,
                        old_label,
                    )?;
                }
                vir_low::Expression::Unfolding(_) => todo!(),
                vir_low::Expression::LabelledOld(_) => todo!(),
                vir_low::Expression::BinaryOp(expression) => match expression.op_kind {
                    vir_low::BinaryOpKind::And => {
                        self.encode_expression_inhale(
                            statements,
                            *expression.left,
                            position,
                            old_label,
                        )?;
                        self.encode_expression_inhale(
                            statements,
                            *expression.right,
                            position,
                            old_label,
                        )?;
                    }
                    vir_low::BinaryOpKind::Implies => {
                        let guard =
                            self.encode_pure_expression(*expression.left, None, old_label)?;
                        let mut body = Vec::new();
                        self.encode_expression_inhale(
                            &mut body,
                            *expression.right,
                            position,
                            old_label,
                        )?;
                        statements.push(vir_low::Statement::conditional(
                            guard,
                            body,
                            Vec::new(),
                            position,
                        ))
                    }
                    _ => unreachable!("expression: {}", expression),
                },
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

    fn encode_expression_exhale(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        expression: vir_low::Expression,
        position: vir_low::Position,
        expression_evaluation_state_label: &str,
        old_label: &Option<String>,
    ) -> SpannedEncodingResult<()> {
        assert!(!position.is_default(), "expression: {}", expression);
        if expression.is_pure() {
            statements.push(vir_low::Statement::assert(
                self.encode_pure_expression(
                    expression,
                    Some(expression_evaluation_state_label),
                    old_label,
                )?,
                position,
            ));
        } else {
            match expression {
                vir_low::Expression::PredicateAccessPredicate(expression) => {
                    let old_permission_mask =
                        self.get_current_permission_mask_for(&expression.name)?;
                    let new_permission_mask =
                        self.get_new_permission_mask_for(&expression.name, position)?;
                    let perm_old = self.perm_call_for_predicate_use(
                        &expression,
                        old_permission_mask.clone(),
                        old_label,
                    )?;
                    let perm_new = self.perm_call_for_predicate_use(
                        &expression,
                        new_permission_mask.clone(),
                        old_label,
                    )?;
                    // assert perm<P>(r1, r2, v_old) >= p
                    statements.push(vir_low::Statement::assert(
                        vir_low::Expression::greater_equals(
                            perm_old.clone(),
                            (*expression.permission).clone(),
                        ),
                        position, // FIXME: use position of expression.permission with proper ErrorCtxt.
                    ));
                    // assume perm<P>(r1, r2, v_new) == perm<P>(r1, r2, v_old) - p
                    statements.push(vir_low::Statement::assume(
                        vir_low::Expression::equals(
                            perm_new.clone(),
                            vir_low::Expression::perm_binary_op_no_pos(
                                vir_low::ast::expression::PermBinaryOpKind::Sub,
                                perm_old.clone(),
                                (*expression.permission).clone(),
                            ),
                        ),
                        position, // FIXME: use position of expression.permission with proper ErrorCtxt.
                    ));
                    // assume forall arg1: Ref, arg2: Ref ::
                    //     {perm<P>(arg1, arg2, v_new)}
                    //     !(r1 == arg1 && r2 == arg2) ==>
                    //     perm<P>(arg1, arg2, v_new) == perm<P>(arg1, arg2, v_old)
                    self.encode_perm_unchanged_quantifier(
                        statements,
                        &expression,
                        old_permission_mask.clone(),
                        new_permission_mask.clone(),
                        position,
                        old_label,
                    )?;
                    // assume forall arg1: Ref, arg2: Ref ::
                    //     {heap<P>(arg1, arg2, vh_new)}
                    //     perm<P>(arg1, arg2, v_new) > 0 ==>
                    //     heap<P>(arg1, arg2, vh_new) == heap<P>(arg1, arg2, vh_old)
                    self.encode_heap_unchanged_quantifier(
                        statements,
                        &expression,
                        new_permission_mask,
                        position,
                    )?;
                }
                vir_low::Expression::Unfolding(_) => todo!(),
                vir_low::Expression::LabelledOld(_) => todo!(),
                vir_low::Expression::BinaryOp(expression) => match expression.op_kind {
                    vir_low::BinaryOpKind::And => {
                        self.encode_expression_exhale(
                            statements,
                            *expression.left,
                            position,
                            expression_evaluation_state_label,
                            old_label,
                        )?;
                        self.encode_expression_exhale(
                            statements,
                            *expression.right,
                            position,
                            expression_evaluation_state_label,
                            old_label,
                        )?;
                    }
                    vir_low::BinaryOpKind::Implies => {
                        let guard =
                            self.encode_pure_expression(*expression.left, None, old_label)?;
                        let mut body = Vec::new();
                        self.encode_expression_exhale(
                            &mut body,
                            *expression.right,
                            position,
                            expression_evaluation_state_label,
                            old_label,
                        )?;
                        statements.push(vir_low::Statement::conditional(
                            guard,
                            body,
                            Vec::new(),
                            position,
                        ))
                    }
                    _ => unreachable!("expression: {}", expression),
                },
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

    fn get_current_permission_mask_for(
        &mut self,
        predicate_name: &str,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let variable_name = self.permission_mask_names.get(predicate_name).unwrap();
        let version = self.ssa_state.current_variable_version(variable_name);
        let ty = self.perm_version_type();
        Ok(self
            .new_variables
            .create_variable(variable_name, ty, version)?
            .into())
    }

    // fn get_initial_permission_mask_for(
    //     &mut self,
    //     predicate_name: &str,
    // ) -> SpannedEncodingResult<vir_low::Expression> {
    //     let variable_name = self.permission_mask_names.get(predicate_name).unwrap();
    //     let version = self.ssa_state.initial_variable_version(variable_name);
    //     let ty = self.perm_version_type();
    //     Ok(self
    //         .new_variables
    //         .create_variable(variable_name, ty, version)?
    //         .into())
    // }

    fn get_new_permission_mask_for(
        &mut self,
        predicate_name: &str,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let variable_name = self.permission_mask_names.get(predicate_name).unwrap();
        let ty = self.perm_version_type();
        let version = self
            .ssa_state
            .new_variable_version(variable_name, &ty, position);
        Ok(self
            .new_variables
            .create_variable(variable_name, ty, version)?
            .into())
    }

    fn get_perm_function_name_for(&self, predicate_name: &str) -> String {
        format!("perm${}", predicate_name)
    }

    fn get_current_heap_version_for(
        &mut self,
        predicate_name: &str,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let variable_name = self.heap_names.get(predicate_name).unwrap();
        let version = self.ssa_state.current_variable_version(variable_name);
        let ty = self.heap_version_type();
        Ok(self
            .new_variables
            .create_variable(variable_name, ty, version)?
            .into())
    }

    fn get_new_heap_version_for(
        &mut self,
        predicate_name: &str,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let variable_name = self.heap_names.get(predicate_name).unwrap();
        let ty = self.heap_version_type();
        let version = self
            .ssa_state
            .new_variable_version(variable_name, &ty, position);
        Ok(self
            .new_variables
            .create_variable(variable_name, ty, version)?
            .into())
    }

    fn get_heap_version_at_label(
        &mut self,
        predicate_name: &str,
        label: &str,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let variable_name = self.heap_names.get(predicate_name).unwrap();
        let version = self
            .ssa_state
            .variable_version_at_label(variable_name, label);
        let ty = self.heap_version_type();
        Ok(self
            .new_variables
            .create_variable(variable_name, ty, version)?
            .into())
    }

    fn get_heap_function_name_for(&self, predicate_name: &str) -> String {
        format!("heap${}", predicate_name)
    }

    fn get_predicate_parameters_for(&self, predicate_name: &str) -> &[vir_low::VariableDecl] {
        self.predicates
            .get(predicate_name)
            .unwrap()
            .parameters
            .as_slice()
    }

    fn prepare_new_current_block(
        &mut self,
        label: &vir_low::Label,
        predecessors: &BTreeMap<vir_low::Label, Vec<vir_low::Label>>,
        basic_block_edges: &mut BTreeMap<
            vir_low::Label,
            BTreeMap<vir_low::Label, Vec<(String, vir_low::Type, vir_low::Position, u64, u64)>>,
        >,
    ) -> SpannedEncodingResult<()> {
        self.ssa_state
            .prepare_new_current_block(label, predecessors, basic_block_edges);
        Ok(())
    }

    fn finish_current_block(&mut self, label: vir_low::Label) -> SpannedEncodingResult<()> {
        self.ssa_state.finish_current_block(label);
        Ok(())
    }

    fn fresh_label(&mut self) -> String {
        self.fresh_label_counter += 1;
        format!("heap_label${}", self.fresh_label_counter)
    }

    fn perm_version_type(&self) -> vir_low::Type {
        vir_low::Type::domain("PermVersion".to_string())
    }

    fn heap_version_type(&self) -> vir_low::Type {
        vir_low::Type::domain("HeapVersion".to_string())
    }

    fn generate_necessary_domains(&self) -> SpannedEncodingResult<Vec<vir_low::DomainDecl>> {
        let perm_version_domain = vir_low::DomainDecl::new("PermVersion", Vec::new(), Vec::new());
        let heap_version_domain = vir_low::DomainDecl::new("HeapVersion", Vec::new(), Vec::new());
        let mut perm_functions = Vec::new();
        let mut heap_functions = Vec::new();
        for predicate in self.predicates.values() {
            {
                let mut parameters = predicate.parameters.clone();
                parameters.push(vir_low::VariableDecl::new(
                    "version",
                    self.perm_version_type(),
                ));
                perm_functions.push(vir_low::DomainFunctionDecl::new(
                    self.get_perm_function_name_for(&predicate.name),
                    false,
                    parameters,
                    vir_low::Type::Perm,
                ));
            }
            if let Some(snapshot_type) = self.get_snapshot_type_for_predicate(&predicate.name) {
                let mut parameters = predicate.parameters.clone();
                parameters.push(vir_low::VariableDecl::new(
                    "version",
                    self.heap_version_type(),
                ));
                heap_functions.push(vir_low::DomainFunctionDecl::new(
                    self.get_heap_function_name_for(&predicate.name),
                    false,
                    parameters,
                    snapshot_type,
                ));
            }
        }
        let perm_domain = vir_low::DomainDecl::new("PermFunctions", perm_functions, Vec::new());
        let heap_domain = vir_low::DomainDecl::new("HeapFunctions", heap_functions, Vec::new());
        let domains = vec![
            perm_domain,
            perm_version_domain,
            heap_domain,
            heap_version_domain,
        ];
        Ok(domains)
    }

    fn generate_init_permissions_to_zero(
        &mut self,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<Vec<vir_low::Statement>> {
        let mut statements = Vec::new();
        for predicate in self.predicates.values() {
            let initial_permission_mask_name =
                self.permission_mask_names.get(&predicate.name).unwrap();
            let initial_permission_mask_version = self
                .ssa_state
                .initial_variable_version(initial_permission_mask_name);
            let initial_permission_mask_ty = self.perm_version_type();
            let initial_permission_mask: vir_low::Expression = self
                .new_variables
                .create_variable(
                    initial_permission_mask_name,
                    initial_permission_mask_ty,
                    initial_permission_mask_version,
                )?
                .into();
            let mut arguments: Vec<_> = predicate
                .parameters
                .iter()
                .map(|parameter| parameter.clone().into())
                .collect();
            arguments.push(initial_permission_mask.clone());
            let perm_function_name = self.get_perm_function_name_for(&predicate.name);
            let perm = vir_low::Expression::domain_function_call(
                "PermFunctions",
                perm_function_name.clone(),
                arguments,
                vir_low::Type::Perm,
            );
            let triggers = vec![vir_low::Trigger::new(vec![perm.clone()])];
            let body = vir_low::Expression::equals(perm, vir_low::Expression::no_permission());
            statements.push(vir_low::Statement::assume(
                vir_low::Expression::forall(predicate.parameters.clone(), triggers, body),
                position,
            ));
        }
        Ok(statements)
    }

    fn get_predicate_name_for_function<'a>(
        &'a self,
        function_name: &str,
    ) -> SpannedEncodingResult<String> {
        let function = self.functions[function_name];
        let predicate_name = match function.kind {
            vir_low::FunctionKind::MemoryBlockBytes => todo!(),
            vir_low::FunctionKind::CallerFor => todo!(),
            vir_low::FunctionKind::Snap => {
                self.snapshot_functions_to_predicates[function_name].clone()
            }
        };
        Ok(predicate_name)
    }

    fn get_snapshot_type_for_predicate(&self, predicate_name: &str) -> Option<vir_low::Type> {
        let predicate = self.predicates[predicate_name];
        match predicate.kind {
            vir_low::PredicateKind::MemoryBlock => {
                use vir_low::macros::*;
                Some(ty!(Bytes))
            }
            vir_low::PredicateKind::Owned => Some(
                self.predicates_to_snapshot_types
                    .get(predicate_name)
                    .unwrap_or_else(|| unreachable!("predicate not found: {}", predicate_name))
                    .clone(),
            ),
            vir_low::PredicateKind::WithoutSnapshot => None,
        }
    }
}
