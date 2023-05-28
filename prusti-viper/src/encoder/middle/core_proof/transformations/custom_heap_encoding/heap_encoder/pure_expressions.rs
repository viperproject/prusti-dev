use super::HeapEncoder;
use crate::encoder::errors::{SpannedEncodingError, SpannedEncodingResult};
use vir_crate::{
    common::{
        builtin_constants::MEMORY_BLOCK_PREDICATE_NAME,
        expression::{BinaryOperationHelpers, ExpressionIterator, UnaryOperationHelpers},
    },
    low::{self as vir_low, expression::visitors::ExpressionFallibleFolder},
};

impl<'p, 'v: 'p, 'tcx: 'v> HeapEncoder<'p, 'v, 'tcx> {
    pub(super) fn encode_pure_expression(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        expression: vir_low::Expression,
        expression_evaluation_state_label: Option<String>,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let mut purifier = Purifier {
            expression_evaluation_state_label,
            heap_encoder: self,
            statements,
            path_condition: Vec::new(),
            position,
        };
        purifier.fallible_fold_expression(expression)
    }
}

struct Purifier<'e, 'p, 'v: 'p, 'tcx: 'v> {
    /// The state in which we should evaluate the heap expressions. If `None`,
    /// takes the latest heap.
    expression_evaluation_state_label: Option<String>,
    heap_encoder: &'e mut HeapEncoder<'p, 'v, 'tcx>,
    statements: &'e mut Vec<vir_low::Statement>,
    path_condition: Vec<vir_low::Expression>,
    position: vir_low::Position,
}

impl<'e, 'p, 'v: 'p, 'tcx: 'v> Purifier<'e, 'p, 'v, 'tcx> {
    fn snap_function_call(
        &mut self,
        predicate_name: &str,
        mut arguments: Vec<vir_low::Expression>,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let heap_version = if let Some(expression_evaluation_state_label) =
            &self.expression_evaluation_state_label
        {
            self.heap_encoder
                .get_heap_version_at_label(predicate_name, expression_evaluation_state_label)?
        } else {
            self.heap_encoder
                .get_current_heap_version_for(predicate_name)?
        };
        arguments.push(heap_version);
        let heap_function_name = self.heap_encoder.heap_function_name(predicate_name);
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

impl<'e, 'p, 'v: 'p, 'tcx: 'v> ExpressionFallibleFolder for Purifier<'e, 'p, 'v, 'tcx> {
    type Error = SpannedEncodingError;

    fn fallible_fold_func_app_enum(
        &mut self,
        func_app: vir_low::expression::FuncApp,
    ) -> Result<vir_low::Expression, Self::Error> {
        let function = self.heap_encoder.functions[&func_app.function_name];
        assert_eq!(function.parameters.len(), func_app.arguments.len());
        let arguments = func_app
            .arguments
            .into_iter()
            .map(|argument| self.fallible_fold_expression(argument))
            .collect::<Result<Vec<_>, _>>()?;
        let path_condition = self.path_condition.iter().cloned().conjoin();
        let replacements = function.parameters.iter().zip(arguments.iter()).collect();
        let pres = function
            .pres
            .iter()
            .cloned()
            .conjoin()
            .substitute_variables(&replacements);
        let pres = self.fallible_fold_expression(pres)?;
        let assert_precondition = vir_low::Expression::implies(path_condition, pres);
        self.heap_encoder.encode_function_precondition_assert(
            self.statements,
            assert_precondition,
            self.position,
            self.expression_evaluation_state_label.clone(),
        )?;
        match function.kind {
            vir_low::FunctionKind::MemoryBlockBytes => {
                self.snap_function_call(MEMORY_BLOCK_PREDICATE_NAME, arguments)
            }
            vir_low::FunctionKind::CallerFor => todo!(),
            vir_low::FunctionKind::SnapRange => todo!(),
            vir_low::FunctionKind::Snap => {
                let predicate_name = self
                    .heap_encoder
                    .get_predicate_name_for_function(&func_app.function_name)?;
                self.snap_function_call(&predicate_name, arguments)
            }
        }
    }

    fn fallible_fold_binary_op(
        &mut self,
        mut binary_op: vir_low::expression::BinaryOp,
    ) -> Result<vir_low::expression::BinaryOp, Self::Error> {
        binary_op.left = self.fallible_fold_expression_boxed(binary_op.left)?;
        if binary_op.op_kind == vir_low::BinaryOpKind::Implies {
            self.path_condition.push((*binary_op.left).clone());
        }
        binary_op.right = self.fallible_fold_expression_boxed(binary_op.right)?;
        if binary_op.op_kind == vir_low::BinaryOpKind::Implies {
            self.path_condition.pop();
        }
        Ok(binary_op)
    }

    fn fallible_fold_conditional(
        &mut self,
        mut conditional: vir_low::expression::Conditional,
    ) -> Result<vir_low::expression::Conditional, Self::Error> {
        conditional.guard = self.fallible_fold_expression_boxed(conditional.guard)?;
        self.path_condition.push((*conditional.guard).clone());
        conditional.then_expr = self.fallible_fold_expression_boxed(conditional.then_expr)?;
        self.path_condition.pop();
        self.path_condition
            .push(vir_low::Expression::not((*conditional.guard).clone()));
        conditional.else_expr = self.fallible_fold_expression_boxed(conditional.else_expr)?;
        self.path_condition.pop();
        Ok(conditional)
    }

    fn fallible_fold_labelled_old_enum(
        &mut self,
        mut labelled_old: vir_low::expression::LabelledOld,
    ) -> Result<vir_low::Expression, Self::Error> {
        std::mem::swap(
            &mut labelled_old.label,
            &mut self.expression_evaluation_state_label,
        );
        let mut labelled_old = self.fallible_fold_labelled_old(labelled_old)?;
        std::mem::swap(
            &mut labelled_old.label,
            &mut self.expression_evaluation_state_label,
        );
        Ok(vir_low::Expression::LabelledOld(labelled_old))
    }

    fn fallible_fold_quantifier(
        &mut self,
        quantifier: vir_low::Quantifier,
    ) -> Result<vir_low::Quantifier, Self::Error> {
        // TODO: Generate a fresh variable for each bound variable and use them instead when checking preconditions.
        unimplemented!("quantifier: {quantifier}");
    }
}
