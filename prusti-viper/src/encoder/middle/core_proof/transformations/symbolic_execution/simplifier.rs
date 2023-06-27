use super::{egg::EGraphState, program_context::ProgramContext};
use crate::{
    encoder::{
        errors::{SpannedEncodingError, SpannedEncodingResult},
        middle::core_proof::transformations::encoder_context::EncoderContext,
    },
    error_internal,
};
use prusti_common::config;
use vir_crate::{
    common::expression::BinaryOperationHelpers,
    low::{self as vir_low, expression::visitors::ExpressionFallibleFolder},
};

// impl<'a> ProcedureExecutor<'a> {
//     pub(super) fn simplify_expression(
//         &mut self,
//         expression: vir_low::Expression,
//     ) -> SpannedEncodingResult<vir_low::Expression> {
//         let mut simplifier = Simplifier {
//             program_context: self.program_context,
//             solver: self.execution_trace_builder.current_egraph_state(),
//         };
//         simplifier.fallible_fold_expression(expression)
//     }
// }

pub(super) fn simplify_expression<'a, 'c>(
    expression: vir_low::Expression,
    program_context: &'a mut ProgramContext<'c, impl EncoderContext>,
    solver: &'a mut EGraphState,
) -> SpannedEncodingResult<vir_low::Expression> {
    let mut simplifier = Simplifier {
        program_context,
        solver,
    };
    simplifier.fallible_fold_expression(expression)
}

struct Simplifier<'a, 'c: 'a, EC: EncoderContext> {
    program_context: &'a mut ProgramContext<'c, EC>,
    solver: &'a mut EGraphState,
}

impl<'a, 'c: 'a, EC: EncoderContext> Simplifier<'a, 'c, EC> {
    // fn intern_arguments_and_saturate(
    //     &mut self,
    //     arguments: &[vir_low::Expression],
    // ) -> SpannedEncodingResult<()> {
    //     for argument in arguments {
    //         self.solver
    //             .try_intern_heap_independent_conjuncts(argument)?;
    //     }
    //     self.solver.saturate()?;
    //     Ok(())
    // }

    fn try_resolve_constants(
        &mut self,
        arguments: &[vir_low::Expression],
    ) -> SpannedEncodingResult<(bool, Vec<Option<(Option<String>, vir_low::Expression)>>)> {
        let mut maybe_constants = Vec::new();
        let mut found_constant = false;
        for argument in arguments {
            let maybe_constant = self.solver.resolve_constant(
                argument,
                self.program_context.get_constant_constructor_names(),
            )?;
            if maybe_constant.is_some() {
                found_constant = true;
            }
            maybe_constants.push(maybe_constant);
        }
        Ok((found_constant, maybe_constants))
    }
}

impl<'a, 'c: 'a, EC: EncoderContext> ExpressionFallibleFolder for Simplifier<'a, 'c, EC> {
    type Error = SpannedEncodingError;

    fn fallible_fold_domain_func_app_enum(
        &mut self,
        mut domain_func_app: vir_low::DomainFuncApp,
    ) -> Result<vir_low::Expression, Self::Error> {
        if let Some(op) = self
            .program_context
            .get_binary_operator(&domain_func_app.domain_name, &domain_func_app.function_name)
        {
            if matches!(op, vir_low::BinaryOpKind::Mul) {
                let domain_func_app_original =
                    vir_low::Expression::DomainFuncApp(domain_func_app.clone());
                // eprintln!("simplify: {domain_func_app}");
                // self.intern_arguments_and_saturate(&domain_func_app.arguments)?;
                let (found_constant, maybe_constants) =
                    self.try_resolve_constants(&domain_func_app.arguments)?;
                if found_constant {
                    let constructor = self
                        .program_context
                        .get_constant_constructor(&domain_func_app.domain_name);
                    let destructor = self
                        .program_context
                        .get_constant_destructor(&domain_func_app.domain_name);
                    let mut constructor_arguments = Vec::new();
                    for (maybe_constant, argument) in maybe_constants
                        .into_iter()
                        .zip(std::mem::take(&mut domain_func_app.arguments).into_iter())
                    {
                        if let Some((constructor_name, constant)) = maybe_constant {
                            assert_eq!(constructor_name.unwrap(), constructor.name);
                            constructor_arguments.push(constant);
                        } else {
                            let destructor = vir_low::Expression::domain_function_call(
                                &domain_func_app.domain_name,
                                destructor.name.clone(),
                                vec![argument],
                                vir_low::Type::Int,
                            );
                            constructor_arguments.push(destructor);
                        }
                    }
                    let right = constructor_arguments.pop().unwrap();
                    let left = constructor_arguments.pop().unwrap();
                    assert!(constructor_arguments.is_empty());
                    let result = vir_low::Expression::domain_function_call(
                        domain_func_app.domain_name,
                        constructor.name.clone(),
                        vec![vir_low::Expression::multiply(left, right)],
                        domain_func_app.return_type,
                    )
                    .set_default_position(domain_func_app.position);

                    if result.is_heap_independent()
                        && domain_func_app_original.is_heap_independent()
                    {
                        self.solver
                            .assume_equal(&result, &domain_func_app_original)?;
                    }
                    return Ok(result);
                } else if config::error_non_linear_arithmetic_simp() {
                    let span = self
                        .program_context
                        .env()
                        .get_span(domain_func_app.position)
                        .unwrap();
                    error_internal!(span => "failed to rewrite multiplication: {}", domain_func_app);
                    // unimplemented!("failed to rewrite multiplication: {domain_func_app}");
                }
            }
        }
        self.fallible_fold_domain_func_app(domain_func_app)
            .map(vir_low::Expression::DomainFuncApp)
    }

    fn fallible_fold_binary_op_enum(
        &mut self,
        mut binary_op: vir_low::BinaryOp,
    ) -> Result<vir_low::Expression, Self::Error> {
        if matches!(binary_op.op_kind, vir_low::BinaryOpKind::Mul)
            && !binary_op.left.is_constant()
            && !binary_op.right.is_constant()
        {
            let arguments = vec![(*binary_op.left).clone(), (*binary_op.right).clone()];
            // self.intern_arguments_and_saturate(&arguments)?;
            let (found_constant, maybe_constants) = self.try_resolve_constants(&arguments)?;
            if found_constant {
                let mut binary_op_arguments = Vec::new();
                for (maybe_constant, argument) in
                    maybe_constants.into_iter().zip(arguments.into_iter())
                {
                    if let Some((constructor_name, constant)) = maybe_constant {
                        assert!(constructor_name.is_none());
                        binary_op_arguments.push(constant);
                    } else {
                        binary_op_arguments.push(argument);
                    }
                }
                let right = binary_op_arguments.pop().unwrap();
                let left = binary_op_arguments.pop().unwrap();
                assert!(binary_op_arguments.is_empty());
                binary_op.left = Box::new(left);
                binary_op.right = Box::new(right);
                return Ok(vir_low::Expression::BinaryOp(binary_op));
            } else if config::error_non_linear_arithmetic_simp() {
                unimplemented!(
                    "failed to rewrite multiplication: {} * {}",
                    arguments[0],
                    arguments[1]
                );
            }
        }
        self.fallible_fold_binary_op(binary_op)
            .map(vir_low::Expression::BinaryOp)
    }
}
