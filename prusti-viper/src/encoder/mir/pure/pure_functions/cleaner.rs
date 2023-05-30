use crate::encoder::{
    errors::{SpannedEncodingError, SpannedEncodingResult},
    Encoder,
};
use prusti_interface::data::ProcedureDefId;
use prusti_rustc_interface::span::Span;
use vir_crate::{
    common::{expression::SyntacticEvaluation, position::Positioned},
    high::{
        self as vir_high,
        visitors::{
            default_fallible_fold_acc_predicate, default_fallible_fold_binary_op,
            default_fallible_fold_builtin_func_app, default_fallible_fold_unfolding,
            ExpressionFallibleFolder,
        },
    },
};

/// When encoding an assertion we sometimes get strange artefacts as a result of
/// using procedural macros. This functions removes them.
pub(super) fn clean_encoding_result<'p, 'v: 'p, 'tcx: 'v>(
    encoder: &'p Encoder<'v, 'tcx>,
    expression: vir_high::Expression,
    proc_def_id: ProcedureDefId,
    span: Span,
) -> SpannedEncodingResult<vir_high::Expression> {
    let _position = expression.position();
    let mut cleaner = Cleaner { encoder, span };

    let expression = cleaner.fallible_fold_expression(expression)?;
    let expression = expression.simplify();
    check_permission_always_positive(proc_def_id, &expression)?;

    Ok(expression)
}

struct Cleaner<'p, 'v: 'p, 'tcx: 'v> {
    encoder: &'p Encoder<'v, 'tcx>,
    span: Span,
}

fn peel_addr_of(place: vir_high::Expression) -> vir_high::Expression {
    match place {
        vir_high::Expression::AddrOf(vir_high::AddrOf { base, .. }) => *base,
        _ => {
            unreachable!("must be addr_of: {}", place)
        }
    }
}

fn clean_acc_predicate(predicate: vir_high::Predicate) -> vir_high::Predicate {
    match predicate {
        vir_high::Predicate::OwnedNonAliased(mut predicate) => {
            // FIXME: Rename OwnedNonAliased to Owned.
            predicate.place = peel_addr_of(predicate.place);
            if !predicate.place.is_behind_pointer_dereference() {
                // FIXME: A proper error message
                unimplemented!("Must be behind pointer dereference: {}", predicate.place)
            }
            vir_high::Predicate::OwnedNonAliased(predicate)
        }
        // vir_high::Predicate::OwnedNonAliased(vir_high::OwnedNonAliased {
        //     place: vir_high::Expression::AddrOf(vir_high::AddrOf { base, .. }), position
        // }) => {
        //     vir_high::Predicate::owned_non_aliased(*base, position)
        // }
        vir_high::Predicate::MemoryBlockHeap(mut predicate) => {
            predicate.address = peel_addr_of(predicate.address);
            if !predicate.address.is_behind_pointer_dereference() {
                // FIXME: A proper error message
                unimplemented!("Must be behind pointer dereference: {}", predicate.address)
            }
            vir_high::Predicate::MemoryBlockHeap(predicate)
        }
        vir_high::Predicate::MemoryBlockHeapRange(predicate) => {
            // predicate.address = peel_addr_of(predicate.address);
            vir_high::Predicate::MemoryBlockHeapRange(predicate)
        }
        vir_high::Predicate::MemoryBlockHeapDrop(mut predicate) => {
            predicate.address = peel_addr_of(predicate.address);
            if !predicate.address.is_behind_pointer_dereference() {
                // FIXME: A proper error message
                unimplemented!("Must be behind pointer dereference: {}", predicate.address)
            }
            vir_high::Predicate::MemoryBlockHeapDrop(predicate)
        }
        vir_high::Predicate::OwnedRange(predicate) => {
            // predicate.address = peel_addr_of(predicate.address);
            vir_high::Predicate::OwnedRange(predicate)
        }
        _ => unimplemented!("{:?}", predicate),
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> ExpressionFallibleFolder for Cleaner<'p, 'v, 'tcx> {
    type Error = SpannedEncodingError;

    fn fallible_fold_acc_predicate(
        &mut self,
        mut acc_predicate: vir_high::AccPredicate,
    ) -> Result<vir_high::AccPredicate, Self::Error> {
        let predicate = clean_acc_predicate(*acc_predicate.predicate);
        acc_predicate.predicate = Box::new(predicate);
        default_fallible_fold_acc_predicate(self, acc_predicate)
    }

    fn fallible_fold_unfolding(
        &mut self,
        mut unfolding: vir_high::Unfolding,
    ) -> Result<vir_high::Unfolding, Self::Error> {
        let predicate = clean_acc_predicate(*unfolding.predicate);
        unfolding.predicate = Box::new(predicate);
        default_fallible_fold_unfolding(self, unfolding)
    }

    fn fallible_fold_conditional_enum(
        &mut self,
        conditional: vir_high::Conditional,
    ) -> Result<vir_high::Expression, Self::Error> {
        let conditional = self.fallible_fold_conditional(conditional)?;
        let expression = match conditional {
            _ if conditional.guard.is_true() => *conditional.then_expr,
            _ if conditional.guard.is_false() => *conditional.else_expr,
            vir_high::Conditional {
                guard:
                    box vir_high::Expression::UnaryOp(vir_high::UnaryOp {
                        op_kind: vir_high::UnaryOpKind::Not,
                        argument: guard,
                        ..
                    }),
                then_expr,
                else_expr,
                position,
            } if then_expr.is_false() || then_expr.is_true() => {
                // This happens due to short-circuiting in Rust.
                if then_expr.is_false() {
                    vir_high::Expression::BinaryOp(vir_high::BinaryOp {
                        op_kind: vir_high::BinaryOpKind::And,
                        left: guard,
                        right: else_expr,
                        position,
                    })
                } else if then_expr.is_true() {
                    if !guard.is_pure() {
                        return Err(SpannedEncodingError::incorrect(
                            "permission predicates can be only in positive positions",
                            self.span,
                        ));
                    }
                    vir_high::Expression::BinaryOp(vir_high::BinaryOp {
                        op_kind: vir_high::BinaryOpKind::Implies,
                        left: guard,
                        right: else_expr,
                        position,
                    })
                } else {
                    unreachable!();
                }
            }
            _ if conditional.else_expr.is_true() => {
                // Clean up stuff generated by `own!` expansion.
                if !conditional.guard.is_pure() {
                    unimplemented!("TODO: A proper error message: {conditional}")
                }
                vir_high::Expression::BinaryOp(vir_high::BinaryOp {
                    op_kind: vir_high::BinaryOpKind::Implies,
                    left: conditional.guard,
                    right: conditional.then_expr,
                    position: conditional.position,
                })
            }
            _ if conditional.else_expr.is_false() => {
                // Clean up stuff generated by `own!` expansion.
                vir_high::Expression::BinaryOp(vir_high::BinaryOp {
                    op_kind: vir_high::BinaryOpKind::And,
                    left: conditional.guard,
                    right: conditional.then_expr,
                    position: conditional.position,
                })
            }
            _ => {
                if !conditional.guard.is_pure() {
                    unimplemented!("TODO: A proper error message: {conditional}")
                }
                return Ok(vir_high::Expression::Conditional(conditional));
            }
        };
        Ok(expression)
    }

    fn fallible_fold_binary_op(
        &mut self,
        binary_op: vir_high::BinaryOp,
    ) -> Result<vir_high::BinaryOp, Self::Error> {
        if binary_op.op_kind != vir_high::BinaryOpKind::And && !binary_op.left.is_pure() {
            unimplemented!("TODO: A proper error message.")
        }
        if !matches!(
            binary_op.op_kind,
            vir_high::BinaryOpKind::And | vir_high::BinaryOpKind::Implies
        ) && !binary_op.right.is_pure()
        {
            unimplemented!("TODO: A proper error message.")
        }
        default_fallible_fold_binary_op(self, binary_op)
    }

    fn fallible_fold_builtin_func_app(
        &mut self,
        mut builtin_func_app: vir_high::BuiltinFuncApp,
    ) -> Result<vir_high::BuiltinFuncApp, Self::Error> {
        if matches!(
            builtin_func_app.function,
            vir_high::BuiltinFunc::MemoryBlockBytes
        ) {
            let address = builtin_func_app.arguments[0].clone();
            builtin_func_app.arguments[0] = peel_addr_of(address);
        }
        default_fallible_fold_builtin_func_app(self, builtin_func_app)
    }

    fn fallible_fold_quantifier(
        &mut self,
        quantifier: vir_high::Quantifier,
    ) -> Result<vir_high::Quantifier, Self::Error> {
        // Quantifier bodies are already cleaned.
        Ok(quantifier)
    }
}

fn check_permission_always_positive(
    proc_def_id: ProcedureDefId,
    expression: &vir_high::Expression,
) -> SpannedEncodingResult<()> {
    match expression {
        vir_high::Expression::AccPredicate(_) => {
            // Accessibility predicate in the positive position.
        }
        vir_high::Expression::BinaryOp(binary_op_expression) => {
            match binary_op_expression.op_kind {
                vir_high::BinaryOpKind::And => {
                    check_permission_always_positive(proc_def_id, &binary_op_expression.left)?;
                    check_permission_always_positive(proc_def_id, &binary_op_expression.right)?;
                }
                vir_high::BinaryOpKind::Implies => {
                    assert!(
                        binary_op_expression.left.is_pure(),
                        "{proc_def_id:?} {expression}"
                    );
                    check_permission_always_positive(proc_def_id, &binary_op_expression.right)?;
                }
                _ => {
                    assert!(expression.is_pure(), "{proc_def_id:?} {expression}");
                }
            }
        }
        _ => {
            assert!(expression.is_pure(), "{proc_def_id:?} {expression}");
        }
    }
    Ok(())
}
