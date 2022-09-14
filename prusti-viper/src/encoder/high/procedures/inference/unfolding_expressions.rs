use crate::encoder::errors::{SpannedEncodingError, SpannedEncodingResult};
use vir_crate::{
    common::position::Positioned,
    typed::{
        self as vir_typed,
        operations::ty::Typed,
        visitors::{
            default_fallible_fold_binary_op, default_fallible_fold_expression,
            ExpressionFallibleFolder,
        },
    },
};

pub(super) fn add_unfolding_expressions(
    expression: vir_typed::Expression,
) -> SpannedEncodingResult<vir_typed::Expression> {
    // let mut ensurer = Ensurer {
    //     syntactically_framed_places: Vec::new(),
    // };
    // ensurer.fallible_fold_expression(expression)
    Ok(expression)
}

struct Ensurer {
    syntactically_framed_places: Vec<vir_typed::Expression>,
}

impl Ensurer {
    fn add_unfolding(
        &self,
        place: vir_typed::Expression,
    ) -> SpannedEncodingResult<vir_typed::Expression> {
        for framing_place in &self.syntactically_framed_places {
            let mut unfolding_stack = Vec::new();
            if self.add_syntactic_unfolding_rec(&place, framing_place, &mut unfolding_stack)? {
                let place = self.apply_unfolding_stack(place, unfolding_stack);
                return Ok(place);
            }
        }
        let mut unfolding_stack = Vec::new();
        self.add_self_unfolding_rec(&place, &mut unfolding_stack)?;
        let place = self.apply_unfolding_stack(place, unfolding_stack);
        Ok(place)
    }

    fn apply_unfolding_stack(
        &self,
        mut place: vir_typed::Expression,
        unfolding_stack: Vec<vir_typed::Expression>,
    ) -> vir_typed::Expression {
        for unfolded_place in unfolding_stack {
            let position = place.position();
            place = vir_typed::Expression::unfolding(
                vir_typed::Predicate::owned_non_aliased(unfolded_place, position),
                place,
                position,
            );
        }
        place
    }

    fn add_syntactic_unfolding_rec(
        &self,
        place: &vir_typed::Expression,
        framing_place: &vir_typed::Expression,
        unfolding_stack: &mut Vec<vir_typed::Expression>,
    ) -> SpannedEncodingResult<bool> {
        if place == framing_place {
            return Ok(true);
        } else if !place.is_deref() {
            if let Some(parent) = place.get_parent_ref() {
                if self.add_syntactic_unfolding_rec(framing_place, parent, unfolding_stack)? {
                    unfolding_stack.push(parent.clone());
                    return Ok(true);
                }
            }
        };
        Ok(false)
    }

    /// Just unfold on all levels except on deref.
    ///
    /// FIXME: This should take into account what places are actually framed by
    /// the structural invariant. For example, if the invariant contains
    /// `own!((*self.p).x)` (that is, it frames only one field of the struct),
    /// then we currently will generate one unfolding too many (we would
    /// generate unfolding of `self.p` even though we should not).
    fn add_self_unfolding_rec(
        &self,
        place: &vir_typed::Expression,
        unfolding_stack: &mut Vec<vir_typed::Expression>,
    ) -> SpannedEncodingResult<()> {
        if let Some(parent) = place.get_parent_ref() {
            if !parent.get_type().is_pointer() {
                unfolding_stack.push(parent.clone());
            }
            self.add_self_unfolding_rec(parent, unfolding_stack)?;
        }
        Ok(())
    }

    //     fn add_unfolding(&self, place: vir_typed::Expression) -> SpannedEncodingResult<vir_typed::Expression> {
    //         for framing_place in &self.syntactically_framed_places {
    // let mut             unfolding_stack = Vec::new();
    //             if let Some(mut new_place) = self.add_unfolding_rec(&place, framing_place, &mut unfolding_stack)? {
    //                 eprintln!("place: {}", place);
    //                 eprintln!("new_place: {}", new_place);
    //                 for unfolded_place in unfolding_stack {
    //                     eprintln!("  unfolded_place: {}", unfolded_place);
    //                     let position =new_place.position();
    //                     new_place = vir_typed::Expression::unfolding(
    //                         vir_typed::Predicate::owned_non_aliased(unfolded_place, position),
    //                         new_place, position);
    //                 }
    //                 eprintln!("final_place: {}", new_place);
    //                 return Ok(new_place);
    //             }
    //         }
    //         Ok(place)
    //     }

    // fn add_unfolding_rec(&self, place: &vir_typed::Expression, framing_place: &vir_typed::Expression,
    //     unfolding_stack: &mut Vec<vir_typed::Expression>,
    // ) -> SpannedEncodingResult<Option<vir_typed::Expression>> {
    //     let new_place = if place == framing_place {
    //         Some(place.clone())
    //     } else {
    //         if place.is_deref() {
    //             None
    //         } else {
    //             if let Some(parent) = place.get_parent_ref() {
    //                 let result = self.add_unfolding_rec(framing_place, parent, unfolding_stack)?;
    //                 if result.is_some() {
    //                     unfolding_stack.push(parent.clone());
    //                 }
    //                 result
    //             } else {
    //                 None
    //             }
    //         }
    //     };
    //     Ok(new_place)
    // }
}

impl ExpressionFallibleFolder for Ensurer {
    type Error = SpannedEncodingError;

    fn fallible_fold_expression(
        &mut self,
        expression: vir_typed::Expression,
    ) -> Result<vir_typed::Expression, Self::Error> {
        if expression.is_place() && expression.get_last_dereferenced_pointer().is_some() {
            self.add_unfolding(expression)
        } else {
            default_fallible_fold_expression(self, expression)
        }
    }

    fn fallible_fold_binary_op(
        &mut self,
        mut binary_op: vir_typed::BinaryOp,
    ) -> Result<vir_typed::BinaryOp, Self::Error> {
        match binary_op.op_kind {
            vir_typed::BinaryOpKind::And => {
                if let vir_typed::Expression::AccPredicate(acc_predicate) = &*binary_op.left {
                    match &*acc_predicate.predicate {
                        vir_typed::Predicate::LifetimeToken(_)
                        | vir_typed::Predicate::MemoryBlockStack(_)
                        | vir_typed::Predicate::MemoryBlockStackDrop(_)
                        | vir_typed::Predicate::MemoryBlockHeap(_)
                        | vir_typed::Predicate::MemoryBlockHeapRange(_)
                        | vir_typed::Predicate::MemoryBlockHeapDrop(_) => {
                            default_fallible_fold_binary_op(self, binary_op)
                        }
                        vir_typed::Predicate::OwnedNonAliased(predicate) => {
                            let place = predicate.place.clone();
                            binary_op.left = self.fallible_fold_expression_boxed(binary_op.left)?;
                            self.syntactically_framed_places.push(place);
                            binary_op.right =
                                self.fallible_fold_expression_boxed(binary_op.right)?;
                            self.syntactically_framed_places.pop();
                            Ok(binary_op)
                        }
                        vir_typed::Predicate::OwnedRange(_) => todo!(),
                        vir_typed::Predicate::OwnedSet(_) => todo!(),
                        vir_typed::Predicate::UniqueRef(_) => todo!(),
                        vir_typed::Predicate::UniqueRefRange(_) => todo!(),
                        vir_typed::Predicate::FracRef(_) => todo!(),
                        vir_typed::Predicate::FracRefRange(_) => todo!(),
                    }
                } else {
                    default_fallible_fold_binary_op(self, binary_op)
                }
            }
            _ => default_fallible_fold_binary_op(self, binary_op),
        }
    }
}
