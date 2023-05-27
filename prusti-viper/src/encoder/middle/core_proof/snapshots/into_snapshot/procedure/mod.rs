//! Code for encoding expressions into snapshots in non-pure contexts such as
//! procedure bodies. Most important difference from `pure` is that this
//! encoding uses SSA.

use super::{common::IntoSnapshotLowerer, PredicateKind};
use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        addresses::AddressesInterface,
        builtin_methods::CallContext,
        lowerer::{FunctionsLowererInterface, Lowerer},
        places::PlacesInterface,
        pointers::PointersInterface,
        predicates::{PredicatesMemoryBlockInterface, PredicatesOwnedInterface},
        references::ReferencesInterface,
        snapshots::SnapshotVariablesInterface,
        utils::bound_variable_stack::{BoundVariableStack, BoundVariableStackMiddle},
    },
};
use vir_crate::{
    common::identifier::WithIdentifier,
    low::{self as vir_low},
    middle::{self as vir_mid, operations::ty::Typed},
};

mod traits;

pub(in super::super::super) use self::traits::{
    IntoProcedureAssertion, IntoProcedureBoolExpression, IntoProcedureFinalSnapshot,
    IntoProcedureSnapshot,
};

pub(in super::super::super::super) struct ProcedureSnapshot {
    old_label: Option<String>,
    deref_to_final: bool,
    is_assertion: bool,
    in_heap_assertions: Vec<vir_low::Expression>,
    predicate_kind: PredicateKind,
    bound_variable_stack: BoundVariableStack,
}

impl ProcedureSnapshot {
    pub(in super::super) fn new_for_owned() -> Self {
        Self {
            old_label: None,
            deref_to_final: false,
            is_assertion: false,
            in_heap_assertions: Vec::new(),
            predicate_kind: PredicateKind::Owned,
            bound_variable_stack: Default::default(),
        }
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> IntoSnapshotLowerer<'p, 'v, 'tcx> for ProcedureSnapshot {
    fn expression_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        expression: &vir_mid::Expression,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        if !lowerer.use_heap_variable()?
            && expression.is_place()
            && expression.get_last_dereferenced_pointer().is_some()
        {
            // let address = lowerer.encode_expression_as_place_address(expression)?;
            // let place = lowerer.encode_expression_as_place(expression)?;
            // let root_address = lowerer.extract_root_address(expression)?;
            let ty = expression.get_type();
            // return lowerer.owned_non_aliased_snap(CallContext::Procedure, ty, ty, place, root_address);
            return self.owned_non_aliased_snap(lowerer, ty, expression);
        }
        self.expression_to_snapshot_impl(lowerer, expression, expect_math_bool)
    }

    fn variable_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        variable: &vir_mid::VariableDecl,
    ) -> SpannedEncodingResult<vir_low::VariableDecl> {
        if self.bound_variable_stack.contains(variable) {
            return Ok(vir_low::VariableDecl::new(
                variable.name.clone(),
                self.type_to_snapshot(lowerer, &variable.ty)?,
            ));
        }
        if let Some(label) = &self.old_label {
            lowerer.snapshot_variable_version_at_label(variable, label)
        } else {
            lowerer.current_snapshot_variable_version(variable)
        }
    }

    fn func_app_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        app: &vir_mid::FuncApp,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let arguments =
            self.expression_vec_to_snapshot(lowerer, &app.arguments, expect_math_bool)?;
        let return_type = self.type_to_snapshot(lowerer, &app.return_type)?;
        let func_app = lowerer.call_pure_function_in_procedure_context(
            app.get_identifier(),
            arguments,
            return_type,
            app.position,
        )?;
        let result = vir_low::Expression::FuncApp(func_app);
        self.ensure_bool_expression(lowerer, &app.return_type, result, expect_math_bool)
    }

    fn labelled_old_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        old: &vir_mid::LabelledOld,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let parent_old_label = std::mem::replace(&mut self.old_label, Some(old.label.clone()));
        let result = self.expression_to_snapshot(lowerer, &old.base, expect_math_bool);
        self.old_label = parent_old_label;
        result
    }

    fn deref_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        deref: &vir_mid::Deref,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let result = if self.deref_to_final {
            self.deref_to_final = false;
            let base_snapshot =
                self.expression_to_snapshot(lowerer, &deref.base, expect_math_bool)?;
            self.deref_to_final = true;
            lowerer.reference_target_final_snapshot(
                deref.base.get_type(),
                base_snapshot,
                deref.position,
            )?
        } else {
            let base_snapshot =
                self.expression_to_snapshot(lowerer, &deref.base, expect_math_bool)?;
            if deref.base.get_type().is_reference() {
                lowerer.reference_target_current_snapshot(
                    deref.base.get_type(),
                    base_snapshot,
                    deref.position,
                )?
            } else {
                lowerer.pointer_target_snapshot(
                    deref.base.get_type(),
                    &self.old_label,
                    base_snapshot,
                    deref.position,
                )?
            }
        };
        self.ensure_bool_expression(lowerer, deref.get_type(), result, expect_math_bool)
    }

    fn acc_predicate_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        acc_predicate: &vir_mid::AccPredicate,
        _expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        assert!(self.is_assertion);
        // fn in_heap<'p, 'v, 'tcx>(
        //     old_label: &Option<String>,
        //     place: &vir_mid::Expression,
        //     lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        // ) -> SpannedEncodingResult<vir_low::Expression> {
        //     let in_heap = if let Some(pointer_place) = place.get_last_dereferenced_pointer() {
        //         let pointer = pointer_place.to_procedure_snapshot(lowerer)?;
        //         let address =
        //             lowerer.pointer_address(pointer_place.get_type(), pointer, place.position())?;
        //         let heap = lowerer.heap_variable_version_at_label(old_label)?;
        //         vir_low::Expression::container_op_no_pos(
        //             vir_low::ContainerOpKind::MapContains,
        //             heap.ty.clone(),
        //             vec![heap.into(), address],
        //         )
        //     } else {
        //         unimplemented!("TODO: Proper error message: {:?}", place);
        //     };
        //     Ok(in_heap)
        // }
        let expression = match &*acc_predicate.predicate {
            vir_mid::Predicate::OwnedNonAliased(predicate) => {
                let _ty = predicate.place.get_type();
                let _place = lowerer.encode_expression_as_place(&predicate.place)?;
                let _root_address = lowerer.extract_root_address(&predicate.place)?;
                let _snapshot = predicate.place.to_procedure_snapshot(lowerer)?; // FIXME: This is probably wrong. It should take into account the current old.
                                                                                 // if lowerer.use_heap_variable()? {
                                                                                 //     let in_heap = in_heap(&self.old_label, &predicate.place, lowerer)?;
                                                                                 //     self.in_heap_assertions.push(in_heap);
                                                                                 // }
                                                                                 // let acc =
                unimplemented!();
                // lowerer.owned_aliased(
                //     CallContext::Procedure,
                //     ty,
                //     ty,
                //     place,
                //     root_address,
                //     snapshot,
                //     None,
                // )?
                // ;
                // vir_low::Expression::and(in_heap, acc)
            }
            vir_mid::Predicate::OwnedRange(_predicate) => {
                unimplemented!();
                // let ty = predicate.address.get_type();
                // let address = predicate.address.to_procedure_snapshot(lowerer)?;
                // let start_index = predicate.start_index.to_procedure_snapshot(lowerer)?;
                // let end_index = predicate.end_index.to_procedure_snapshot(lowerer)?;
                // lowerer.owned_aliased_range(
                //     CallContext::Procedure,
                //     ty,
                //     ty,
                //     address,
                //     start_index,
                //     end_index,
                //     None,
                // )?
            }
            vir_mid::Predicate::MemoryBlockHeap(predicate) => {
                let place = lowerer.encode_expression_as_place_address(&predicate.address)?;
                let size = predicate.size.to_procedure_snapshot(lowerer)?;
                // if lowerer.use_heap_variable()? {
                //     let in_heap = in_heap(&self.old_label, &predicate.address, lowerer)?;
                //     self.in_heap_assertions.push(in_heap);
                // }
                // let acc =
                lowerer.encode_memory_block_acc(place, size, acc_predicate.position)?
                //;
                // vir_low::Expression::and(in_heap, acc)
            }
            vir_mid::Predicate::MemoryBlockHeapRange(_predicate) => {
                unimplemented!();
                // let pointer_value = predicate.address.to_procedure_snapshot(lowerer)?;
                // let address = lowerer.pointer_address(
                //     predicate.address.get_type(),
                //     pointer_value,
                //     predicate.position,
                // )?;
                // let size = predicate.size.to_procedure_snapshot(lowerer)?;
                // let start_index = predicate.start_index.to_procedure_snapshot(lowerer)?;
                // let end_index = predicate.end_index.to_procedure_snapshot(lowerer)?;
                // lowerer.encode_memory_block_range_acc(
                //     address,
                //     size,
                //     start_index,
                //     end_index,
                //     acc_predicate.position,
                // )?
            }
            vir_mid::Predicate::MemoryBlockHeapDrop(predicate) => {
                let place = lowerer.encode_expression_as_place_address(&predicate.address)?; // FIXME: This looks very wrong.
                let size = predicate.size.to_procedure_snapshot(lowerer)?;
                // if lowerer.use_heap_variable()? {
                //     let in_heap = in_heap(&self.old_label, &predicate.address, lowerer)?;
                //     self.in_heap_assertions.push(in_heap);
                // }
                // let acc =
                lowerer.encode_memory_block_heap_drop_acc(place, size, acc_predicate.position)?
                // ;
                // vir_low::Expression::and(in_heap, acc)
            }
            _ => unimplemented!("{acc_predicate}"),
        };
        Ok(expression)
    }

    fn owned_non_aliased_snap(
        &mut self,
        _lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        _ty: &vir_mid::Type,
        _pointer_place: &vir_mid::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        unimplemented!();
        // let place = lowerer.encode_expression_as_place(pointer_place)?;
        // let root_address = lowerer.extract_root_address(pointer_place)?;
        // match &self.predicate_kind {
        //     PredicateKind::Owned => lowerer.owned_non_aliased_snap(
        //         CallContext::Procedure,
        //         ty,
        //         ty,
        //         place,
        //         root_address,
        //         pointer_place.position(),
        //     ),
        //     PredicateKind::FracRef { lifetime } => todo!(),
        //     PredicateKind::UniqueRef { lifetime, is_final } => {
        //         let TODO_target_slice_len = None;
        //         lowerer.unique_ref_snap(
        //             CallContext::Procedure,
        //             ty,
        //             ty,
        //             place,
        //             root_address,
        //             lifetime.clone(),
        //             TODO_target_slice_len,
        //             *is_final,
        //         )
        //     }
        // }
        // if let Some(reference_place) = pointer_place.get_first_dereferenced_reference() {
        //     let vir_mid::Type::Reference(reference_type) = reference_place.get_type() else {
        //         unreachable!()
        //     };
        //     let TODO_target_slice_len = None;
        //     let lifetime = lowerer
        //         .encode_lifetime_const_into_procedure_variable(reference_type.lifetime.clone())?;
        //     match reference_type.uniqueness {
        //         vir_mid::ty::Uniqueness::Unique => lowerer.unique_ref_snap(
        //             CallContext::Procedure,
        //             ty,
        //             ty,
        //             place,
        //             root_address,
        //             lifetime.into(),
        //             TODO_target_slice_len,
        //             self.deref_to_final,
        //         ),
        //         vir_mid::ty::Uniqueness::Shared => lowerer.frac_ref_snap(
        //             CallContext::Procedure,
        //             ty,
        //             ty,
        //             place,
        //             root_address,
        //             lifetime.into(),
        //             TODO_target_slice_len,
        //         ),
        //     }
        // } else {
        // lowerer.owned_non_aliased_snap(
        //     CallContext::Procedure,
        //     ty,
        //     ty,
        //     place,
        //     root_address,
        //     pointer_place.position(),
        // )
        // }
        // // TODO: Check whether the place is behind a shared/mutable reference and use the appropriate function
        // eprintln!("pointer_place: {}", pointer_place);
        // eprintln!("pointer_place: {:?}", pointer_place);
    }

    fn call_context(&self) -> CallContext {
        CallContext::Procedure
    }

    fn push_bound_variables(
        &mut self,
        variables: &[vir_mid::VariableDecl],
    ) -> SpannedEncodingResult<()> {
        self.bound_variable_stack.push(variables);
        Ok(())
    }

    fn pop_bound_variables(&mut self) -> SpannedEncodingResult<()> {
        self.bound_variable_stack.pop();
        Ok(())
    }

    // fn unfolding_to_snapshot(
    //     &mut self,
    //     lowerer: &mut Lowerer<'p, 'v, 'tcx>,
    //     unfolding: &vir_mid::Unfolding,
    //     expect_math_bool: bool,
    // ) -> SpannedEncodingResult<vir_low::Expression> {
    //     let predicate = match &*unfolding.predicate {
    //         vir_mid::Predicate::OwnedNonAliased(predicate) => {
    //             let ty = predicate.place.get_type();
    //             lowerer.mark_owned_predicate_as_unfolded(ty)?;
    //             let place = lowerer.encode_expression_as_place(&predicate.place)?;
    //             let root_address = lowerer.extract_root_address(&predicate.place)?;
    //             let snapshot = predicate.place.to_procedure_snapshot(lowerer)?; // FIXME: This is probably wrong. It should take into account the current old.
    //             lowerer
    //                 .owned_non_aliased(
    //                     CallContext::Procedure,
    //                     ty,
    //                     ty,
    //                     place,
    //                     root_address,
    //                     snapshot,
    //                     None,
    //                 )?
    //                 .unwrap_predicate_access_predicate()
    //         }
    //         _ => unimplemented!("{unfolding}"),
    //     };
    //     let body = self.expression_to_snapshot(lowerer, &unfolding.body, expect_math_bool)?;
    //     let expression = vir_low::Expression::unfolding(predicate, body, unfolding.position);
    //     Ok(expression)
    // }
}
