use crate::encoder::{
    errors::SpannedEncodingResult,
    high::types::HighTypeEncoderInterface,
    middle::core_proof::{
        builtin_methods::CallContext,
        lowerer::Lowerer,
        places::PlacesInterface,
        pointers::PointersInterface,
        predicates::{PredicatesMemoryBlockInterface, PredicatesOwnedInterface},
        references::ReferencesInterface,
        snapshots::{IntoSnapshotLowerer, SnapshotValuesInterface, SnapshotVariablesInterface},
    },
};

use std::collections::BTreeMap;
use vir_crate::{
    common::{expression::BinaryOperationHelpers, position::Positioned},
    low::{self as vir_low},
    middle::{self as vir_mid, operations::ty::Typed},
};

// TODO: Delete this file.
pub(in super::super::super) struct AssertionEncoder<'a> {
    /// A map from field names to arguments that are being assigned to these
    /// fields.
    field_arguments: BTreeMap<String, vir_low::Expression>,
    heap: &'a Option<vir_low::VariableDecl>,
    result_value: Option<vir_low::VariableDecl>,
    replace_self_with_result_value: bool,
    in_function: bool,
}

impl<'a> AssertionEncoder<'a> {
    pub(in super::super::super) fn new(
        decl: &vir_mid::type_decl::Struct,
        operand_values: Vec<vir_low::Expression>,
        heap: &'a Option<vir_low::VariableDecl>,
    ) -> Self {
        let mut field_arguments = BTreeMap::default();
        // assert_eq!(decl.fields.len(), operand_values.len()); FIXME: Split
        // into two assertion encoders: one that uses result value and one that
        // usess field_arguments.
        for (field, operand) in decl.fields.iter().zip(operand_values.into_iter()) {
            assert!(field_arguments
                .insert(field.name.clone(), operand)
                .is_none());
        }
        Self {
            field_arguments,
            heap,
            result_value: None,
            replace_self_with_result_value: false,
            in_function: false,
        }
    }

    // FIXME: Code duplication.
    fn pointer_deref_into_address<'p, 'v, 'tcx>(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        place: &vir_mid::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        if let Some(deref_place) = place.get_last_dereferenced_pointer() {
            let base_snapshot = self.expression_to_snapshot(lowerer, deref_place, true)?;
            let ty = deref_place.get_type();
            lowerer.pointer_address(ty, base_snapshot, place.position())
            // match deref_place {
            //     vir_mid::Expression::Deref(deref) => {
            //         let base_snapshot = self.expression_to_snapshot(lowerer, &deref.base, true)?;
            //         let ty = deref.base.get_type();
            //         assert!(ty.is_pointer());
            //         lowerer.pointer_address(ty, base_snapshot, place.position())
            //     }
            //     _ => unreachable!(),
            // }
        } else {
            unreachable!()
        }
        // PlaceExpressionDomainEncoder::encode_expression(self, place, lowerer)
    }

    pub(super) fn address_in_heap<'p, 'v, 'tcx>(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        pointer_place: &vir_mid::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let pointer = self.expression_to_snapshot(lowerer, pointer_place, true)?;
        let address =
            lowerer.pointer_address(pointer_place.get_type(), pointer, pointer_place.position())?;
        let in_heap = vir_low::Expression::container_op_no_pos(
            vir_low::ContainerOpKind::MapContains,
            self.heap.as_ref().unwrap().ty.clone(),
            vec![self.heap.clone().unwrap().into(), address],
        );
        Ok(in_heap)
    }

    // pub(in super::super::super) fn set_in_function(&mut self) {
    //     assert!(!self.in_function);
    //     self.in_function = true;
    // }

    pub(in super::super::super) fn set_result_value(
        &mut self,
        result_value: vir_low::VariableDecl,
    ) {
        assert!(self.result_value.is_none());
        self.result_value = Some(result_value);
    }

    pub(super) fn unset_result_value(&mut self) {
        assert!(self.result_value.is_some());
        self.result_value = None;
    }

    fn acc_predicate_to_snapshot_precondition<'p, 'v, 'tcx>(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        acc_predicate: &vir_mid::AccPredicate,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        assert!(expect_math_bool);
        let expression = match &*acc_predicate.predicate {
            vir_mid::Predicate::OwnedNonAliased(_predicate) => {
                unimplemented!("Outdated code? TODO: Remove?");
                // let ty = predicate.place.get_type();
                // let place = lowerer.encode_expression_as_place(&predicate.place)?;
                // // eprintln!("predicate: {}", predicate);
                // let root_address = self.pointer_deref_into_address(lowerer, &predicate.place)?;
                // // eprintln!("root_address2: {}", root_address);
                // // let deref = predicate.place.clone().unwrap_deref();
                // // let base_snapshot =
                // //     self.expression_to_snapshot(lowerer, &deref.base, expect_math_bool)?;
                // // let snapshot = lowerer.pointer_target_snapshot_in_heap(
                // //     deref.base.get_type(),
                // //     self.heap.clone(),
                // //     base_snapshot,
                // //     deref.position,
                // // )?;

                // let snapshot = if config::use_snapshot_parameters_in_predicates() {
                //     self.expression_to_snapshot(lowerer, &predicate.place, expect_math_bool)?
                // } else {
                //     // FIXME: cleanup code
                //     if lowerer.use_heap_variable()? {
                //         let deref = predicate.place.clone().unwrap_deref();
                //         let base_snapshot =
                //             self.expression_to_snapshot(lowerer, &deref.base, expect_math_bool)?;

                //         lowerer.pointer_target_snapshot_in_heap(
                //             deref.base.get_type(),
                //             self.heap.clone().unwrap(),
                //             base_snapshot,
                //             deref.position,
                //         )?
                //     } else {
                //         true.into()
                //     }
                // };

                // if lowerer.use_heap_variable()? {
                //     // let snapshot =  self.expression_to_snapshot(lowerer, &predicate.place, expect_math_bool)?;
                //     lowerer.owned_non_aliased(
                //         CallContext::BuiltinMethod,
                //         ty,
                //         ty,
                //         place,
                //         root_address,
                //         snapshot,
                //         None,
                //     )?
                // } else {
                //     lowerer.owned_non_aliased(
                //         CallContext::BuiltinMethod,
                //         ty,
                //         ty,
                //         place,
                //         root_address,
                //         snapshot,
                //         None,
                //     )?
                // }
            }
            vir_mid::Predicate::MemoryBlockHeap(predicate) => {
                let place = lowerer.encode_expression_as_place(&predicate.address)?;
                let root_address = self.pointer_deref_into_address(lowerer, &predicate.address)?;
                use vir_low::macros::*;
                let compute_address = ty!(Address);
                let address = expr! {
                    ComputeAddress::compute_address([place], [root_address])
                };
                let size =
                    self.expression_to_snapshot(lowerer, &predicate.size, expect_math_bool)?;
                lowerer.encode_memory_block_acc(address, size, acc_predicate.position)?
            }
            vir_mid::Predicate::MemoryBlockHeapDrop(predicate) => {
                // FIXME: Why this does not match the encoding of MemoryBlockHeap?
                let address = self.pointer_deref_into_address(lowerer, &predicate.address)?;
                let size =
                    self.expression_to_snapshot(lowerer, &predicate.size, expect_math_bool)?;
                lowerer.encode_memory_block_heap_drop_acc(address, size, acc_predicate.position)?
            }
            _ => unimplemented!("{acc_predicate}"),
        };
        Ok(expression)
    }

    fn acc_predicate_to_snapshot_postcondition<'p, 'v, 'tcx>(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        acc_predicate: &vir_mid::AccPredicate,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        assert!(expect_math_bool);
        let expression = match &*acc_predicate.predicate {
            vir_mid::Predicate::OwnedNonAliased(predicate) => {
                let position = predicate.position;
                let ty = predicate.place.get_type();
                let place = lowerer.encode_expression_as_place(&predicate.place)?;
                let old_value = self.replace_self_with_result_value;
                self.replace_self_with_result_value = true;
                let root_address_self =
                    self.pointer_deref_into_address(lowerer, &predicate.place)?;
                self.replace_self_with_result_value = old_value;
                let snap_call_self = lowerer.owned_non_aliased_snap(
                    CallContext::BuiltinMethod,
                    ty,
                    ty,
                    place.clone(),
                    root_address_self,
                    position,
                )?;
                if self.in_function {
                    let snap_call_result_value =
                        self.expression_to_snapshot(lowerer, &predicate.place, expect_math_bool)?;
                    vir_low::Expression::equals(snap_call_result_value, snap_call_self)
                } else {
                    let root_address_parameter =
                        self.pointer_deref_into_address(lowerer, &predicate.place)?;
                    let snap_call_parameter = lowerer.owned_non_aliased_snap(
                        CallContext::BuiltinMethod,
                        ty,
                        ty,
                        place,
                        root_address_parameter,
                        position,
                    )?;
                    vir_low::Expression::equals(
                        snap_call_parameter,
                        vir_low::Expression::labelled_old(None, snap_call_self, position),
                    )
                }
            }
            vir_mid::Predicate::MemoryBlockHeap(_) | vir_mid::Predicate::MemoryBlockHeapDrop(_) => {
                true.into()
            }
            _ => unimplemented!("{acc_predicate}"),
        };
        Ok(expression)
    }
}

// impl<'a> PlaceExpressionDomainEncoder for AssertionEncoder<'a> {
//     fn domain_name(&mut self, lowerer: &mut Lowerer) -> &str {
//         lowerer.address_domain()
//     }

//     fn encode_local(
//         &mut self,
//         local: &vir_mid::expression::Local,
//         lowerer: &mut Lowerer,
//     ) -> SpannedEncodingResult<vir_low::Expression> {
//         lowerer.root_address(local, &None)
//     }

//     fn encode_deref(
//         &mut self,
//         deref: &vir_mid::expression::Deref,
//         lowerer: &mut Lowerer,
//         _arg: vir_low::Expression,
//     ) -> SpannedEncodingResult<vir_low::Expression> {
//         let base_snapshot = self.expression_to_snapshot(lowerer, &deref.base, true)?;
//         let ty = deref.base.get_type();
//         let result = if ty.is_reference() {
//             lowerer.reference_address(ty, base_snapshot, deref.position)?
//         } else {
//             lowerer.pointer_address(ty, base_snapshot, deref.position)?
//         };
//         Ok(result)
//     }

//     fn encode_labelled_old(
//         &mut self,
//         _expression: &vir_mid::expression::LabelledOld,
//         _lowerer: &mut Lowerer,
//     ) -> SpannedEncodingResult<vir_low::Expression> {
//         todo!()
//     }

//     fn encode_array_index_axioms(
//         &mut self,
//         _base_type: &vir_mid::Type,
//         _lowerer: &mut Lowerer,
//     ) -> SpannedEncodingResult<()> {
//         todo!()
//     }
// }

impl<'a, 'p, 'v: 'p, 'tcx: 'v> IntoSnapshotLowerer<'p, 'v, 'tcx> for AssertionEncoder<'a> {
    fn variable_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        variable: &vir_mid::VariableDecl,
    ) -> SpannedEncodingResult<vir_low::VariableDecl> {
        if self.replace_self_with_result_value || self.in_function {
            assert!(variable.is_self_variable());
            Ok(self.result_value.clone().unwrap())
        } else {
            Ok(vir_low::VariableDecl {
                name: variable.name.clone(),
                ty: self.type_to_snapshot(lowerer, &variable.ty)?,
            })
        }
    }

    fn labelled_old_to_snapshot(
        &mut self,
        _lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        _old: &vir_mid::LabelledOld,
        _expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        todo!()
    }

    fn func_app_to_snapshot(
        &mut self,
        _lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        _app: &vir_mid::FuncApp,
        _expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        todo!()
    }

    fn acc_predicate_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        acc_predicate: &vir_mid::AccPredicate,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let expression = if self.result_value.is_some() {
            self.acc_predicate_to_snapshot_postcondition(lowerer, acc_predicate, expect_math_bool)?
        } else {
            self.acc_predicate_to_snapshot_precondition(lowerer, acc_predicate, expect_math_bool)?
        };
        Ok(expression)
    }

    fn field_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        field: &vir_mid::Field,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        match &*field.base {
            vir_mid::Expression::Local(local)
                if !self.replace_self_with_result_value && !self.in_function =>
            {
                assert!(local.variable.is_self_variable());
                Ok(self.field_arguments[&field.field.name].clone())
                // if self.replace_self_with_result_value {
                //     Ok(self.result_value.clone().unwrap().into())
                // } else
                // {Ok(self.field_arguments[&field.field.name].clone())}
            }
            _ => {
                // FIXME: Code duplication because Rust does not have syntax for calling
                // overriden methods.
                let base_snapshot =
                    self.expression_to_snapshot(lowerer, &field.base, expect_math_bool)?;
                let result = if field.field.is_discriminant() {
                    let ty = field.base.get_type();
                    // FIXME: Create a method for obtainging the discriminant type.
                    let type_decl = lowerer.encoder.get_type_decl_mid(ty)?;
                    let enum_decl = type_decl.unwrap_enum();
                    let discriminant_call =
                        lowerer.obtain_enum_discriminant(base_snapshot, ty, field.position)?;
                    lowerer.construct_constant_snapshot(
                        &enum_decl.discriminant_type,
                        discriminant_call,
                        field.position,
                    )?
                } else {
                    lowerer.obtain_struct_field_snapshot(
                        field.base.get_type(),
                        &field.field,
                        base_snapshot,
                        field.position,
                    )?
                };
                self.ensure_bool_expression(lowerer, field.get_type(), result, expect_math_bool)
            }
        }
    }

    fn deref_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        deref: &vir_mid::Deref,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let base_snapshot = self.expression_to_snapshot(lowerer, &deref.base, expect_math_bool)?;
        let ty = deref.base.get_type();
        let result = if ty.is_reference() {
            lowerer.reference_target_current_snapshot(ty, base_snapshot, Default::default())?
        } else if lowerer.use_heap_variable()? {
            lowerer.pointer_target_snapshot_in_heap(
                deref.base.get_type(),
                self.heap.clone().unwrap(),
                base_snapshot,
                deref.position,
            )?
        } else {
            // eprintln!("deref: {}", deref);
            // unimplemented!()
            true.into() // TODO
        };
        self.ensure_bool_expression(lowerer, deref.get_type(), result, expect_math_bool)
    }

    fn owned_non_aliased_snap(
        &mut self,
        _lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        _ty: &vir_mid::Type,
        _pointer_snapshot: &vir_mid::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        unimplemented!()
    }

    fn call_context(&self) -> CallContext {
        CallContext::BuiltinMethod
    }

    fn push_bound_variables(
        &mut self,
        _variables: &[vir_mid::VariableDecl],
    ) -> SpannedEncodingResult<()> {
        todo!()
    }

    fn pop_bound_variables(&mut self) -> SpannedEncodingResult<()> {
        todo!()
    }

    // fn unfolding_to_snapshot(
    //     &mut self,
    //     _lowerer: &mut Lowerer<'p, 'v, 'tcx>,
    //     _unfolding: &vir_mid::Unfolding,
    //     _expect_math_bool: bool,
    // ) -> SpannedEncodingResult<vir_low::Expression> {
    //     todo!()
    // }
}
