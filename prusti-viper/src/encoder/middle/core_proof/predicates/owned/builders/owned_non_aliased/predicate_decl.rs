use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        addresses::AddressesInterface,
        builtin_methods::CallContext,
        lowerer::Lowerer,
        places::PlacesInterface,
        predicates::{
            owned::builders::{
                common::predicate_decl::{ContainingPredicateKind, PredicateDeclBuilder},
                PredicateDeclBuilderMethods,
            },
            PredicatesMemoryBlockInterface, PredicatesOwnedInterface,
        },
        snapshots::{
            IntoPureSnapshot, IntoSnapshot, IntoSnapshotLowerer, PredicateKind,
            SnapshotValidityInterface, SnapshotValuesInterface,
        },
        type_layouts::TypeLayoutsInterface,
    },
};
use prusti_common::config;
use vir_crate::{
    common::{
        expression::{GuardedExpressionIterator, QuantifierHelpers},
        position::Positioned,
    },
    low::{self as vir_low},
    middle::{self as vir_mid},
};

pub(in super::super::super) struct OwnedNonAliasedBuilder<'l, 'p, 'v, 'tcx> {
    inner: PredicateDeclBuilder<'l, 'p, 'v, 'tcx>,
    snapshot: vir_low::VariableDecl,
    slice_len: Option<vir_mid::VariableDecl>,
}

impl<'l, 'p, 'v, 'tcx> PredicateDeclBuilderMethods<'l, 'p, 'v, 'tcx>
    for OwnedNonAliasedBuilder<'l, 'p, 'v, 'tcx>
{
    fn inner(&mut self) -> &mut PredicateDeclBuilder<'l, 'p, 'v, 'tcx> {
        &mut self.inner
    }
}

impl<'l, 'p, 'v, 'tcx> OwnedNonAliasedBuilder<'l, 'p, 'v, 'tcx> {
    pub(in super::super::super) fn new(
        lowerer: &'l mut Lowerer<'p, 'v, 'tcx>,
        ty: &'l vir_mid::Type,
        type_decl: &'l vir_mid::TypeDecl,
    ) -> SpannedEncodingResult<Self> {
        let slice_len = if ty.is_slice() {
            Some(vir_mid::VariableDecl::new(
                "slice_len",
                lowerer.size_type_mid()?,
            ))
        } else {
            None
        };
        let position = type_decl.position();
        Ok(Self {
            snapshot: vir_low::VariableDecl::new("snapshot", ty.to_snapshot(lowerer)?),
            slice_len,
            inner: PredicateDeclBuilder::new(lowerer, "OwnedNonAliased", ty, type_decl, position)?,
        })
    }

    pub(in super::super::super) fn build(self) -> vir_low::PredicateDecl {
        self.inner.build()
    }

    pub(in super::super::super) fn create_parameters(&mut self) -> SpannedEncodingResult<()> {
        self.inner.parameters.push(self.inner.place.clone());
        self.inner.parameters.push(self.inner.address.clone());
        if config::use_snapshot_parameters_in_predicates() {
            self.inner.parameters.push(self.snapshot.clone());
        }
        self.inner.create_lifetime_parameters()?;
        if let Some(slice_len_mid) = &self.slice_len {
            let slice_len = slice_len_mid.to_pure_snapshot(self.inner.lowerer)?;
            self.inner.parameters.push(slice_len);
        }
        self.inner.create_const_parameters()?;
        Ok(())
    }

    pub(in super::super::super) fn add_validity(&mut self) -> SpannedEncodingResult<()> {
        self.inner.add_validity(&self.snapshot)
    }

    // fn compute_address(&self) -> SpannedEncodingResult<vir_low::Expression> {
    //     use vir_low::macros::*;
    //     let compute_address = ty!(Address);
    //     let expression = expr! {
    //         ComputeAddress::compute_address(
    //             [self.inner.place.clone().into()],
    //             [self.inner.address.clone().into()]
    //         )
    //     };
    //     Ok(expression)
    // }

    fn size_of(&mut self) -> SpannedEncodingResult<vir_low::Expression> {
        self.inner
            .lowerer
            .encode_type_size_expression2(self.inner.ty, self.inner.type_decl)
    }

    fn padding_size(&mut self) -> SpannedEncodingResult<vir_low::Expression> {
        self.inner
            .lowerer
            .encode_type_padding_size_expression(self.inner.ty)
    }

    pub(in super::super::super) fn add_base_memory_block(&mut self) -> SpannedEncodingResult<()> {
        use vir_low::macros::*;
        // let compute_address = self.compute_address()?;
        let size_of = self.size_of()?;
        let address = &self.inner.address;
        let expression = expr! {
            acc(MemoryBlock(address, [size_of]))
        };
        self.inner.add_conjunct(expression)
    }

    pub(in super::super::super) fn add_padding_memory_block(
        &mut self,
    ) -> SpannedEncodingResult<()> {
        use vir_low::macros::*;
        // let compute_address = self.compute_address()?;
        let padding_size = self.padding_size()?;
        let address = &self.inner.address;
        let expression = expr! {
            // acc(MemoryBlock([compute_address], [padding_size]))
            acc(MemoryBlock(address, [padding_size]))
        };
        self.inner.add_conjunct(expression)
    }

    fn add_bytes_snapshot_equality_with(
        &mut self,
        snap_ty: &vir_mid::Type,
        snapshot: vir_low::Expression,
    ) -> SpannedEncodingResult<()> {
        use vir_low::macros::*;
        let size_of = self.size_of()?;
        let bytes = self
            .inner
            .lowerer
            // .encode_memory_block_bytes_expression(self.compute_address()?, size_of)?;
            .encode_memory_block_bytes_expression(self.inner.address.clone().into(), size_of)?;
        let to_bytes = ty! { Bytes };
        let expression = expr! {
            [bytes] == (Snap<snap_ty>::to_bytes([snapshot]))
        };
        self.inner.add_conjunct(expression)
    }

    pub(in super::super::super) fn add_bytes_snapshot_equality(
        &mut self,
    ) -> SpannedEncodingResult<()> {
        self.add_bytes_snapshot_equality_with(self.inner.ty, self.snapshot.clone().into())
    }

    // pub(in super::super::super) fn add_bytes_address_snapshot_equality(
    //     &mut self,
    // ) -> SpannedEncodingResult<()> {
    //     let address_type = self.inner.lowerer.reference_address_type(self.inner.ty)?;
    //     self.inner
    //         .lowerer
    //         .encode_snapshot_to_bytes_function(&address_type)?;
    //     let target_address_snapshot = self.inner.lowerer.reference_address_snapshot(
    //         self.inner.ty,
    //         self.snapshot.clone().into(),
    //         self.inner.position,
    //     )?;
    //     self.add_bytes_snapshot_equality_with(&address_type, target_address_snapshot)
    // }

    pub(in super::super::super) fn add_field_predicate(
        &mut self,
        field: &vir_mid::FieldDecl,
    ) -> SpannedEncodingResult<()> {
        let field_place = self.inner.lowerer.encode_field_place(
            self.inner.ty,
            field,
            self.inner.place.clone().into(),
            self.inner.position,
        )?;
        let field_address = self.inner.lowerer.encode_field_address(
            self.inner.ty,
            field,
            self.inner.address.clone().into(),
            self.inner.position,
        )?;
        // let field_snapshot = self.inner.lowerer.obtain_struct_field_snapshot(
        //     self.inner.ty,
        //     field,
        //     self.snapshot.clone().into(),
        //     Default::default(),
        // )?;
        let expression = self.inner.lowerer.owned_non_aliased(
            CallContext::BuiltinMethod,
            &field.ty,
            &field.ty,
            field_place,
            field_address,
            None,
            self.inner.position,
        )?;
        self.inner.add_conjunct(expression)
    }

    pub(in super::super::super) fn add_discriminant_predicate(
        &mut self,
        decl: &vir_mid::type_decl::Enum,
    ) -> SpannedEncodingResult<()> {
        let discriminant_field = decl.discriminant_field();
        let discriminant_place = self.inner.lowerer.encode_field_place(
            self.inner.ty,
            &discriminant_field,
            self.inner.place.clone().into(),
            self.inner.position,
        )?;
        let discriminant_address = self.inner.lowerer.encode_field_address(
            self.inner.ty,
            &discriminant_field,
            self.inner.address.clone().into(),
            self.inner.position,
        )?;
        let _discriminant_call = self.inner.lowerer.obtain_enum_discriminant(
            self.snapshot.clone().into(),
            self.inner.ty,
            self.inner.position,
        )?;
        // let discriminant_snapshot = self.inner.lowerer.construct_constant_snapshot(
        //     &decl.discriminant_type,
        //     discriminant_call,
        //     self.inner.position,
        // )?;
        let expression = self.inner.lowerer.owned_non_aliased(
            CallContext::BuiltinMethod,
            &decl.discriminant_type,
            &decl.discriminant_type,
            discriminant_place,
            discriminant_address,
            None,
            self.inner.position,
        )?;
        self.inner.add_conjunct(expression)
    }

    pub(in super::super::super) fn add_unique_ref_target_predicate(
        &mut self,
        target_type: &vir_mid::Type,
        lifetime: &vir_mid::ty::LifetimeConst,
    ) -> SpannedEncodingResult<()> {
        let place = self.inner.place.clone();
        let address = self.inner.address.clone();
        self.inner.add_unique_ref_target_predicate(
            target_type,
            lifetime,
            place.into(),
            address,
            ContainingPredicateKind::Owned,
        )
    }

    pub(in super::super::super) fn add_frac_ref_target_predicate(
        &mut self,
        target_type: &vir_mid::Type,
        lifetime: &vir_mid::ty::LifetimeConst,
    ) -> SpannedEncodingResult<()> {
        let place = self.inner.place.clone();
        let address = self.inner.address.clone();
        self.inner.add_frac_ref_target_predicate(
            target_type,
            lifetime,
            place.into(),
            address,
            ContainingPredicateKind::Owned,
        )
    }

    // FIXME: Code duplication.
    pub(in super::super::super) fn get_slice_len(
        &self,
    ) -> SpannedEncodingResult<vir_mid::VariableDecl> {
        Ok(self.slice_len.as_ref().unwrap().clone())
    }

    pub(in super::super::super) fn add_snapshot_len_equal_to(
        &mut self,
        array_length_mid: &vir_mid::VariableDecl,
    ) -> SpannedEncodingResult<()> {
        self.inner
            .add_snapshot_len_equal_to(&self.snapshot, array_length_mid)
    }

    pub(in super::super::super) fn add_quantified_permission(
        &mut self,
        array_length_mid: &vir_mid::VariableDecl,
        element_type: &vir_mid::Type,
    ) -> SpannedEncodingResult<()> {
        use vir_low::macros::*;
        let size_type = self.inner.lowerer.size_type()?;
        let size_type_mid = self.inner.lowerer.size_type_mid()?;
        var_decls! {
            index: {size_type}
        };
        let index_validity = self
            .inner
            .lowerer
            .encode_snapshot_valid_call_for_type(index.clone().into(), &size_type_mid)?;
        let index_int = self.inner.lowerer.obtain_constant_value(
            &size_type_mid,
            index.clone().into(),
            self.inner.position,
        )?;
        let array_length_int = self.inner.array_length_int(array_length_mid)?;
        let element_place = self.inner.lowerer.encode_index_place(
            self.inner.ty,
            self.inner.place.clone().into(),
            index.clone().into(),
            self.inner.position,
        )?;
        let element_address = self.inner.lowerer.encode_index_address(
            self.inner.ty,
            self.inner.address.clone().into(),
            index.clone().into(),
            self.inner.position,
        )?;
        // let element_snapshot = self.inner.lowerer.obtain_array_element_snapshot(
        //     self.snapshot.clone().into(),
        //     index_int.clone(),
        //     self.inner.position,
        // )?;
        let element_predicate_acc = self.inner.lowerer.owned_non_aliased(
            CallContext::BuiltinMethod,
            element_type,
            element_type,
            element_place,
            element_address,
            None,
            self.inner.position,
        )?;
        let elements = vir_low::Expression::forall(
            vec![index],
            vec![vir_low::Trigger::new(vec![element_predicate_acc.clone()])],
            expr! {
                ([index_validity] && ([index_int] < [array_length_int])) ==>
                [element_predicate_acc]
            },
        );
        self.inner.add_conjunct(elements)
    }

    pub(in super::super::super) fn create_variant_predicate(
        &mut self,
        decl: &vir_mid::type_decl::Enum,
        discriminant_value: vir_mid::DiscriminantValue,
        variant: &vir_mid::type_decl::Struct,
        variant_type: &vir_mid::Type,
    ) -> SpannedEncodingResult<(vir_low::Expression, vir_low::Expression)> {
        use vir_low::macros::*;
        let discriminant_call = if config::use_snapshot_parameters_in_predicates() {
            self.inner.lowerer.obtain_enum_discriminant(
                self.snapshot.clone().into(),
                self.inner.ty,
                self.inner.position,
            )?
        } else {
            // FIXME: Code duplication with other create_variant_predicate methods.
            let discriminant_field = decl.discriminant_field();
            let discriminant_place = self.inner.lowerer.encode_field_place(
                self.inner.ty,
                &discriminant_field,
                self.inner.place.clone().into(),
                self.inner.position,
            )?;
            let discriminant_address = self.inner.lowerer.encode_field_address(
                self.inner.ty,
                &discriminant_field,
                self.inner.address.clone().into(),
                self.inner.position,
            )?;
            let discriminant_snapshot = self.inner.lowerer.owned_non_aliased_snap(
                CallContext::BuiltinMethod,
                &decl.discriminant_type,
                &decl.discriminant_type,
                discriminant_place,
                discriminant_address,
                self.inner.position,
            )?;
            self.inner.lowerer.obtain_constant_value(
                &decl.discriminant_type,
                discriminant_snapshot,
                self.inner.position,
            )?
        };
        let guard = expr! {
            [ discriminant_call ] == [ discriminant_value.into() ]
        };
        let variant_index = variant.name.clone().into();
        let variant_place = self.inner.lowerer.encode_enum_variant_place(
            self.inner.ty,
            &variant_index,
            self.inner.place.clone().into(),
            self.inner.position,
        )?;
        let variant_address = self.inner.lowerer.encode_enum_variant_address(
            self.inner.ty,
            &variant_index,
            self.inner.address.clone().into(),
            self.inner.position,
        )?;
        // let variant_snapshot = self.inner.lowerer.obtain_enum_variant_snapshot(
        //     self.inner.ty,
        //     &variant_index,
        //     self.snapshot.clone().into(),
        //     self.inner.position,
        // )?;
        let predicate = self.inner.lowerer.owned_non_aliased(
            CallContext::BuiltinMethod,
            variant_type,
            variant_type,
            variant_place,
            variant_address,
            None,
            self.inner.position,
        )?;
        Ok((guard, predicate))
    }

    pub(in super::super::super) fn add_variant_predicates(
        &mut self,
        variant_predicates: Vec<(vir_low::Expression, vir_low::Expression)>,
    ) -> SpannedEncodingResult<()> {
        self.inner
            .add_conjunct(variant_predicates.into_iter().create_match())
    }

    pub(in super::super::super) fn add_structural_invariant(
        &mut self,
        decl: &vir_mid::type_decl::Struct,
    ) -> SpannedEncodingResult<Vec<vir_mid::Type>> {
        self.inner
            .add_structural_invariant(decl, PredicateKind::Owned)
    }

    // pub(in super::super::super) fn add_structural_invariant(
    //     &mut self,
    //     decl: &vir_mid::type_decl::Struct,
    // ) -> SpannedEncodingResult<()> {
    //     if let Some(invariant) = &decl.structural_invariant {
    //         let mut encoder = SelfFramingAssertionToSnapshot::for_predicate_body(
    //             self.inner.place.clone(),
    //             self.inner.address.clone(),
    //             PredicateKind::Owned,
    //         );
    //         // let mut encoder = PredicateAssertionEncoder {
    //         //     place: &self.inner.place,
    //         //     address: &self.inner.address,
    //         //     snap_calls: Default::default(),
    //         // };
    //         for assertion in invariant {
    //             let low_assertion =
    //                 encoder.expression_to_snapshot(self.inner.lowerer, assertion, true)?;
    //             self.inner.add_conjunct(low_assertion)?;
    //         }
    //     }
    //     Ok(())
    // }
}

// // FIXME: Move this to its own module.
// FIXME: This should be replaced by prusti-viper/src/encoder/middle/core_proof/snapshots/into_snapshot/assertions/self_framing.rs
// struct PredicateAssertionEncoder<'a> {
//     place: &'a vir_low::VariableDecl,
//     address: &'a vir_low::VariableDecl,
//     /// Mapping from place to snapshot. We use a vector because we need to know
//     /// the insertion order.
//     snap_calls: Vec<(vir_mid::Expression, vir_low::Expression)>,
// }

// impl<'a> PredicateAssertionEncoder<'a> {
//     // FIXME: Code duplication.
//     fn pointer_deref_into_address<'p, 'v, 'tcx>(
//         &mut self,
//         lowerer: &mut Lowerer<'p, 'v, 'tcx>,
//         place: &vir_mid::Expression,
//     ) -> SpannedEncodingResult<vir_low::Expression> {
//         if let Some(deref_place) = place.get_last_dereferenced_pointer() {
//             let base_snapshot = self.expression_to_snapshot(lowerer, deref_place, true)?;
//             let ty = deref_place.get_type();
//             lowerer.pointer_address(ty, base_snapshot, place.position())
//         } else {
//             unreachable!()
//         }
//         // match place {
//         //     vir_mid::Expression::Deref(deref) => {
//         //         let base_snapshot = self.expression_to_snapshot(lowerer, &deref.base, true)?;
//         //         let ty = deref.base.get_type();
//         //         assert!(ty.is_pointer());
//         //         lowerer.pointer_address(ty, base_snapshot, place.position())
//         //     }
//         //     _ => unreachable!(),
//         // }
//     }
// }

// impl<'a, 'p, 'v: 'p, 'tcx: 'v> IntoSnapshotLowerer<'p, 'v, 'tcx> for PredicateAssertionEncoder<'a> {
//     fn expression_to_snapshot(
//         &mut self,
//         lowerer: &mut Lowerer<'p, 'v, 'tcx>,
//         expression: &vir_mid::Expression,
//         expect_math_bool: bool,
//     ) -> SpannedEncodingResult<vir_low::Expression> {
//         for (place, call) in &self.snap_calls {
//             if place == expression {
//                 return Ok(call.clone());
//             }
//         }
//         self.expression_to_snapshot_impl(lowerer, expression, expect_math_bool)
//     }

//     fn variable_to_snapshot(
//         &mut self,
//         lowerer: &mut Lowerer<'p, 'v, 'tcx>,
//         variable: &vir_mid::VariableDecl,
//     ) -> SpannedEncodingResult<vir_low::VariableDecl> {
//         assert!(variable.is_self_variable(), "{} must be self", variable);
//         Ok(vir_low::VariableDecl {
//             name: variable.name.clone(),
//             ty: self.type_to_snapshot(lowerer, &variable.ty)?,
//         })
//     }

//     fn labelled_old_to_snapshot(
//         &mut self,
//         _lowerer: &mut Lowerer<'p, 'v, 'tcx>,
//         _old: &vir_mid::LabelledOld,
//         _expect_math_bool: bool,
//     ) -> SpannedEncodingResult<vir_low::Expression> {
//         unreachable!("Old expression are not allowed in predicates");
//     }

//     fn func_app_to_snapshot(
//         &mut self,
//         lowerer: &mut Lowerer<'p, 'v, 'tcx>,
//         app: &vir_mid::FuncApp,
//         expect_math_bool: bool,
//     ) -> SpannedEncodingResult<vir_low::Expression> {
//         todo!()
//     }

//     fn binary_op_to_snapshot(
//         &mut self,
//         lowerer: &mut Lowerer<'p, 'v, 'tcx>,
//         op: &vir_mid::BinaryOp,
//         expect_math_bool: bool,
//     ) -> SpannedEncodingResult<vir_low::Expression> {
//         // TODO: Create impl versions of each method so that I can override
//         // without copying.
//         let mut introduced_snap = false;
//         if op.op_kind == vir_mid::BinaryOpKind::And {
//             if let box vir_mid::Expression::AccPredicate(expression) = &op.left {
//                 if expression.predicate.is_owned_non_aliased() {
//                     introduced_snap = true;
//                 }
//             }
//         }
//         let expression = self.binary_op_to_snapshot_impl(lowerer, op, expect_math_bool)?;
//         if introduced_snap {
//             // TODO: Use the snap calls from this vector instead of generating
//             // on demand. This must always succeed because we require
//             // expressions to be framed.
//             self.snap_calls.pop();
//         }
//         Ok(expression)
//     }

//     fn acc_predicate_to_snapshot(
//         &mut self,
//         lowerer: &mut Lowerer<'p, 'v, 'tcx>,
//         acc_predicate: &vir_mid::AccPredicate,
//         expect_math_bool: bool,
//     ) -> SpannedEncodingResult<vir_low::Expression> {
//         assert!(expect_math_bool);
//         let expression = match &*acc_predicate.predicate {
//             vir_mid::Predicate::OwnedNonAliased(predicate) => {
//                 let ty = predicate.place.get_type();
//                 let place = lowerer.encode_expression_as_place(&predicate.place)?;
//                 let address = self.pointer_deref_into_address(lowerer, &predicate.place)?;
//                 let snapshot = true.into();
//                 let acc = lowerer.owned_non_aliased(
//                     CallContext::Procedure,
//                     ty,
//                     ty,
//                     place.clone(),
//                     address.clone(),
//                     snapshot,
//                     None,
//                 )?;
//                 let snap_call = lowerer.owned_non_aliased_snap(
//                     CallContext::BuiltinMethod,
//                     ty,
//                     ty,
//                     place,
//                     address,
//                     predicate.place.position(),
//                 )?;
//                 self.snap_calls.push((predicate.place.clone(), snap_call));
//                 acc
//             }
//             vir_mid::Predicate::MemoryBlockHeap(predicate) => {
//                 let place = lowerer.encode_expression_as_place(&predicate.address)?;
//                 let address = self.pointer_deref_into_address(lowerer, &predicate.address)?;
//                 use vir_low::macros::*;
//                 let compute_address = ty!(Address);
//                 let address = expr! {
//                     ComputeAddress::compute_address([place], [address])
//                 };
//                 let size =
//                     self.expression_to_snapshot(lowerer, &predicate.size, expect_math_bool)?;
//                 lowerer.encode_memory_block_acc(address, size, acc_predicate.position)?
//             }
//             vir_mid::Predicate::MemoryBlockHeapDrop(predicate) => {
//                 let place = self.pointer_deref_into_address(lowerer, &predicate.address)?;
//                 let size =
//                     self.expression_to_snapshot(lowerer, &predicate.size, expect_math_bool)?;
//                 lowerer.encode_memory_block_heap_drop_acc(place, size, acc_predicate.position)?
//             }
//             _ => unimplemented!("{acc_predicate}"),
//         };
//         Ok(expression)
//     }

//     fn field_to_snapshot(
//         &mut self,
//         lowerer: &mut Lowerer<'p, 'v, 'tcx>,
//         field: &vir_mid::Field,
//         expect_math_bool: bool,
//     ) -> SpannedEncodingResult<vir_low::Expression> {
//         match &*field.base {
//             vir_mid::Expression::Local(local) => {
//                 assert!(local.variable.is_self_variable());
//                 let field_place = lowerer.encode_field_place(
//                     &local.variable.ty,
//                     &field.field,
//                     self.inner.place.clone().into(),
//                     field.position,
//                 )?;
//                 lowerer.owned_non_aliased_snap(
//                     CallContext::BuiltinMethod,
//                     &field.field.ty,
//                     &field.field.ty,
//                     field_place,
//                     self.inner.address.clone().into(),
//                     local.position,
//                 )
//             }
//             _ => {
//                 // FIXME: Code duplication because Rust does not have syntax for calling
//                 // overriden methods.
//                 let base_snapshot =
//                     self.expression_to_snapshot(lowerer, &field.base, expect_math_bool)?;
//                 let result = if field.field.is_discriminant() {
//                     let ty = field.base.get_type();
//                     // FIXME: Create a method for obtainging the discriminant type.
//                     let type_decl = lowerer.encoder.get_type_decl_mid(ty)?;
//                     let enum_decl = type_decl.unwrap_enum();
//                     let discriminant_call =
//                         lowerer.obtain_enum_discriminant(base_snapshot, ty, field.position)?;
//                     lowerer.construct_constant_snapshot(
//                         &enum_decl.discriminant_type,
//                         discriminant_call,
//                         field.position,
//                     )?
//                 } else {
//                     lowerer.obtain_struct_field_snapshot(
//                         field.base.get_type(),
//                         &field.field,
//                         base_snapshot,
//                         field.position,
//                     )?
//                 };
//                 self.ensure_bool_expression(lowerer, field.get_type(), result, expect_math_bool)
//             }
//         }
//     }

//     // FIXME: Code duplication.
//     fn deref_to_snapshot(
//         &mut self,
//         lowerer: &mut Lowerer<'p, 'v, 'tcx>,
//         deref: &vir_mid::Deref,
//         expect_math_bool: bool,
//     ) -> SpannedEncodingResult<vir_low::Expression> {
//         let base_snapshot = self.expression_to_snapshot(lowerer, &deref.base, expect_math_bool)?;
//         let ty = deref.base.get_type();
//         let result = if ty.is_reference() {
//             lowerer.reference_target_current_snapshot(ty, base_snapshot, Default::default())?
//         } else {
//             let aliased_root_place = lowerer.encode_aliased_place_root(deref.position)?;
//             let address = lowerer.pointer_address(ty, base_snapshot, deref.position)?;
//             lowerer.owned_non_aliased_snap(
//                 CallContext::BuiltinMethod,
//                 &deref.ty,
//                 &deref.ty,
//                 aliased_root_place,
//                 address,
//                 deref.position,
//             )?
//             // snap_owned_non_aliased$I32(aliased_place_root(), destructor$Snap$ptr$I32$$address(snap_owned_non_aliased$ptr$I32(field_place$$struct$m_T5$$$f$p2(place), address)))

//             // FIXME: This should be unreachable. Most likely, in predicates we should use snap
//             // functions.
//             // let heap = vir_low::VariableDecl::new("predicate_heap$", lowerer.heap_type()?);
//             // lowerer.pointer_target_snapshot_in_heap(
//             //     deref.base.get_type(),
//             //     heap,
//             //     base_snapshot,
//             //     deref.position,
//             // )?
//         };
//         self.ensure_bool_expression(lowerer, deref.get_type(), result, expect_math_bool)
//     }

//     fn owned_non_aliased_snap(
//         &mut self,
//         lowerer: &mut Lowerer<'p, 'v, 'tcx>,
//         ty: &vir_mid::Type,
//         pointer_snapshot: &vir_mid::Expression,
//     ) -> SpannedEncodingResult<vir_low::Expression> {
//         unimplemented!()
//     }

//     fn call_context(&self) -> CallContext {
//         CallContext::BuiltinMethod
//     }

//     // fn unfolding_to_snapshot(
//     //     &mut self,
//     //     lowerer: &mut Lowerer<'p, 'v, 'tcx>,
//     //     unfolding: &vir_mid::Unfolding,
//     //     expect_math_bool: bool,
//     // ) -> SpannedEncodingResult<vir_low::Expression> {
//     //     todo!()
//     // }
// }
