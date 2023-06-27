// use crate::encoder::{
//     errors::SpannedEncodingResult,
//     middle::core_proof::{
//         addresses::AddressesInterface,
//         builtin_methods::CallContext,
//         lifetimes::LifetimesInterface,
//         lowerer::Lowerer,
//         places::PlacesInterface,
//         predicates::{
//             owned::builders::common::function_decl::FunctionDeclBuilder,
//             PredicatesMemoryBlockInterface, PredicatesOwnedInterface,
//         },
//         references::ReferencesInterface,
//         snapshots::{
//             IntoPureSnapshot, PredicateKind, SnapshotBytesInterface, SnapshotValidityInterface,
//             SnapshotValuesInterface,
//         },
//         type_layouts::TypeLayoutsInterface,
//     },
// };

// use vir_crate::{
//     common::{expression::QuantifierHelpers, position::Positioned},
//     low::{self as vir_low},
//     middle::{self as vir_mid},
// };

// pub(in super::super::super) struct OwnedAliasedSnapFunctionBuilder<'l, 'p, 'v, 'tcx> {
//     inner: FunctionDeclBuilder<'l, 'p, 'v, 'tcx>,
//     // address: vir_low::VariableDecl,
//     slice_len: Option<vir_mid::VariableDecl>,
// }

// impl<'l, 'p, 'v, 'tcx> OwnedAliasedSnapFunctionBuilder<'l, 'p, 'v, 'tcx> {
//     pub(in super::super::super) fn new(
//         _lowerer: &'l mut Lowerer<'p, 'v, 'tcx>,
//         _ty: &'l vir_mid::Type,
//         _type_decl: &'l vir_mid::TypeDecl,
//     ) -> SpannedEncodingResult<Self> {
//         unimplemented!();
//         // let slice_len = if ty.is_slice() {
//         //     Some(vir_mid::VariableDecl::new(
//         //         "slice_len",
//         //         lowerer.size_type_mid()?,
//         //     ))
//         // } else {
//         //     None
//         // };
//         // Ok(Self {
//         //     // address: vir_low::VariableDecl::new("address", lowerer.address_type()?),
//         //     slice_len,
//         //     inner: FunctionDeclBuilder::new(
//         //         lowerer,
//         //         "snap_owned_aliased",
//         //         ty,
//         //         type_decl,
//         //         Default::default(),
//         //     )?,
//         // })
//     }

//     pub(in super::super::super) fn get_snapshot_postconditions(
//         &self,
//     ) -> SpannedEncodingResult<Vec<vir_low::Expression>> {
//         self.inner.get_snapshot_postconditions()
//     }

//     pub(in super::super::super) fn get_snapshot_body(
//         &self,
//     ) -> SpannedEncodingResult<Vec<vir_low::Expression>> {
//         self.inner.get_snapshot_body()
//     }

//     pub(in super::super::super) fn build(self) -> SpannedEncodingResult<vir_low::FunctionDecl> {
//         self.inner.build()
//     }

//     pub(in super::super::super) fn create_parameters(&mut self) -> SpannedEncodingResult<()> {
//         self.inner.parameters.push(self.inner.address.clone());
//         self.inner.create_lifetime_parameters()?;
//         if let Some(slice_len_mid) = &self.slice_len {
//             let slice_len = slice_len_mid.to_pure_snapshot(self.inner.lowerer)?;
//             self.inner.parameters.push(slice_len);
//         }
//         self.inner.create_const_parameters()?;
//         Ok(())
//     }

//     // FIXME: Code duplication.
//     pub(in super::super::super) fn get_slice_len(
//         &self,
//     ) -> SpannedEncodingResult<vir_mid::VariableDecl> {
//         Ok(self.slice_len.as_ref().unwrap().clone())
//     }

//     // fn owned_predicate<G>(
//     //     &mut self,
//     //     ty: &vir_mid::Type,
//     //     generics: &G,
//     //     address: vir_low::Expression,
//     // ) -> SpannedEncodingResult<vir_low::Expression>
//     // where
//     //     G: WithLifetimes + WithConstArguments,
//     // {
//     //     let mut builder = OwnedNonAliasedUseBuilder::new(
//     //         self.inner.lowerer,
//     //         CallContext::BuiltinMethod,
//     //         ty,
//     //         generics,
//     //         place,
//     //         root_address,
//     //     )?;
//     //     builder.add_lifetime_arguments()?;
//     //     builder.add_const_arguments()?;
//     //     builder.build()
//     // }

//     // FIXME: Code duplication with add_quantified_permission.
//     pub(in super::super::super) fn add_quantifiers(
//         &mut self,
//         array_length_mid: &vir_mid::VariableDecl,
//         element_type: &vir_mid::Type,
//     ) -> SpannedEncodingResult<()> {
//         use vir_low::macros::*;
//         let size_type_mid = self.inner.lowerer.size_type_mid()?;
//         var_decls! {
//             index_int: Int
//         };
//         let index = self.inner.lowerer.construct_constant_snapshot(
//             &size_type_mid,
//             index_int.clone().into(),
//             self.inner.position,
//         )?;
//         let index_validity = self
//             .inner
//             .lowerer
//             .encode_snapshot_valid_call_for_type(index.clone(), &size_type_mid)?;
//         let array_length_int = self.inner.array_length_int(array_length_mid)?;
//         let element_address = self.inner.lowerer.encode_index_address(
//             self.inner.ty,
//             self.inner.address.clone().into(),
//             index,
//             self.inner.position,
//         )?;
//         let element_predicate_acc = {
//             self.inner.lowerer.owned_aliased(
//                 CallContext::BuiltinMethod,
//                 element_type,
//                 element_type,
//                 element_address.clone(),
//                 None,
//                 self.inner.position,
//             )?
//         };
//         let result = self.inner.result()?.into();
//         let element_snapshot = self.inner.lowerer.obtain_array_element_snapshot(
//             result,
//             index_int.clone().into(),
//             self.inner.position,
//         )?;
//         let element_snap_call = self.inner.lowerer.owned_aliased_snap(
//             CallContext::BuiltinMethod,
//             element_type,
//             element_type,
//             element_address,
//             self.inner.position,
//         )?;
//         let elements = vir_low::Expression::forall(
//             vec![index_int.clone()],
//             vec![vir_low::Trigger::new(vec![element_predicate_acc])],
//             expr! {
//                 ([index_validity] && (index_int < [array_length_int])) ==>
//                 ([element_snapshot] == [element_snap_call])
//             },
//         );
//         self.add_snapshot_body_postcondition(elements)
//     }

//     pub(in super::super::super) fn add_snapshot_body_postcondition(
//         &mut self,
//         body: vir_low::Expression,
//     ) -> SpannedEncodingResult<()> {
//         // let predicate = self.precondition_predicate()?;
//         // let unfolding = predicate.into_unfolding(body);
//         // self.inner.add_postcondition(unfolding)
//         self.inner.add_snapshot_body_postcondition(body)
//     }

//     pub(in super::super::super) fn add_validity_postcondition(
//         &mut self,
//     ) -> SpannedEncodingResult<()> {
//         self.inner.add_validity_postcondition()
//     }

//     pub(in super::super::super) fn add_snapshot_len_equal_to_postcondition(
//         &mut self,
//         array_length_mid: &vir_mid::VariableDecl,
//     ) -> SpannedEncodingResult<()> {
//         self.inner
//             .add_snapshot_len_equal_to_postcondition(array_length_mid)
//     }

//     pub(in super::super::super) fn add_owned_precondition(&mut self) -> SpannedEncodingResult<()> {
//         let predicate = self.precondition_predicate()?;
//         self.inner.add_precondition(predicate)
//     }

//     fn precondition_predicate(&mut self) -> SpannedEncodingResult<vir_low::Expression> {
//         self.inner.lowerer.owned_aliased(
//             CallContext::BuiltinMethod,
//             self.inner.ty,
//             self.inner.type_decl,
//             self.inner.address.clone().into(),
//             Some(vir_low::Expression::wildcard_permission()),
//             self.inner.position,
//         )
//     }

//     // fn compute_address(&self) -> SpannedEncodingResult<vir_low::Expression> {
//     //     use vir_low::macros::*;
//     //     let compute_address = ty!(Address);
//     //     let expression = expr! {
//     //         ComputeAddress::compute_address(
//     //             [self.place.clone().into()],
//     //             [self.root_address.clone().into()]
//     //         )
//     //     };
//     //     Ok(expression)
//     // }

//     fn size_of(&mut self) -> SpannedEncodingResult<vir_low::Expression> {
//         self.inner
//             .lowerer
//             .encode_type_size_expression2(self.inner.ty, self.inner.type_decl)
//     }

//     // FIXME: Code duplication.
//     fn add_bytes_snapshot_equality_with(
//         &mut self,
//         snap_ty: &vir_mid::Type,
//         snapshot: vir_low::Expression,
//     ) -> SpannedEncodingResult<()> {
//         use vir_low::macros::*;
//         let size_of = self.size_of()?;
//         let bytes = self
//             .inner
//             .lowerer
//             .encode_memory_block_bytes_expression(self.inner.address.clone().into(), size_of)?;
//         let to_bytes = ty! { Bytes };
//         let expression = expr! {
//             [bytes] == (Snap<snap_ty>::to_bytes([snapshot]))
//         };
//         self.add_snapshot_body_postcondition(expression)
//     }

//     pub(in super::super::super) fn add_bytes_snapshot_equality(
//         &mut self,
//     ) -> SpannedEncodingResult<()> {
//         let result = self.inner.result()?.into();
//         self.add_bytes_snapshot_equality_with(self.inner.ty, result)
//     }

//     pub(in super::super::super) fn add_bytes_address_snapshot_equality(
//         &mut self,
//     ) -> SpannedEncodingResult<()> {
//         let result = self.inner.result()?.into();
//         let address_type = self.inner.lowerer.reference_address_type(self.inner.ty)?;
//         self.inner
//             .lowerer
//             .encode_snapshot_to_bytes_function(&address_type)?;
//         let target_address_snapshot = self.inner.lowerer.reference_address_snapshot(
//             self.inner.ty,
//             result,
//             self.inner.position,
//         )?;
//         self.add_bytes_snapshot_equality_with(&address_type, target_address_snapshot)
//     }

//     // // fn create_field_snap_call(
//     // //     &mut self,
//     // //     field: &vir_mid::FieldDecl,
//     // // ) -> SpannedEncodingResult<vir_low::Expression> {
//     // //     let field_place = self.inner.lowerer.encode_field_place(
//     // //         self.inner.ty,
//     // //         field,
//     // //         self.place.clone().into(),
//     // //         self.inner.position,
//     // //     )?;
//     // //     self.inner.lowerer.owned_non_aliased_snap(
//     // //         CallContext::BuiltinMethod,
//     // //         &field.ty,
//     // //         &field.ty,
//     // //         field_place,
//     // //         self.root_address.clone().into(),
//     // //         self.inner.position,
//     // //     )
//     // // }

//     // // pub(in super::super::super) fn create_field_snapshot_equality(
//     // //     &mut self,
//     // //     field: &vir_mid::FieldDecl,
//     // // ) -> SpannedEncodingResult<vir_low::Expression> {
//     // //     use vir_low::macros::*;
//     // //     let result = self.inner.result()?;
//     // //     let field_snapshot = self.inner.lowerer.obtain_struct_field_snapshot(
//     // //         self.inner.ty,
//     // //         field,
//     // //         result.into(),
//     // //         self.inner.position,
//     // //     )?;
//     // //     let snap_call = self.create_field_snap_call(&field)?;
//     // //     Ok(expr! {
//     // //         [field_snapshot] == [snap_call]
//     // //     })
//     // // }

//     pub(in super::super::super) fn create_field_snapshot_equality(
//         &mut self,
//         field: &vir_mid::FieldDecl,
//     ) -> SpannedEncodingResult<vir_low::Expression> {
//         let owned_call = self.field_owned_snap()?;
//         self.inner.create_field_snapshot_equality(field, owned_call)
//     }

//     fn field_owned_snap(
//         &mut self,
//     ) -> SpannedEncodingResult<
//         impl Fn(
//             &mut FunctionDeclBuilder,
//             &vir_mid::FieldDecl,
//             vir_low::Expression,
//             vir_low::Expression,
//         ) -> SpannedEncodingResult<vir_low::Expression>,
//     > {
//         let address: vir_low::Expression = self.inner.address.clone().into();
//         let _address = std::rc::Rc::new(address);
//         Ok(
//             move |builder: &mut FunctionDeclBuilder,
//                   field: &vir_mid::FieldDecl,
//                   _,
//                   field_address| {
//                 // let field_address = builder.lowerer.encode_field_address(
//                 //     builder.ty,
//                 //     field,
//                 //     (*address).clone(),
//                 //     builder.position,
//                 // )?;
//                 builder.lowerer.owned_aliased_snap(
//                     CallContext::BuiltinMethod,
//                     &field.ty,
//                     &field.ty,
//                     field_address,
//                     builder.position,
//                 )
//             },
//         )
//     }

//     pub(in super::super::super) fn create_discriminant_snapshot_equality(
//         &mut self,
//         decl: &vir_mid::type_decl::Enum,
//     ) -> SpannedEncodingResult<vir_low::Expression> {
//         use vir_low::macros::*;
//         let result = self.inner.result()?;
//         let discriminant_snapshot = self.inner.lowerer.obtain_enum_discriminant(
//             result.into(),
//             self.inner.ty,
//             self.inner.position,
//         )?;
//         let discriminant_field = decl.discriminant_field();
//         let discriminant_address = self.inner.lowerer.encode_field_address(
//             self.inner.ty,
//             &discriminant_field,
//             self.inner.address.clone().into(),
//             self.inner.position,
//         )?;
//         let snap_call = self.inner.lowerer.owned_aliased_snap(
//             CallContext::BuiltinMethod,
//             &decl.discriminant_type,
//             &decl.discriminant_type,
//             discriminant_address,
//             self.inner.position,
//         )?;
//         let snap_call_int = self.inner.lowerer.obtain_constant_value(
//             &decl.discriminant_type,
//             snap_call,
//             self.inner.position,
//         )?;
//         Ok(expr! {
//             [discriminant_snapshot] == [snap_call_int]
//         })
//     }

//     pub(in super::super::super) fn create_variant_snapshot_equality(
//         &mut self,
//         discriminant_value: vir_mid::DiscriminantValue,
//         variant: &vir_mid::type_decl::Struct,
//     ) -> SpannedEncodingResult<(vir_low::Expression, vir_low::Expression)> {
//         use vir_low::macros::*;
//         let result = self.inner.result()?;
//         let discriminant_call = self.inner.lowerer.obtain_enum_discriminant(
//             result.clone().into(),
//             self.inner.ty,
//             self.inner.position,
//         )?;
//         let guard = expr! {
//             [ discriminant_call ] == [ discriminant_value.into() ]
//         };
//         let variant_index = variant.name.clone().into();
//         let variant_address = self.inner.lowerer.encode_enum_variant_address(
//             self.inner.ty,
//             &variant_index,
//             self.inner.address.clone().into(),
//             self.inner.position,
//         )?;
//         let variant_snapshot = self.inner.lowerer.obtain_enum_variant_snapshot(
//             self.inner.ty,
//             &variant_index,
//             result.into(),
//             self.inner.position,
//         )?;
//         let ty = self.inner.ty.clone();
//         let variant_type = ty.variant(variant_index);
//         let snap_call = self.inner.lowerer.owned_aliased_snap(
//             CallContext::BuiltinMethod,
//             &variant_type,
//             // Enum variant and enum have the same set of lifetime parameters,
//             // so we use type_decl here. We cannot use `variant_type` because
//             // `ty` is normalized.
//             self.inner.type_decl,
//             variant_address,
//             self.inner.position,
//         )?;
//         let equality = expr! {
//             [variant_snapshot] == [snap_call]
//         };
//         Ok((guard, equality))
//     }

//     pub(in super::super::super) fn add_reference_snapshot_equalities(
//         &mut self,
//         decl: &vir_mid::type_decl::Reference,
//         lifetime: &vir_mid::ty::LifetimeConst,
//     ) -> SpannedEncodingResult<()> {
//         use vir_low::macros::*;
//         let result = self.inner.result()?;
//         let guard = self
//             .inner
//             .lowerer
//             .encode_lifetime_const_into_pure_is_alive_variable(lifetime)?;
//         let lifetime = lifetime.to_pure_snapshot(self.inner.lowerer)?;
//         let place = self
//             .inner
//             .lowerer
//             .encode_aliased_place_root(self.inner.position)?;
//         let deref_place = self
//             .inner
//             .lowerer
//             .reference_deref_place(place, self.inner.position)?;
//         let current_snapshot = self.inner.lowerer.reference_target_current_snapshot(
//             self.inner.ty,
//             result.clone().into(),
//             self.inner.position,
//         )?;
//         let final_snapshot = self.inner.lowerer.reference_target_final_snapshot(
//             self.inner.ty,
//             result.clone().into(),
//             self.inner.position,
//         )?;
//         let address = self.inner.lowerer.reference_address(
//             self.inner.ty,
//             result.clone().into(),
//             self.inner.position,
//         )?;
//         let slice_len = self.inner.lowerer.reference_slice_len(
//             self.inner.ty,
//             result.into(),
//             self.inner.position,
//         )?;
//         let equalities = if decl.uniqueness.is_unique() {
//             let current_snap_call = self.inner.lowerer.unique_ref_snap(
//                 CallContext::BuiltinMethod,
//                 &decl.target_type,
//                 &decl.target_type,
//                 deref_place.clone(),
//                 address.clone(),
//                 lifetime.clone().into(),
//                 slice_len.clone(),
//                 false,
//                 self.inner.position,
//             )?;
//             let final_snap_call = self.inner.lowerer.unique_ref_snap(
//                 CallContext::BuiltinMethod,
//                 &decl.target_type,
//                 &decl.target_type,
//                 deref_place,
//                 address,
//                 lifetime.into(),
//                 slice_len,
//                 true,
//                 self.inner.position,
//             )?;
//             expr! {
//                 ([current_snapshot] == [current_snap_call]) &&
//                 ([final_snapshot] == [final_snap_call])
//             }
//         } else {
//             let snap_call = self.inner.lowerer.frac_ref_snap(
//                 CallContext::BuiltinMethod,
//                 &decl.target_type,
//                 &decl.target_type,
//                 deref_place,
//                 address,
//                 lifetime.into(),
//                 slice_len,
//                 self.inner.position,
//             )?;
//             expr! {
//                 [current_snapshot] == [snap_call]
//             }
//         };
//         let expression = expr! {
//             guard ==> [equalities]
//         };
//         self.add_snapshot_body_postcondition(expression)
//     }

//     pub(in super::super::super) fn add_structural_invariant(
//         &mut self,
//         decl: &vir_mid::type_decl::Struct,
//     ) -> SpannedEncodingResult<()> {
//         // let precondition_predicate = self.precondition_predicate()?;
//         let predicate_kind = PredicateKind::Owned;
//         let snap_call = self.field_owned_snap()?;
//         self.inner
//             .add_structural_invariant(decl, false, predicate_kind, &snap_call)
//     }

//     pub(in super::super::super) fn take_owned_snapshot_functions_to_encode(
//         &mut self,
//     ) -> Vec<vir_mid::Type> {
//         std::mem::take(&mut self.inner.owned_snapshot_functions_to_encode)
//     }

//     pub(in super::super::super) fn take_owned_range_snapshot_functions_to_encode(
//         &mut self,
//     ) -> Vec<vir_mid::Type> {
//         std::mem::take(&mut self.inner.owned_range_snapshot_functions_to_encode)
//     }
// }
