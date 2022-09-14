// use crate::encoder::{
//     errors::SpannedEncodingResult,
//     middle::core_proof::{
//         addresses::AddressesInterface,
//         builtin_methods::CallContext,
//         lowerer::Lowerer,
//         places::PlacesInterface,
//         predicates::{
//             owned::builders::{
//                 common::predicate_decl::PredicateDeclBuilder, PredicateDeclBuilderMethods,
//             },
//             PredicatesOwnedInterface,
//         },
//         snapshots::{IntoPureSnapshot, PredicateKind, SnapshotValuesInterface},
//         type_layouts::TypeLayoutsInterface,
//     },
// };

// use vir_crate::{
//     common::{expression::GuardedExpressionIterator, position::Positioned},
//     low::{self as vir_low},
//     middle::{self as vir_mid},
// };

// pub(in super::super::super) struct OwnedAliasedBuilder<'l, 'p, 'v, 'tcx> {
//     inner: PredicateDeclBuilder<'l, 'p, 'v, 'tcx>,
//     slice_len: Option<vir_mid::VariableDecl>,
// }

// impl<'l, 'p, 'v, 'tcx> PredicateDeclBuilderMethods<'l, 'p, 'v, 'tcx>
//     for OwnedAliasedBuilder<'l, 'p, 'v, 'tcx>
// {
//     fn inner(&mut self) -> &mut PredicateDeclBuilder<'l, 'p, 'v, 'tcx> {
//         &mut self.inner
//     }
// }

// impl<'l, 'p, 'v, 'tcx> OwnedAliasedBuilder<'l, 'p, 'v, 'tcx> {
//     pub(in super::super::super) fn new(
//         _lowerer: &'l mut Lowerer<'p, 'v, 'tcx>,
//         _ty: &'l vir_mid::Type,
//         _type_decl: &'l vir_mid::TypeDecl,
//     ) -> SpannedEncodingResult<Self> {
//         unimplemented!()
//         // let slice_len = if ty.is_slice() {
//         //     Some(vir_mid::VariableDecl::new(
//         //         "slice_len",
//         //         lowerer.size_type_mid()?,
//         //     ))
//         // } else {
//         //     None
//         // };
//         // let position = type_decl.position();
//         // Ok(Self {
//         //     slice_len,
//         //     inner: PredicateDeclBuilder::new(lowerer, "OwnedAliased", ty, type_decl, position)?,
//         // })
//     }

//     pub(in super::super::super) fn build(self) -> vir_low::PredicateDecl {
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

//     fn size_of(&mut self) -> SpannedEncodingResult<vir_low::Expression> {
//         self.inner
//             .lowerer
//             .encode_type_size_expression2(self.inner.ty, self.inner.type_decl)
//     }

//     fn padding_size(&mut self) -> SpannedEncodingResult<vir_low::Expression> {
//         self.inner
//             .lowerer
//             .encode_type_padding_size_expression(self.inner.ty)
//     }

//     pub(in super::super::super) fn add_base_memory_block(&mut self) -> SpannedEncodingResult<()> {
//         use vir_low::macros::*;
//         let size_of = self.size_of()?;
//         let address = &self.inner.address;
//         let expression = expr! {
//             acc(MemoryBlock(address, [size_of]))
//         };
//         self.inner.add_conjunct(expression)
//     }

//     pub(in super::super::super) fn add_padding_memory_block(
//         &mut self,
//     ) -> SpannedEncodingResult<()> {
//         use vir_low::macros::*;
//         let padding_size = self.padding_size()?;
//         let address = &self.inner.address;
//         let expression = expr! {
//             acc(MemoryBlock(address, [padding_size]))
//         };
//         self.inner.add_conjunct(expression)
//     }

//     pub(in super::super::super) fn add_field_predicate(
//         &mut self,
//         field: &vir_mid::FieldDecl,
//     ) -> SpannedEncodingResult<()> {
//         let field_address = self.inner.lowerer.encode_field_address(
//             self.inner.ty,
//             field,
//             self.inner.address.clone().into(),
//             self.inner.position,
//         )?;
//         let expression = self.inner.lowerer.owned_aliased(
//             CallContext::BuiltinMethod,
//             &field.ty,
//             &field.ty,
//             field_address,
//             None,
//             self.inner.position,
//         )?;
//         self.inner.add_conjunct(expression)
//     }

//     pub(in super::super::super) fn add_discriminant_predicate(
//         &mut self,
//         decl: &vir_mid::type_decl::Enum,
//     ) -> SpannedEncodingResult<()> {
//         let discriminant_field = decl.discriminant_field();
//         let discriminant_address = self.inner.lowerer.encode_field_address(
//             self.inner.ty,
//             &discriminant_field,
//             self.inner.address.clone().into(),
//             self.inner.position,
//         )?;
//         let expression = self.inner.lowerer.owned_aliased(
//             CallContext::BuiltinMethod,
//             &decl.discriminant_type,
//             &decl.discriminant_type,
//             discriminant_address,
//             None,
//             self.inner.position,
//         )?;
//         self.inner.add_conjunct(expression)
//     }

//     pub(in super::super::super) fn add_unique_ref_target_predicate(
//         &mut self,
//         target_type: &vir_mid::Type,
//         lifetime: &vir_mid::ty::LifetimeConst,
//     ) -> SpannedEncodingResult<()> {
//         let place = self
//             .inner
//             .lowerer
//             .encode_aliased_place_root(self.inner.position)?;
//         let root_address = self.inner.address.clone();
//         self.inner.add_unique_ref_target_predicate(
//             target_type,
//             lifetime,
//             place,
//             root_address,
//             false,
//         )
//     }

//     pub(in super::super::super) fn add_frac_ref_target_predicate(
//         &mut self,
//         target_type: &vir_mid::Type,
//         lifetime: &vir_mid::ty::LifetimeConst,
//     ) -> SpannedEncodingResult<()> {
//         let place = self
//             .inner
//             .lowerer
//             .encode_aliased_place_root(self.inner.position)?;
//         let root_address = self.inner.address.clone();
//         self.inner
//             .add_frac_ref_target_predicate(target_type, lifetime, place, root_address)
//     }

//     // FIXME: Code duplication.
//     pub(in super::super::super) fn get_slice_len(
//         &self,
//     ) -> SpannedEncodingResult<vir_mid::VariableDecl> {
//         Ok(self.slice_len.as_ref().unwrap().clone())
//     }

//     // pub(in super::super::super) fn add_quantified_permission(
//     //     &mut self,
//     //     array_length_mid: &vir_mid::VariableDecl,
//     //     element_type: &vir_mid::Type,
//     // ) -> SpannedEncodingResult<()> {
//     //     use vir_low::macros::*;
//     //     let size_type = self.inner.lowerer.size_type()?;
//     //     let size_type_mid = self.inner.lowerer.size_type_mid()?;
//     //     var_decls! {
//     //         index: {size_type}
//     //     };
//     //     let index_validity = self
//     //         .inner
//     //         .lowerer
//     //         .encode_snapshot_valid_call_for_type(index.clone().into(), &size_type_mid)?;
//     //     let index_int = self.inner.lowerer.obtain_constant_value(
//     //         &size_type_mid,
//     //         index.clone().into(),
//     //         self.inner.position,
//     //     )?;
//     //     let array_length_int = self.inner.array_length_int(array_length_mid)?;
//     //     let element_place = self.inner.lowerer.encode_index_place(
//     //         self.inner.ty,
//     //         self.inner.place.clone().into(),
//     //         index.clone().into(),
//     //         self.inner.position,
//     //     )?;
//     //     let element_snapshot = self.inner.lowerer.obtain_array_element_snapshot(
//     //         self.snapshot.clone().into(),
//     //         index_int.clone(),
//     //         self.inner.position,
//     //     )?;
//     //     let element_predicate_acc = self.inner.lowerer.owned_non_aliased(
//     //         CallContext::BuiltinMethod,
//     //         element_type,
//     //         element_type,
//     //         element_place,
//     //         self.inner.root_address.clone().into(),
//     //         element_snapshot,
//     //         None,
//     //     )?;
//     //     let elements = vir_low::Expression::forall(
//     //         vec![index],
//     //         vec![vir_low::Trigger::new(vec![element_predicate_acc.clone()])],
//     //         expr! {
//     //             ([index_validity] && ([index_int] < [array_length_int])) ==>
//     //             [element_predicate_acc]
//     //         },
//     //     );
//     //     self.inner.add_conjunct(elements)
//     // }

//     pub(in super::super::super) fn create_variant_predicate(
//         &mut self,
//         decl: &vir_mid::type_decl::Enum,
//         discriminant_value: vir_mid::DiscriminantValue,
//         variant: &vir_mid::type_decl::Struct,
//         variant_type: &vir_mid::Type,
//     ) -> SpannedEncodingResult<(vir_low::Expression, vir_low::Expression)> {
//         use vir_low::macros::*;
//         let discriminant_call = {
//             let discriminant_field = decl.discriminant_field();
//             let discriminant_address = self.inner.lowerer.encode_field_address(
//                 self.inner.ty,
//                 &discriminant_field,
//                 self.inner.place.clone().into(),
//                 self.inner.position,
//             )?;
//             let discriminant_snapshot = self.inner.lowerer.owned_aliased_snap(
//                 CallContext::BuiltinMethod,
//                 &decl.discriminant_type,
//                 &decl.discriminant_type,
//                 discriminant_address,
//                 self.inner.position,
//             )?;
//             self.inner.lowerer.obtain_constant_value(
//                 &decl.discriminant_type,
//                 discriminant_snapshot,
//                 self.inner.position,
//             )?
//         };
//         let guard = expr! {
//             [ discriminant_call ] == [ discriminant_value.into() ]
//         };
//         let variant_index = variant.name.clone().into();
//         let variant_address = self.inner.lowerer.encode_enum_variant_address(
//             self.inner.ty,
//             &variant_index,
//             self.inner.place.clone().into(),
//             self.inner.position,
//         )?;
//         let predicate = self.inner.lowerer.owned_aliased(
//             CallContext::BuiltinMethod,
//             variant_type,
//             variant_type,
//             variant_address,
//             None,
//             self.inner.position,
//         )?;
//         Ok((guard, predicate))
//     }

//     pub(in super::super::super) fn add_variant_predicates(
//         &mut self,
//         variant_predicates: Vec<(vir_low::Expression, vir_low::Expression)>,
//     ) -> SpannedEncodingResult<()> {
//         self.inner
//             .add_conjunct(variant_predicates.into_iter().create_match())
//     }

//     pub(in super::super::super) fn add_structural_invariant(
//         &mut self,
//         decl: &vir_mid::type_decl::Struct,
//     ) -> SpannedEncodingResult<Vec<vir_mid::Type>> {
//         self.inner
//             .add_structural_invariant(decl, PredicateKind::Owned)
//     }
// }
