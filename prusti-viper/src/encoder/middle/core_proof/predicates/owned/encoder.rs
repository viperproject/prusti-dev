use crate::encoder::{
    errors::SpannedEncodingResult,
    high::types::HighTypeEncoderInterface,
    middle::core_proof::{
        compute_address::ComputeAddressInterface,
        lowerer::Lowerer,
        places::PlacesInterface,
        predicates::{PredicatesMemoryBlockInterface, PredicatesOwnedInterface},
        references::ReferencesInterface,
        snapshots::{
            IntoSnapshot, SnapshotBytesInterface, SnapshotValidityInterface,
            SnapshotValuesInterface,
        },
        type_layouts::TypeLayoutsInterface,
        types::TypesInterface,
    },
};
use rustc_hash::FxHashSet;
use std::borrow::Cow;
use vir_crate::{
    common::expression::{ExpressionIterator, QuantifierHelpers},
    low::{self as vir_low},
    middle as vir_mid,
};

pub(super) struct PredicateEncoder<'l, 'p, 'v, 'tcx> {
    lowerer: &'l mut Lowerer<'p, 'v, 'tcx>,
    unfolded_owned_non_aliased_predicates: &'l FxHashSet<vir_mid::Type>,
    encoded_owned_predicates: FxHashSet<vir_mid::Type>,
    encoded_mut_borrow_predicates: FxHashSet<vir_mid::Type>,
    encoded_frac_borrow_predicates: FxHashSet<vir_mid::Type>,
    predicates: Vec<vir_low::PredicateDecl>,
}

impl<'l, 'p, 'v, 'tcx> PredicateEncoder<'l, 'p, 'v, 'tcx> {
    pub(super) fn new(
        lowerer: &'l mut Lowerer<'p, 'v, 'tcx>,
        unfolded_owned_non_aliased_predicates: &'l FxHashSet<vir_mid::Type>,
    ) -> Self {
        Self {
            lowerer,
            unfolded_owned_non_aliased_predicates,
            encoded_owned_predicates: Default::default(),
            encoded_mut_borrow_predicates: Default::default(),
            encoded_frac_borrow_predicates: Default::default(),
            predicates: Default::default(),
        }
    }

    pub(super) fn into_predicates(self) -> Vec<vir_low::PredicateDecl> {
        self.predicates
    }

    pub(super) fn encode_owned_non_aliased(
        &mut self,
        ty_with_lifetime: &vir_mid::Type,
    ) -> SpannedEncodingResult<()> {
        let ty: &mut vir_mid::Type = &mut ty_with_lifetime.clone();
        ty.erase_lifetime();
        if self.encoded_owned_predicates.contains(ty) {
            return Ok(());
        }
        self.encoded_owned_predicates.insert(ty.clone());
        self.lowerer.encode_compute_address(ty)?;
        use vir_low::macros::*;
        let position = Default::default();
        let type_decl = self.lowerer.encoder.get_type_decl_mid(ty)?;
        self.lowerer.encode_snapshot_to_bytes_function(ty)?;
        let snapshot_type = ty.to_snapshot(self.lowerer)?;
        var_decls! {
            place: Place,
            root_address: Address,
            snapshot: {snapshot_type.clone()}
        }
        let compute_address = ty!(Address);
        let to_bytes = ty! { Bytes };
        let validity = self
            .lowerer
            .encode_snapshot_valid_call_for_type(snapshot.clone().into(), ty)?;
        let size_of = self.lowerer.encode_type_size_expression(ty)?;
        let compute_address = expr! { ComputeAddress::compute_address(place, root_address) };
        let bytes = self
            .lowerer
            .encode_memory_block_bytes_expression(compute_address.clone(), size_of.clone())?;
        let predicate = match &type_decl {
            vir_mid::TypeDecl::Bool
            | vir_mid::TypeDecl::Int(_)
            | vir_mid::TypeDecl::Float(_)
            | vir_mid::TypeDecl::Pointer(_)
            | vir_mid::TypeDecl::Sequence(_)
            | vir_mid::TypeDecl::Map(_) => {
                predicate! {
                    OwnedNonAliased<ty>(place: Place, root_address: Address, snapshot: {snapshot_type})
                    {(
                        ([validity]) &&
                        (acc(MemoryBlock([compute_address], [size_of]))) &&
                        (([bytes]) == (Snap<ty>::to_bytes(snapshot)))
                    )}
                }
            }
            vir_mid::TypeDecl::TypeVar(_) | vir_mid::TypeDecl::Trusted(_) => {
                vir_low::PredicateDecl::new(
                    predicate_name! { OwnedNonAliased<ty> },
                    vars! { place: Place, root_address: Address, snapshot: {snapshot_type} },
                    None,
                )
            }
            vir_mid::TypeDecl::Tuple(tuple_decl) => self.encode_owned_non_aliased_with_fields(
                ty,
                snapshot,
                snapshot_type,
                validity,
                tuple_decl.iter_fields(),
            )?,
            vir_mid::TypeDecl::Struct(struct_decl) => self.encode_owned_non_aliased_with_fields(
                ty,
                snapshot,
                snapshot_type,
                validity,
                struct_decl.iter_fields(),
            )?,
            vir_mid::TypeDecl::Enum(decl) => {
                let mut variant_predicates = Vec::new();
                let discriminant_call =
                    self.lowerer
                        .obtain_enum_discriminant(snapshot.clone().into(), ty, position)?;
                for (&discriminant, variant) in decl.discriminant_values.iter().zip(&decl.variants)
                {
                    let variant_index = variant.name.clone().into();
                    let variant_place = self.lowerer.encode_enum_variant_place(
                        ty,
                        &variant_index,
                        place.clone().into(),
                        position,
                    )?;
                    let variant_snapshot = self.lowerer.obtain_enum_variant_snapshot(
                        ty,
                        &variant_index,
                        snapshot.clone().into(),
                        position,
                    )?;
                    let variant_type = ty.clone().variant(variant_index);
                    if !self
                        .unfolded_owned_non_aliased_predicates
                        .contains(&variant_type)
                    {
                        // TODO: Optimization: This variant is never unfolded,
                        // encode it as abstract predicate.
                        self.encode_owned_non_aliased(&variant_type)?;
                    }
                    let variant_type = &variant_type;
                    let acc = expr! {
                        ([ discriminant_call.clone() ] == [ discriminant.into() ]) ==>
                        (acc(OwnedNonAliased<variant_type>(
                            [variant_place], root_address, [variant_snapshot]
                        )))
                    };
                    variant_predicates.push(acc);
                }
                let discriminant_type = &decl.discriminant_type;
                if !self
                    .unfolded_owned_non_aliased_predicates
                    .contains(discriminant_type)
                {
                    // TODO: Optimization: The discriminant is never unfolded,
                    // encode it as abstract predicate.
                    self.encode_owned_non_aliased(discriminant_type)?;
                }
                let discriminant_field = decl.discriminant_field();
                let discriminant_place = self.lowerer.encode_field_place(
                    ty,
                    &discriminant_field,
                    place.into(),
                    position,
                )?;
                let discriminant_snapshot = self.lowerer.construct_constant_snapshot(
                    discriminant_type,
                    discriminant_call,
                    position,
                )?;
                predicate! {
                    OwnedNonAliased<ty>(place: Place, root_address: Address, snapshot: {snapshot_type})
                    {(
                        ([validity]) &&
                        (acc(OwnedNonAliased<discriminant_type>(
                            [discriminant_place], root_address, [discriminant_snapshot]
                        ))) &&
                        ([variant_predicates.into_iter().conjoin()])
                    )}
                }
            }
            vir_mid::TypeDecl::Union(decl) => {
                let mut variant_predicates = Vec::new();
                let discriminant_call =
                    self.lowerer
                        .obtain_enum_discriminant(snapshot.clone().into(), ty, position)?;
                for (&discriminant, variant) in decl.discriminant_values.iter().zip(&decl.variants)
                {
                    let variant_index = variant.name.clone().into();
                    let variant_place = self.lowerer.encode_enum_variant_place(
                        ty,
                        &variant_index,
                        place.clone().into(),
                        position,
                    )?;
                    let variant_snapshot = self.lowerer.obtain_enum_variant_snapshot(
                        ty,
                        &variant_index,
                        snapshot.clone().into(),
                        position,
                    )?;
                    let variant_type = ty.clone().variant(variant_index);
                    if !self
                        .unfolded_owned_non_aliased_predicates
                        .contains(&variant_type)
                    {
                        // TODO: Optimization: This variant is never unfolded,
                        // encode it as abstract predicate.
                        self.encode_owned_non_aliased(&variant_type)?;
                    }
                    let variant_type = &variant_type;
                    let acc = expr! {
                        ([ discriminant_call.clone() ] == [ discriminant.into() ]) ==>
                        (acc(OwnedNonAliased<variant_type>(
                            [variant_place], root_address, [variant_snapshot]
                        )))
                    };
                    variant_predicates.push(acc);
                }
                predicate! {
                    OwnedNonAliased<ty>(place: Place, root_address: Address, snapshot: {snapshot_type})
                    {(
                        ([validity]) &&
                        ([variant_predicates.into_iter().conjoin()])
                    )}
                }
            }
            vir_mid::TypeDecl::Array(decl) => {
                let element_type = &decl.element_type;
                self.lowerer.encode_place_array_index_axioms(ty)?;
                self.lowerer.ensure_type_definition(element_type)?;
                let parameters = self.lowerer.extract_non_type_parameters_from_type(ty)?;
                let parameters_validity: vir_low::Expression = self
                    .lowerer
                    .extract_non_type_parameters_from_type_validity(ty)?
                    .into_iter()
                    .conjoin();
                var_decls! {
                    index: Int,
                    snapshot: {snapshot_type.clone()}
                };
                let snapshot_length = self
                    .lowerer
                    .obtain_array_len_snapshot(snapshot.clone().into(), Default::default())?;
                let array_length = self.lowerer.array_length_variable()?;
                let size_type = self.lowerer.size_type_mid()?;
                let array_length_int = self.lowerer.obtain_constant_value(
                    &size_type,
                    array_length.into(),
                    Default::default(),
                )?;
                let index_usize = self.lowerer.construct_constant_snapshot(
                    &size_type,
                    index.clone().into(),
                    Default::default(),
                )?;
                let element_place = self.lowerer.encode_index_place(
                    ty,
                    place.into(),
                    index_usize,
                    Default::default(),
                )?;
                let element_snapshot = self.lowerer.obtain_array_element_snapshot(
                    snapshot.into(),
                    index.clone().into(),
                    Default::default(),
                )?;

                let element_predicate_acc = expr! {
                    (acc(OwnedNonAliased<element_type>(
                        [element_place], root_address, [element_snapshot]
                    )))
                };
                let elements = vir_low::Expression::forall(
                    vec![index.clone()],
                    vec![vir_low::Trigger::new(vec![element_predicate_acc.clone()])],
                    expr! {
                        (([0.into()] <= index) && (index < [array_length_int.clone()])) ==>
                        [element_predicate_acc]
                    },
                );
                self.encode_owned_non_aliased(element_type)?;
                predicate! {
                    OwnedNonAliased<ty>(
                        place: Place,
                        root_address: Address,
                        snapshot: {snapshot_type},
                        *parameters
                    )
                    {(
                        [validity] &&
                        [parameters_validity] &&
                        ([array_length_int] == [snapshot_length]) &&
                        [elements]
                    )}
                }
            }
            vir_mid::TypeDecl::Reference(reference) if reference.uniqueness.is_unique() => {
                let address_type = &self.lowerer.reference_address_type(ty)?;
                self.lowerer
                    .encode_snapshot_to_bytes_function(address_type)?;
                self.lowerer.ensure_type_definition(address_type)?;
                let target_address_snapshot = self.lowerer.reference_address_snapshot(
                    ty,
                    snapshot.clone().into(),
                    position,
                )?;
                let target_address =
                    self.lowerer
                        .reference_address(ty, snapshot.clone().into(), position)?;
                let current_snapshot = self.lowerer.reference_target_current_snapshot(
                    ty,
                    snapshot.clone().into(),
                    position,
                )?;
                let final_snapshot =
                    self.lowerer
                        .reference_target_final_snapshot(ty, snapshot.into(), position)?;
                let target_type = &reference.target_type;
                let deref_place = self.lowerer.reference_deref_place(place.into(), position)?;
                self.encode_unique_ref(target_type)?;
                predicate! {
                    OwnedNonAliased<ty>(
                        place: Place,
                        root_address: Address,
                        snapshot: {snapshot_type},
                        lifetime: Lifetime
                    )
                    {(
                        ([validity]) &&
                        (acc(MemoryBlock([compute_address], [size_of]))) &&
                        (([bytes]) == (Snap<address_type>::to_bytes([target_address_snapshot]))) &&
                        (acc(UniqueRef<target_type>(
                            lifetime, [deref_place], [target_address], [current_snapshot], [final_snapshot]
                        )))
                    )}
                }
            }
            vir_mid::TypeDecl::Reference(reference) if reference.uniqueness.is_shared() => {
                let address_type = &self.lowerer.reference_address_type(ty)?;
                self.lowerer
                    .encode_snapshot_to_bytes_function(address_type)?;
                self.lowerer.ensure_type_definition(address_type)?;
                let target_address_snapshot = self.lowerer.reference_address_snapshot(
                    ty,
                    snapshot.clone().into(),
                    position,
                )?;
                let target_address =
                    self.lowerer
                        .reference_address(ty, snapshot.clone().into(), position)?;
                let current_snapshot = self.lowerer.reference_target_current_snapshot(
                    ty,
                    snapshot.into(),
                    position,
                )?;
                let target_type = &reference.target_type;
                let deref_place = self.lowerer.reference_deref_place(place.into(), position)?;
                self.encode_unique_ref(target_type)?;
                self.encode_frac_ref(target_type)?;
                predicate! {
                    OwnedNonAliased<ty>(
                        place: Place,
                        root_address: Address,
                        snapshot: {snapshot_type},
                        lifetime: Lifetime
                    )
                    {(
                        ([validity]) &&
                        (acc(MemoryBlock([compute_address], [size_of]))) &&
                        (([bytes]) == (Snap<address_type>::to_bytes([target_address_snapshot]))) &&
                        (acc(FracRef<target_type>(
                            lifetime, [deref_place], [target_address], [current_snapshot]
                        )))
                    )}
                }
            }
            // vir_mid::TypeDecl::Never => {},
            // vir_mid::TypeDecl::Closure(Closure) => {},
            // vir_mid::TypeDecl::Unsupported(Unsupported) => {},
            x => unimplemented!("{}", x),
        };
        self.predicates.push(predicate);
        Ok(())
    }

    fn encode_owned_non_aliased_with_fields<'a>(
        &mut self,
        ty: &vir_mid::Type,
        snapshot: vir_low::VariableDecl,
        snapshot_type: vir_low::Type,
        validity: vir_low::Expression,
        fields: impl Iterator<Item = Cow<'a, vir_mid::FieldDecl>>,
    ) -> SpannedEncodingResult<vir_low::PredicateDecl> {
        use vir_low::macros::*;
        var_decls! {
            place: Place,
            root_address: Address
        }
        let mut field_predicates = Vec::new();
        let mut lifetimes = Vec::new();
        for (i, field) in fields.enumerate() {
            let field_place = self.lowerer.encode_field_place(
                ty,
                &field,
                place.clone().into(),
                Default::default(),
            )?;
            let field_value = self.lowerer.obtain_struct_field_snapshot(
                ty,
                &field,
                snapshot.clone().into(),
                Default::default(),
            )?;
            let field_ty = &field.ty;
            if let vir_mid::Type::Reference(_) = field_ty {
                let lifetime =
                    vir_low::VariableDecl::new(format!("lft_field_{}", i), ty!(Lifetime));
                lifetimes.push(lifetime.clone());
                let acc = expr! {
                    acc(OwnedNonAliased<field_ty>(
                        [field_place], root_address, [field_value], [lifetime.into()]
                    ))
                };
                field_predicates.push(acc);
            } else {
                let acc = expr! {
                    acc(OwnedNonAliased<field_ty>(
                        [field_place], root_address, [field_value]
                    ))
                };
                field_predicates.push(acc);
            }
        }
        if field_predicates.is_empty() {
            // TODO: Extract this into a separate method and deduplicate with
            // primitive type encoding.

            // FIXME: We should add an extra memory block not only for ZSTs, but
            // also for types to represent padding bytes and similar stuff.
            let compute_address = ty!(Address);
            let to_bytes = ty! { Bytes };
            let compute_address = expr! { ComputeAddress::compute_address(place, root_address) };
            let size_of = self.lowerer.encode_type_size_expression(ty)?;
            let bytes = self
                .lowerer
                .encode_memory_block_bytes_expression(compute_address.clone(), size_of.clone())?;
            field_predicates.push(expr! {
                (acc(MemoryBlock([compute_address], [size_of])))
            });
            field_predicates.push(expr! {
                (([bytes]) == (Snap<ty>::to_bytes(snapshot)))
            });
        }
        let predicate_decl = predicate! {
            OwnedNonAliased<ty>(place: Place, root_address: Address, snapshot: {snapshot_type}, *lifetimes)
            {(
                ([validity]) &&
                ([field_predicates.into_iter().conjoin()])
            )}
        };
        Ok(predicate_decl)
    }

    fn encode_frac_ref(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<()> {
        if self.encoded_frac_borrow_predicates.contains(ty) {
            return Ok(());
        }
        self.encoded_frac_borrow_predicates.insert(ty.clone());
        self.lowerer.encode_compute_address(ty)?;
        use vir_low::macros::*;
        let type_decl = self.lowerer.encoder.get_type_decl_mid(ty)?;
        self.lowerer.encode_snapshot_to_bytes_function(ty)?;
        let snapshot_type = ty.to_snapshot(self.lowerer)?;
        var_decls! {
            lifetime: Lifetime,
            place: Place,
            root_address: Address,
            snapshot: {snapshot_type}
        }
        let current_validity = self
            .lowerer
            .encode_snapshot_valid_call_for_type(snapshot.clone().into(), ty)?;
        let predicate = match &type_decl {
            vir_mid::TypeDecl::Bool
            | vir_mid::TypeDecl::Int(_)
            | vir_mid::TypeDecl::Float(_)
            | vir_mid::TypeDecl::Pointer(_)
            | vir_mid::TypeDecl::Sequence(_)
            | vir_mid::TypeDecl::Map(_) => vir_low::PredicateDecl::new(
                predicate_name! {FracRef<ty>},
                vec![lifetime, place, root_address, snapshot],
                None,
            ),
            // vir_mid::TypeDecl::TypeVar(TypeVar) => {},
            vir_mid::TypeDecl::Tuple(_decl) => unimplemented!(),
            vir_mid::TypeDecl::Struct(decl) => {
                // TODO: test or add unimplemented!
                let mut field_predicates = Vec::new();
                for field in &decl.fields {
                    let field_place = self.lowerer.encode_field_place(
                        ty,
                        field,
                        place.clone().into(),
                        Default::default(),
                    )?;
                    let field_snapshot = self.lowerer.obtain_struct_field_snapshot(
                        ty,
                        field,
                        snapshot.clone().into(),
                        Default::default(),
                    )?;
                    let field_ty = &field.ty;
                    self.encode_frac_ref(field_ty)?;
                    let acc = expr! {
                        acc(FracRef<field_ty>(
                            lifetime,
                            [field_place],
                            root_address,
                            [field_snapshot]
                        ))
                    };
                    field_predicates.push(acc);
                }
                if field_predicates.is_empty() {
                    unimplemented!();
                }
                vir_low::PredicateDecl::new(
                    predicate_name! {FracRef<ty>},
                    vec![lifetime, place, root_address, snapshot],
                    Some(expr! {
                        [current_validity] &&
                        [field_predicates.into_iter().conjoin()]
                    }),
                )
            }
            vir_mid::TypeDecl::Enum(_decl) => {
                unimplemented!();
            }
            vir_mid::TypeDecl::Union(_decl) => {
                unimplemented!();
            }
            // vir_mid::TypeDecl::Array(Array) => {},
            vir_mid::TypeDecl::Reference(reference) if reference.uniqueness.is_unique() => {
                unimplemented!();
            }
            // vir_mid::TypeDecl::Never => {},
            // vir_mid::TypeDecl::Closure(Closure) => {},
            // vir_mid::TypeDecl::Unsupported(Unsupported) => {},
            x => unimplemented!("{}", x),
        };
        self.predicates.push(predicate);
        Ok(())
    }

    fn encode_unique_ref(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<()> {
        if self.encoded_mut_borrow_predicates.contains(ty) {
            return Ok(());
        }
        self.encoded_mut_borrow_predicates.insert(ty.clone());
        self.lowerer.encode_compute_address(ty)?;
        use vir_low::macros::*;
        // let position = Default::default();
        let type_decl = self.lowerer.encoder.get_type_decl_mid(ty)?;
        self.lowerer.encode_snapshot_to_bytes_function(ty)?;
        let snapshot_type = ty.to_snapshot(self.lowerer)?;
        var_decls! {
            lifetime: Lifetime,
            place: Place,
            root_address: Address,
            current_snapshot: {snapshot_type.clone()},
            final_snapshot: {snapshot_type}
        }
        // let compute_address = ty!(Address);
        // let to_bytes = ty! { Bytes };
        let current_validity = self
            .lowerer
            .encode_snapshot_valid_call_for_type(current_snapshot.clone().into(), ty)?;
        let final_validity = self
            .lowerer
            .encode_snapshot_valid_call_for_type(final_snapshot.clone().into(), ty)?;
        // let size_of = self.lowerer.encode_type_size_expression(ty)?;
        // let compute_address = expr! { ComputeAddress::compute_address(place, root_address) };
        // let bytes = self
        //     .lowerer
        //     .encode_memory_block_bytes_expression(compute_address.clone(), size_of.clone())?;
        let predicate = match &type_decl {
            vir_mid::TypeDecl::Bool
            | vir_mid::TypeDecl::Int(_)
            | vir_mid::TypeDecl::Float(_)
            | vir_mid::TypeDecl::Pointer(_)
            | vir_mid::TypeDecl::Sequence(_)
            | vir_mid::TypeDecl::Map(_) => vir_low::PredicateDecl::new(
                predicate_name! {UniqueRef<ty>},
                vec![
                    lifetime,
                    place,
                    root_address,
                    current_snapshot,
                    final_snapshot,
                ],
                None,
            ),
            // vir_mid::TypeDecl::TypeVar(TypeVar) => {},
            vir_mid::TypeDecl::Tuple(_decl) => unimplemented!(),
            vir_mid::TypeDecl::Struct(decl) => {
                let mut field_predicates = Vec::new();
                for field in &decl.fields {
                    let field_place = self.lowerer.encode_field_place(
                        ty,
                        field,
                        place.clone().into(),
                        Default::default(),
                    )?;
                    let current_field_snapshot = self.lowerer.obtain_struct_field_snapshot(
                        ty,
                        field,
                        current_snapshot.clone().into(),
                        Default::default(),
                    )?;
                    let final_field_snapshot = self.lowerer.obtain_struct_field_snapshot(
                        ty,
                        field,
                        final_snapshot.clone().into(),
                        Default::default(),
                    )?;
                    let field_ty = &field.ty;
                    self.encode_unique_ref(field_ty)?;
                    let acc = expr! {
                        acc(UniqueRef<field_ty>(
                            lifetime,
                            [field_place],
                            root_address,
                            [current_field_snapshot],
                            [final_field_snapshot]
                        ))
                    };
                    field_predicates.push(acc);
                }
                if field_predicates.is_empty() {
                    unimplemented!();
                }
                vir_low::PredicateDecl::new(
                    predicate_name! {UniqueRef<ty>},
                    vec![
                        lifetime,
                        place,
                        root_address,
                        current_snapshot,
                        final_snapshot,
                    ],
                    Some(expr! {
                        [current_validity] &&
                        [final_validity] &&
                        [field_predicates.into_iter().conjoin()]
                    }),
                )
            }
            vir_mid::TypeDecl::Enum(_decl) => {
                unimplemented!();
            }
            vir_mid::TypeDecl::Union(_decl) => {
                unimplemented!();
            }
            // vir_mid::TypeDecl::Array(Array) => {},
            vir_mid::TypeDecl::Reference(reference) if reference.uniqueness.is_unique() => {
                unimplemented!();
            }
            // vir_mid::TypeDecl::Never => {},
            // vir_mid::TypeDecl::Closure(Closure) => {},
            // vir_mid::TypeDecl::Unsupported(Unsupported) => {},
            x => unimplemented!("{}", x),
        };
        self.predicates.push(predicate);
        Ok(())
    }
}
