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
    middle::operations::lifetimes::WithLifetimes,
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
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<()> {
        let ty_without_lifetime = ty.clone().erase_lifetimes();
        if self.encoded_owned_predicates.contains(&ty_without_lifetime) {
            return Ok(());
        }
        self.encoded_owned_predicates.insert(ty_without_lifetime);
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
            | vir_mid::TypeDecl::Trusted(_)
            | vir_mid::TypeDecl::Map(_) => {
                let mut lifetimes_ty = vec![];
                for lifetime in ty.get_lifetimes() {
                    lifetimes_ty.push(vir_low::VariableDecl {
                        name: lifetime.name.clone(),
                        ty: ty!(Lifetime),
                    });
                }
                predicate! {
                    OwnedNonAliased<ty>(
                        place: Place,
                        root_address: Address,
                        snapshot: {snapshot_type},
                        *lifetimes_ty
                    )
                    {(
                        ([validity]) &&
                        (acc(MemoryBlock([compute_address], [size_of]))) &&
                        (([bytes]) == (Snap<ty>::to_bytes(snapshot)))
                    )}
                }
            }
            vir_mid::TypeDecl::TypeVar(_) => {
                let mut lifetimes_ty = vec![];
                for lifetime in ty.get_lifetimes() {
                    lifetimes_ty.push(vir_low::VariableDecl {
                        name: lifetime.name.clone(),
                        ty: ty!(Lifetime),
                    });
                }
                let mut parameters = vars! {
                    place: Place,
                    root_address: Address,
                    snapshot: {snapshot_type}
                };
                parameters.extend(lifetimes_ty);
                vir_low::PredicateDecl::new(
                    predicate_name! { OwnedNonAliased<ty> },
                    parameters,
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
                let mut lifetimes_ty = vec![];
                for lifetime in ty.get_lifetimes() {
                    lifetimes_ty.push(vir_low::VariableDecl {
                        name: lifetime.name.clone(),
                        ty: ty!(Lifetime),
                    });
                }
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
                    let lifetimes_variant_type_expr: Vec<vir_low::Expression> = variant_type
                        .get_lifetimes()
                        .iter()
                        .map(|x| {
                            vir_low::VariableDecl {
                                name: x.name.clone(),
                                ty: ty!(Lifetime),
                            }
                            .into()
                        })
                        .collect();
                    let acc = expr! {
                        ([ discriminant_call.clone() ] == [ discriminant.into() ]) ==>
                        (acc(OwnedNonAliased<variant_type>(
                            [variant_place],
                            root_address,
                            [variant_snapshot];
                            lifetimes_variant_type_expr
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
                let mut lifetimes_discriminant_type: Vec<vir_low::Expression> = vec![];
                for lifetime in discriminant_type.get_lifetimes() {
                    lifetimes_discriminant_type.push(
                        vir_low::VariableDecl {
                            name: lifetime.name.clone(),
                            ty: ty!(Lifetime),
                        }
                        .into(),
                    );
                }
                predicate! {
                    OwnedNonAliased<ty>(
                        place: Place,
                        root_address: Address,
                        snapshot: {snapshot_type},
                        *lifetimes_ty
                    )
                    {(
                        ([validity]) &&
                        (acc(OwnedNonAliased<discriminant_type>(
                            [discriminant_place],
                            root_address,
                            [discriminant_snapshot];
                            lifetimes_discriminant_type
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
                    let mut lifetimes_variant_type: Vec<vir_low::Expression> = vec![];
                    for lifetime in variant_type.get_lifetimes() {
                        lifetimes_variant_type.push(
                            vir_low::VariableDecl {
                                name: lifetime.name.clone(),
                                ty: ty!(Lifetime),
                            }
                            .into(),
                        );
                    }
                    let acc = expr! {
                        ([ discriminant_call.clone() ] == [ discriminant.into() ]) ==>
                        (acc(OwnedNonAliased<variant_type>(
                            [variant_place],
                            root_address,
                            [variant_snapshot];
                            lifetimes_variant_type
                        )))
                    };
                    variant_predicates.push(acc);
                }
                let mut lifetimes_ty = vec![];
                for lifetime in ty.get_lifetimes() {
                    lifetimes_ty.push(vir_low::VariableDecl {
                        name: lifetime.name.clone(),
                        ty: ty!(Lifetime),
                    });
                }
                predicate! {
                    OwnedNonAliased<ty>(
                        place: Place,
                        root_address: Address,
                        snapshot: {snapshot_type},
                        *lifetimes_ty
                    )
                    {(
                        ([validity]) &&
                        ([variant_predicates.into_iter().conjoin()])
                    )}
                }
            }
            vir_mid::TypeDecl::Array(decl) => {
                self.lowerer.encode_place_array_index_axioms(ty)?;
                let element_type = &decl.element_type;
                self.lowerer.encode_place_array_index_axioms(ty)?;
                self.lowerer.ensure_type_definition(element_type)?;
                let mut parameters: Vec<vir_low::VariableDecl> =
                    self.lowerer.extract_non_type_parameters_from_type(ty)?;
                let parameters_validity: vir_low::Expression = self
                    .lowerer
                    .extract_non_type_parameters_from_type_validity(ty)?
                    .into_iter()
                    .conjoin();
                let size_type = self.lowerer.size_type()?;
                var_decls! {
                    index: {size_type},
                    snapshot: {snapshot_type.clone()}
                };
                let snapshot_length = self
                    .lowerer
                    .obtain_array_len_snapshot(snapshot.clone().into(), Default::default())?;
                let array_length = self.lowerer.array_length_variable()?;
                let size_type_mid = self.lowerer.size_type_mid()?;
                let array_length_int = self.lowerer.obtain_constant_value(
                    &size_type_mid,
                    array_length.into(),
                    Default::default(),
                )?;
                let index_int = self.lowerer.obtain_constant_value(
                    &size_type_mid,
                    index.clone().into(),
                    position,
                )?;
                let index_validity = self
                    .lowerer
                    .encode_snapshot_valid_call_for_type(index.clone().into(), &size_type_mid)?;
                let element_place = self.lowerer.encode_index_place(
                    ty,
                    place.into(),
                    index.clone().into(),
                    Default::default(),
                )?;
                let element_snapshot = self.lowerer.obtain_array_element_snapshot(
                    snapshot.into(),
                    index_int.clone(),
                    Default::default(),
                )?;
                let mut lifetimes_element_type_expr: Vec<vir_low::Expression> = vec![];
                for lifetime in element_type.get_lifetimes() {
                    lifetimes_element_type_expr.push(
                        vir_low::VariableDecl {
                            name: lifetime.name.clone(),
                            ty: ty!(Lifetime),
                        }
                        .into(),
                    );
                }
                let element_predicate_acc = expr! {
                    (acc(OwnedNonAliased<element_type>(
                        [element_place],
                        root_address,
                        [element_snapshot];
                        lifetimes_element_type_expr
                    )))
                };
                let elements = vir_low::Expression::forall(
                    vec![index],
                    vec![vir_low::Trigger::new(vec![element_predicate_acc.clone()])],
                    expr! {
                        ([index_validity] && ([index_int] < [array_length_int.clone()])) ==>
                        [element_predicate_acc]
                    },
                );
                self.encode_owned_non_aliased(element_type)?;
                let mut lifetimes_ty = vec![];
                for lifetime in ty.get_lifetimes() {
                    lifetimes_ty.push(vir_low::VariableDecl {
                        name: lifetime.name.clone(),
                        ty: ty!(Lifetime),
                    });
                }
                parameters.extend(lifetimes_ty);
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
                let mut lifetimes_ty = vec![];
                for lifetime in reference.target_type.get_lifetimes() {
                    lifetimes_ty.push(vir_low::VariableDecl {
                        name: lifetime.name.clone(),
                        ty: ty!(Lifetime),
                    });
                }
                let lifetimes_ty_expr: Vec<vir_low::Expression> =
                    lifetimes_ty.iter().cloned().map(|x| x.into()).collect();
                predicate! {
                    OwnedNonAliased<ty>(
                        place: Place,
                        root_address: Address,
                        snapshot: {snapshot_type},
                        lifetime: Lifetime,
                        *lifetimes_ty
                    )
                    {(
                        ([validity]) &&
                        (acc(MemoryBlock([compute_address], [size_of]))) &&
                        (([bytes]) == (Snap<address_type>::to_bytes([target_address_snapshot]))) &&
                        (acc(UniqueRef<target_type>(
                            [deref_place], [target_address], [current_snapshot], [final_snapshot], lifetime; lifetimes_ty_expr
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
                self.encode_frac_ref(target_type)?;
                let mut lifetimes_ty = vec![];
                for lifetime in reference.target_type.get_lifetimes() {
                    lifetimes_ty.push(vir_low::VariableDecl {
                        name: lifetime.name.clone(),
                        ty: ty!(Lifetime),
                    });
                }
                let lifetimes_ty_expr: Vec<vir_low::Expression> =
                    lifetimes_ty.iter().cloned().map(|x| x.into()).collect();
                predicate! {
                    OwnedNonAliased<ty>(
                        place: Place,
                        root_address: Address,
                        snapshot: {snapshot_type},
                        lifetime: Lifetime,
                        *lifetimes_ty
                    )
                    {(
                        ([validity]) &&
                        (acc(MemoryBlock([compute_address], [size_of]))) &&
                        (([bytes]) == (Snap<address_type>::to_bytes([target_address_snapshot]))) &&
                        (acc(FracRef<target_type>(
                            [deref_place],
                            [target_address],
                            [current_snapshot],
                            lifetime;
                            lifetimes_ty_expr
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
        let mut lifetimes_ty = vec![];
        for lifetime in ty.get_lifetimes() {
            lifetimes_ty.push(vir_low::VariableDecl {
                name: lifetime.name.clone(),
                ty: ty!(Lifetime),
            });
        }
        let mut field_lifetimes = Vec::new();

        for field in fields {
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
            if !self
                .unfolded_owned_non_aliased_predicates
                .contains(field_ty)
            {
                // TODO: Optimization: This variant is never unfolded,
                // encode it as abstract predicate.
                self.encode_owned_non_aliased(field_ty)?;
            }
            let lifetimes_field_ty: Vec<vir_low::VariableDecl> = field_ty
                .get_lifetimes()
                .iter()
                .map(|x| vir_low::VariableDecl {
                    name: x.name.clone(),
                    ty: ty!(Lifetime),
                })
                .collect();
            let lifetimes_field_ty_expr: Vec<vir_low::Expression> = lifetimes_field_ty
                .clone()
                .iter()
                .cloned()
                .map(|x| x.into())
                .collect();
            field_lifetimes.extend(lifetimes_field_ty.clone());
            let acc = expr! {
                acc(OwnedNonAliased<field_ty>(
                    [field_place], root_address, [field_value]; lifetimes_field_ty_expr
                ))
            };
            field_predicates.push(acc);
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
            OwnedNonAliased<ty>(place: Place, root_address: Address, snapshot: {snapshot_type}, *lifetimes_ty)
            {(
                ([validity]) &&
                ([field_predicates.into_iter().conjoin()])
            )}
        };
        Ok(predicate_decl)
    }

    fn encode_frac_ref(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<()> {
        let ty_without_lifetime = ty.clone().erase_lifetimes();
        if self
            .encoded_frac_borrow_predicates
            .contains(&ty_without_lifetime)
        {
            return Ok(());
        }
        self.encoded_frac_borrow_predicates
            .insert(ty_without_lifetime);
        self.lowerer.encode_compute_address(ty)?;
        use vir_low::macros::*;
        let type_decl = self.lowerer.encoder.get_type_decl_mid(ty)?;
        self.lowerer.encode_snapshot_to_bytes_function(ty)?;
        let snapshot_type = ty.to_snapshot(self.lowerer)?;
        let position = Default::default();
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
            | vir_mid::TypeDecl::Map(_)
            | vir_mid::TypeDecl::Trusted(_)
            | vir_mid::TypeDecl::TypeVar(_) => {
                let mut parameters = vec![place, root_address, snapshot, lifetime];
                let lifetimes_ty: Vec<vir_low::VariableDecl> = ty
                    .get_lifetimes()
                    .iter()
                    .map(|x| vir_low::VariableDecl {
                        name: x.name.clone(),
                        ty: ty!(Lifetime),
                    })
                    .collect();
                parameters.extend(lifetimes_ty);
                vir_low::PredicateDecl::new(predicate_name! {FracRef<ty>}, parameters, None)
            }
            vir_mid::TypeDecl::Tuple(_decl) => unimplemented!(),
            vir_mid::TypeDecl::Struct(vir_mid::type_decl::Struct { fields, .. }) => {
                let mut field_predicates = Vec::new();
                for field in fields {
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
                    let lifetimes_field_ty: Vec<vir_low::VariableDecl> = field_ty
                        .get_lifetimes()
                        .iter()
                        .map(|x| vir_low::VariableDecl {
                            name: x.name.clone(),
                            ty: ty!(Lifetime),
                        })
                        .collect();
                    let lifetimes_field_ty_expr: Vec<vir_low::Expression> = lifetimes_field_ty
                        .clone()
                        .iter()
                        .cloned()
                        .map(|x| x.into())
                        .collect();
                    // NOTE: field_ty may be a mutable reference
                    self.encode_frac_ref(field_ty)?;
                    let acc = expr! {
                        acc(FracRef<field_ty>(
                            [field_place],
                            root_address,
                            [field_snapshot],
                            lifetime;
                            lifetimes_field_ty_expr
                        ))
                    };
                    field_predicates.push(acc);
                }
                if field_predicates.is_empty() {
                    // FIXME: Add backing MemoryBlock unimplemented!();
                }
                let mut arguments = vec![place, root_address, snapshot, lifetime];
                let lifetimes_ty: Vec<vir_low::VariableDecl> = ty
                    .get_lifetimes()
                    .iter()
                    .map(|x| vir_low::VariableDecl {
                        name: x.name.clone(),
                        ty: ty!(Lifetime),
                    })
                    .collect();
                arguments.extend(lifetimes_ty);
                vir_low::PredicateDecl::new(
                    predicate_name! {FracRef<ty>},
                    arguments,
                    Some(expr! {
                        [current_validity] &&
                        [field_predicates.into_iter().conjoin()]
                    }),
                )
            }
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
                    let lifetimes_variant_ty: Vec<vir_low::VariableDecl> = variant_type
                        .get_lifetimes()
                        .iter()
                        .map(|x| vir_low::VariableDecl {
                            name: x.name.clone(),
                            ty: ty!(Lifetime),
                        })
                        .collect();
                    let lifetimes_variant_ty_expr: Vec<vir_low::Expression> = lifetimes_variant_ty
                        .clone()
                        .iter()
                        .cloned()
                        .map(|x| x.into())
                        .collect();
                    // NOTE: variant_type may be a mutable reference
                    self.encode_frac_ref(&variant_type)?;
                    let variant_type = &variant_type;
                    let acc = expr! {
                        ([ discriminant_call.clone() ] == [ discriminant.into() ]) ==>
                        (acc(FracRef<variant_type>(
                            [variant_place], root_address, [variant_snapshot], lifetime; lifetimes_variant_ty_expr
                        )))
                    };
                    variant_predicates.push(acc);
                }
                let discriminant_type = &decl.discriminant_type;
                self.encode_frac_ref(discriminant_type)?;
                let discriminant_field = decl.discriminant_field();
                let discriminant_place = self.lowerer.encode_field_place(
                    ty,
                    &discriminant_field,
                    place.clone().into(),
                    position,
                )?;
                let discriminant_snapshot = self.lowerer.construct_constant_snapshot(
                    discriminant_type,
                    discriminant_call,
                    position,
                )?;
                let lifetimes_discriminant_ty: Vec<vir_low::VariableDecl> = discriminant_type
                    .get_lifetimes()
                    .iter()
                    .map(|x| vir_low::VariableDecl {
                        name: x.name.clone(),
                        ty: ty!(Lifetime),
                    })
                    .collect();
                let lifetimes_discriminant_ty_expr: Vec<vir_low::Expression> =
                    lifetimes_discriminant_ty
                        .iter()
                        .cloned()
                        .map(|x| x.into())
                        .collect();
                let lifetimes_ty: Vec<vir_low::VariableDecl> = ty
                    .get_lifetimes()
                    .iter()
                    .map(|x| vir_low::VariableDecl {
                        name: x.name.clone(),
                        ty: ty!(Lifetime),
                    })
                    .collect();
                let mut arguments = vec![place, root_address.clone(), snapshot, lifetime.clone()];
                arguments.extend(lifetimes_ty);
                vir_low::PredicateDecl::new(
                    predicate_name! {FracRef<ty>},
                    arguments,
                    Some(expr! {
                        [current_validity] &&
                        (acc(FracRef<discriminant_type>(
                            [discriminant_place], root_address,
                            [discriminant_snapshot], lifetime; lifetimes_discriminant_ty_expr
                        ))) &&
                        [variant_predicates.into_iter().conjoin()]
                    }),
                )
            }
            vir_mid::TypeDecl::Union(_decl) => {
                unimplemented!();
            }
            // vir_mid::TypeDecl::Array(Array) => {},
            vir_mid::TypeDecl::Reference(reference) => {
                // NOTE: regardless if the reference is shared or unique, we encode FracRef here
                let target_type = &reference.target_type;
                self.encode_frac_ref(target_type)?;
                let mut parameters = vec![place, root_address, snapshot, lifetime];
                let lifetimes_ty: Vec<vir_low::VariableDecl> = ty
                    .get_lifetimes()
                    .iter()
                    .map(|x| vir_low::VariableDecl {
                        name: x.name.clone(),
                        ty: ty!(Lifetime),
                    })
                    .collect();
                parameters.extend(lifetimes_ty);
                vir_low::PredicateDecl::new(predicate_name! {FracRef<ty>}, parameters, None)
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
        let ty_without_lifetime = ty.clone().erase_lifetimes();
        if self
            .encoded_mut_borrow_predicates
            .contains(&ty_without_lifetime)
        {
            return Ok(());
        }
        self.encoded_mut_borrow_predicates
            .insert(ty_without_lifetime);
        self.lowerer.encode_compute_address(ty)?;
        use vir_low::macros::*;
        let position = Default::default();
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
        let current_validity = self
            .lowerer
            .encode_snapshot_valid_call_for_type(current_snapshot.clone().into(), ty)?;
        let predicate = match &type_decl {
            vir_mid::TypeDecl::Bool
            | vir_mid::TypeDecl::Int(_)
            | vir_mid::TypeDecl::Float(_)
            | vir_mid::TypeDecl::Pointer(_)
            | vir_mid::TypeDecl::Sequence(_)
            | vir_mid::TypeDecl::Map(_)
            | vir_mid::TypeDecl::Trusted(_)
            | vir_mid::TypeDecl::TypeVar(_) => {
                let mut parameters = vec![
                    place,
                    root_address,
                    current_snapshot,
                    final_snapshot,
                    lifetime,
                ];
                let lifetimes_ty: Vec<vir_low::VariableDecl> = ty
                    .get_lifetimes()
                    .iter()
                    .map(|x| vir_low::VariableDecl {
                        name: x.name.clone(),
                        ty: ty!(Lifetime),
                    })
                    .collect();
                parameters.extend(lifetimes_ty);
                vir_low::PredicateDecl::new(predicate_name! {UniqueRef<ty>}, parameters, None)
            }
            vir_mid::TypeDecl::Tuple(_decl) => unimplemented!(),
            vir_mid::TypeDecl::Struct(vir_mid::type_decl::Struct { fields, .. }) => {
                let mut field_predicates = Vec::new();
                let mut field_lifetimes = Vec::new();
                for field in fields {
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
                    let lifetimes_field_ty: Vec<vir_low::VariableDecl> = field_ty
                        .get_lifetimes()
                        .iter()
                        .map(|x| vir_low::VariableDecl {
                            name: x.name.clone(),
                            ty: ty!(Lifetime),
                        })
                        .collect();
                    let lifetimes_field_ty_expr: Vec<vir_low::Expression> = lifetimes_field_ty
                        .clone()
                        .iter()
                        .cloned()
                        .map(|x| x.into())
                        .collect();
                    field_lifetimes.extend(lifetimes_field_ty.clone());
                    if field_ty.is_reference() {
                        let reference = field_ty.clone().unwrap_reference();
                        if reference.uniqueness.is_shared() {
                            self.encode_frac_ref(field_ty)?;
                            let acc = expr! {
                                acc(FracRef<field_ty>(
                                    [field_place],
                                    root_address,
                                    [current_field_snapshot],
                                    lifetime;
                                    lifetimes_field_ty_expr
                                ))
                            };
                            field_predicates.push(acc);
                            continue;
                        }
                    }
                    self.encode_unique_ref(field_ty)?;
                    let acc = expr! {
                        acc(UniqueRef<field_ty>(
                            [field_place],
                            root_address,
                            [current_field_snapshot],
                            [final_field_snapshot],
                            lifetime;
                            lifetimes_field_ty_expr
                        ))
                    };
                    field_predicates.push(acc);
                }
                if field_predicates.is_empty() {
                    // FIXME: add MemoryBlock predicate unimplemented!();
                }
                let mut arguments = vec![
                    place,
                    root_address,
                    current_snapshot,
                    final_snapshot,
                    lifetime,
                ];
                let lifetimes_ty: Vec<vir_low::VariableDecl> = ty
                    .get_lifetimes()
                    .iter()
                    .map(|x| vir_low::VariableDecl {
                        name: x.name.clone(),
                        ty: ty!(Lifetime),
                    })
                    .collect();
                arguments.extend(lifetimes_ty);
                vir_low::PredicateDecl::new(
                    predicate_name! {UniqueRef<ty>},
                    arguments,
                    Some(expr! {
                        [current_validity] &&
                        [field_predicates.into_iter().conjoin()]
                    }),
                )
            }
            vir_mid::TypeDecl::Enum(decl) => {
                let mut variant_predicates = Vec::new();
                let discriminant_current_call = self.lowerer.obtain_enum_discriminant(
                    current_snapshot.clone().into(),
                    ty,
                    position,
                )?;
                let discriminant_final_call = self.lowerer.obtain_enum_discriminant(
                    final_snapshot.clone().into(),
                    ty,
                    position,
                )?;
                for (&discriminant, variant) in decl.discriminant_values.iter().zip(&decl.variants)
                {
                    let variant_index = variant.name.clone().into();
                    let variant_place = self.lowerer.encode_enum_variant_place(
                        ty,
                        &variant_index,
                        place.clone().into(),
                        position,
                    )?;
                    let current_variant_snapshot = self.lowerer.obtain_enum_variant_snapshot(
                        ty,
                        &variant_index,
                        current_snapshot.clone().into(),
                        position,
                    )?;
                    let final_variant_snapshot = self.lowerer.obtain_enum_variant_snapshot(
                        ty,
                        &variant_index,
                        final_snapshot.clone().into(),
                        position,
                    )?;
                    let variant_type = &ty.clone().variant(variant_index);
                    let lifetimes_variant_ty: Vec<vir_low::VariableDecl> = variant_type
                        .get_lifetimes()
                        .iter()
                        .map(|x| vir_low::VariableDecl {
                            name: x.name.clone(),
                            ty: ty!(Lifetime),
                        })
                        .collect();
                    let lifetimes_variant_ty_expr: Vec<vir_low::Expression> = lifetimes_variant_ty
                        .clone()
                        .iter()
                        .cloned()
                        .map(|x| x.into())
                        .collect();
                    if variant_type.is_reference() {
                        let reference = variant_type.clone().unwrap_reference();
                        if reference.uniqueness.is_shared() {
                            self.encode_frac_ref(variant_type)?;
                            let acc = expr! {
                                ([ discriminant_current_call.clone() ] == [ discriminant.into() ]) ==>
                                (acc(FracRef<variant_type>(
                                    [variant_place],
                                    root_address,
                                    [current_variant_snapshot],
                                    lifetime;
                                    lifetimes_variant_ty_expr
                                )))
                            };
                            variant_predicates.push(acc);
                            continue;
                        }
                    }
                    self.encode_unique_ref(variant_type)?;
                    let acc = expr! {
                        ([ discriminant_current_call.clone() ] == [ discriminant.into() ]) ==>
                        (acc(UniqueRef<variant_type>(
                            [variant_place],
                            root_address,
                            [current_variant_snapshot],
                            [final_variant_snapshot],
                            lifetime;
                            lifetimes_variant_ty_expr
                        )))
                    };
                    variant_predicates.push(acc);
                }
                let discriminant_type = &decl.discriminant_type;
                self.encode_unique_ref(discriminant_type)?;
                let discriminant_field = decl.discriminant_field();
                let discriminant_place = self.lowerer.encode_field_place(
                    ty,
                    &discriminant_field,
                    place.clone().into(),
                    position,
                )?;
                let discriminant_current_snapshot = self.lowerer.construct_constant_snapshot(
                    discriminant_type,
                    discriminant_current_call,
                    position,
                )?;
                let discriminant_final_snapshot = self.lowerer.construct_constant_snapshot(
                    discriminant_type,
                    discriminant_final_call,
                    position,
                )?;
                let lifetimes_discriminant_ty: Vec<vir_low::VariableDecl> = discriminant_type
                    .get_lifetimes()
                    .iter()
                    .map(|x| vir_low::VariableDecl {
                        name: x.name.clone(),
                        ty: ty!(Lifetime),
                    })
                    .collect();
                let lifetimes_discriminant_ty_expr: Vec<vir_low::Expression> =
                    lifetimes_discriminant_ty
                        .iter()
                        .cloned()
                        .map(|x| x.into())
                        .collect();
                let lifetimes_ty: Vec<vir_low::VariableDecl> = ty
                    .get_lifetimes()
                    .iter()
                    .map(|x| vir_low::VariableDecl {
                        name: x.name.clone(),
                        ty: ty!(Lifetime),
                    })
                    .collect();
                let mut arguments = vec![
                    place,
                    root_address.clone(),
                    current_snapshot,
                    final_snapshot,
                    lifetime.clone(),
                ];
                arguments.extend(lifetimes_ty);
                vir_low::PredicateDecl::new(
                    predicate_name! {UniqueRef<ty>},
                    arguments,
                    Some(expr! {
                        [current_validity] &&
                        (acc(UniqueRef<discriminant_type>(
                            [discriminant_place],
                            root_address,
                            [discriminant_current_snapshot],
                            [discriminant_final_snapshot],
                            lifetime;
                            lifetimes_discriminant_ty_expr
                        ))) &&
                        [variant_predicates.into_iter().conjoin()]
                    }),
                )
            }
            vir_mid::TypeDecl::Union(_decl) => {
                unimplemented!();
            }
            // vir_mid::TypeDecl::Array(Array) => {},
            vir_mid::TypeDecl::Reference(reference) if reference.uniqueness.is_unique() => {
                let target_type = &reference.target_type;
                self.encode_unique_ref(target_type)?;
                let mut parameters = vec![
                    place,
                    root_address,
                    current_snapshot,
                    final_snapshot,
                    lifetime,
                ];
                let lifetimes_ty: Vec<vir_low::VariableDecl> = ty
                    .get_lifetimes()
                    .iter()
                    .map(|x| vir_low::VariableDecl {
                        name: x.name.clone(),
                        ty: ty!(Lifetime),
                    })
                    .collect();
                parameters.extend(lifetimes_ty);
                vir_low::PredicateDecl::new(predicate_name! {UniqueRef<ty>}, parameters, None)
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
