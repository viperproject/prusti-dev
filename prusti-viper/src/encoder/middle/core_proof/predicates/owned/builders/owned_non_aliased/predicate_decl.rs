use super::predicate_use::OwnedNonAliasedUseBuilder;
use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        addresses::AddressesInterface,
        builtin_methods::CallContext,
        lowerer::Lowerer,
        places::PlacesInterface,
        predicates::{
            owned::builders::{
                common::predicate_decl::PredicateDeclBuilder, PredicateDeclBuilderMethods,
            },
            PredicatesMemoryBlockInterface,
        },
        references::ReferencesInterface,
        snapshots::{
            IntoPureSnapshot, IntoSnapshot, SnapshotBytesInterface, SnapshotValidityInterface,
            SnapshotValuesInterface,
        },
        type_layouts::TypeLayoutsInterface,
    },
};
use vir_crate::{
    common::expression::{GuardedExpressionIterator, QuantifierHelpers},
    low::{self as vir_low},
    middle as vir_mid,
};

pub(in super::super::super) struct OwnedNonAliasedBuilder<'l, 'p, 'v, 'tcx> {
    inner: PredicateDeclBuilder<'l, 'p, 'v, 'tcx>,
    place: vir_low::VariableDecl,
    root_address: vir_low::VariableDecl,
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
        Ok(Self {
            place: vir_low::VariableDecl::new("place", lowerer.place_type()?),
            root_address: vir_low::VariableDecl::new("root_address", lowerer.address_type()?),
            snapshot: vir_low::VariableDecl::new("snapshot", ty.to_snapshot(lowerer)?),
            slice_len,
            inner: PredicateDeclBuilder::new(
                lowerer,
                "OwnedNonAliased",
                ty,
                type_decl,
                Default::default(),
            )?,
        })
    }

    pub(in super::super::super) fn build(self) -> vir_low::PredicateDecl {
        self.inner.build()
    }

    pub(in super::super::super) fn create_parameters(&mut self) -> SpannedEncodingResult<()> {
        self.inner.parameters.push(self.place.clone());
        self.inner.parameters.push(self.root_address.clone());
        self.inner.parameters.push(self.snapshot.clone());
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

    fn compute_address(&self) -> SpannedEncodingResult<vir_low::Expression> {
        use vir_low::macros::*;
        let compute_address = ty!(Address);
        let expression = expr! {
            ComputeAddress::compute_address(
                [self.place.clone().into()],
                [self.root_address.clone().into()]
            )
        };
        Ok(expression)
    }

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
        let compute_address = self.compute_address()?;
        let size_of = self.size_of()?;
        let expression = expr! {
            acc(MemoryBlock([compute_address], [size_of]))
        };
        self.inner.add_conjunct(expression)
    }

    pub(in super::super::super) fn add_padding_memory_block(
        &mut self,
    ) -> SpannedEncodingResult<()> {
        use vir_low::macros::*;
        let compute_address = self.compute_address()?;
        let padding_size = self.padding_size()?;
        let expression = expr! {
            acc(MemoryBlock([compute_address], [padding_size]))
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
            .encode_memory_block_bytes_expression(self.compute_address()?, size_of)?;
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

    pub(in super::super::super) fn add_bytes_address_snapshot_equality(
        &mut self,
    ) -> SpannedEncodingResult<()> {
        let address_type = self.inner.lowerer.reference_address_type(self.inner.ty)?;
        self.inner
            .lowerer
            .encode_snapshot_to_bytes_function(&address_type)?;
        let target_address_snapshot = self.inner.lowerer.reference_address_snapshot(
            self.inner.ty,
            self.snapshot.clone().into(),
            self.inner.position,
        )?;
        self.add_bytes_snapshot_equality_with(&address_type, target_address_snapshot)
    }

    pub(in super::super::super) fn add_field_predicate(
        &mut self,
        field: &vir_mid::FieldDecl,
    ) -> SpannedEncodingResult<()> {
        let field_place = self.inner.lowerer.encode_field_place(
            self.inner.ty,
            field,
            self.place.clone().into(),
            self.inner.position,
        )?;
        let field_snapshot = self.inner.lowerer.obtain_struct_field_snapshot(
            self.inner.ty,
            field,
            self.snapshot.clone().into(),
            Default::default(),
        )?;
        let mut builder = OwnedNonAliasedUseBuilder::new(
            self.inner.lowerer,
            CallContext::BuiltinMethod,
            &field.ty,
            &field.ty,
            field_place,
            self.root_address.clone().into(),
            field_snapshot,
        )?;
        builder.add_lifetime_arguments()?;
        builder.add_const_arguments()?;
        let expression = builder.build();
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
            self.place.clone().into(),
            self.inner.position,
        )?;
        let discriminant_call = self.inner.lowerer.obtain_enum_discriminant(
            self.snapshot.clone().into(),
            self.inner.ty,
            self.inner.position,
        )?;
        let discriminant_snapshot = self.inner.lowerer.construct_constant_snapshot(
            &decl.discriminant_type,
            discriminant_call,
            self.inner.position,
        )?;
        let builder = OwnedNonAliasedUseBuilder::new(
            self.inner.lowerer,
            CallContext::BuiltinMethod,
            &decl.discriminant_type,
            &decl.discriminant_type,
            discriminant_place,
            self.root_address.clone().into(),
            discriminant_snapshot,
        )?;
        let expression = builder.build();
        self.inner.add_conjunct(expression)
    }

    pub(in super::super::super) fn add_unique_ref_target_predicate(
        &mut self,
        target_type: &vir_mid::Type,
        lifetime: &vir_mid::ty::LifetimeConst,
    ) -> SpannedEncodingResult<()> {
        self.inner.add_unique_ref_target_predicate(
            target_type,
            lifetime,
            &self.place,
            &self.snapshot,
        )
    }

    pub(in super::super::super) fn add_frac_ref_target_predicate(
        &mut self,
        target_type: &vir_mid::Type,
        lifetime: &vir_mid::ty::LifetimeConst,
    ) -> SpannedEncodingResult<()> {
        self.inner
            .add_frac_ref_target_predicate(target_type, lifetime, &self.place, &self.snapshot)
    }

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
            self.place.clone().into(),
            index.clone().into(),
            self.inner.position,
        )?;
        let element_snapshot = self.inner.lowerer.obtain_array_element_snapshot(
            self.snapshot.clone().into(),
            index_int.clone(),
            self.inner.position,
        )?;
        let mut builder = OwnedNonAliasedUseBuilder::new(
            self.inner.lowerer,
            CallContext::BuiltinMethod,
            element_type,
            element_type,
            element_place,
            self.root_address.clone().into(),
            element_snapshot,
        )?;
        builder.add_lifetime_arguments()?;
        builder.add_const_arguments()?;
        let element_predicate_acc = builder.build();
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
        discriminant_value: vir_mid::DiscriminantValue,
        variant: &vir_mid::type_decl::Struct,
        variant_type: &vir_mid::Type,
    ) -> SpannedEncodingResult<(vir_low::Expression, vir_low::Expression)> {
        use vir_low::macros::*;
        let discriminant_call = self.inner.lowerer.obtain_enum_discriminant(
            self.snapshot.clone().into(),
            self.inner.ty,
            self.inner.position,
        )?;
        let guard = expr! {
            [ discriminant_call ] == [ discriminant_value.into() ]
        };
        let variant_index = variant.name.clone().into();
        let variant_place = self.inner.lowerer.encode_enum_variant_place(
            self.inner.ty,
            &variant_index,
            self.place.clone().into(),
            self.inner.position,
        )?;
        let variant_snapshot = self.inner.lowerer.obtain_enum_variant_snapshot(
            self.inner.ty,
            &variant_index,
            self.snapshot.clone().into(),
            self.inner.position,
        )?;
        let mut builder = OwnedNonAliasedUseBuilder::new(
            self.inner.lowerer,
            CallContext::BuiltinMethod,
            variant_type,
            variant_type,
            variant_place,
            self.root_address.clone().into(),
            variant_snapshot,
        )?;
        builder.add_lifetime_arguments()?;
        builder.add_const_arguments()?;
        let predicate = builder.build();
        Ok((guard, predicate))
    }

    pub(in super::super::super) fn add_variant_predicates(
        &mut self,
        variant_predicates: Vec<(vir_low::Expression, vir_low::Expression)>,
    ) -> SpannedEncodingResult<()> {
        self.inner
            .add_conjunct(variant_predicates.into_iter().create_match())
    }
}
