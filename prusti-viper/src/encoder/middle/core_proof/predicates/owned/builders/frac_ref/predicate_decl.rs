use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        addresses::AddressesInterface,
        builtin_methods::CallContext,
        lifetimes::LifetimesInterface,
        lowerer::Lowerer,
        places::PlacesInterface,
        predicates::{
            owned::builders::{
                common::predicate_decl::PredicateDeclBuilder, PredicateDeclBuilderMethods,
            },
            PredicatesOwnedInterface,
        },
        snapshots::{
            IntoPureSnapshot, IntoSnapshot, IntoSnapshotLowerer, PredicateKind,
            SelfFramingAssertionToSnapshot, SnapshotValidityInterface, SnapshotValuesInterface,
        },
        type_layouts::TypeLayoutsInterface,
    },
};
use vir_crate::{
    common::expression::{GuardedExpressionIterator, QuantifierHelpers},
    low::{self as vir_low},
    middle as vir_mid,
};

use super::predicate_use::FracRefUseBuilder;

pub(in super::super::super) struct FracRefBuilder<'l, 'p, 'v, 'tcx> {
    inner: PredicateDeclBuilder<'l, 'p, 'v, 'tcx>,
    // place: vir_low::VariableDecl,
    // root_address: vir_low::VariableDecl,
    current_snapshot: vir_low::VariableDecl,
    reference_lifetime: vir_low::VariableDecl,
    slice_len: Option<vir_mid::VariableDecl>,
}

impl<'l, 'p, 'v, 'tcx> PredicateDeclBuilderMethods<'l, 'p, 'v, 'tcx>
    for FracRefBuilder<'l, 'p, 'v, 'tcx>
{
    fn inner(&mut self) -> &mut PredicateDeclBuilder<'l, 'p, 'v, 'tcx> {
        &mut self.inner
    }
}

impl<'l, 'p, 'v, 'tcx> FracRefBuilder<'l, 'p, 'v, 'tcx> {
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
            // place: vir_low::VariableDecl::new("place", lowerer.place_type()?),
            // root_address: vir_low::VariableDecl::new("root_address", lowerer.address_type()?),
            current_snapshot: vir_low::VariableDecl::new(
                "current_snapshot",
                ty.to_snapshot(lowerer)?,
            ),
            reference_lifetime: vir_low::VariableDecl::new(
                "reference_lifetime",
                lowerer.lifetime_type()?,
            ),
            slice_len,
            inner: PredicateDeclBuilder::new(
                lowerer,
                "FracRef2",
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
        self.inner.parameters.push(self.inner.place.clone());
        self.inner.parameters.push(self.inner.root_address.clone());
        // self.inner.parameters.push(self.current_snapshot.clone());
        self.inner.parameters.push(self.reference_lifetime.clone());
        self.inner.create_lifetime_parameters()?;
        if let Some(slice_len_mid) = &self.slice_len {
            let slice_len = slice_len_mid.to_pure_snapshot(self.inner.lowerer)?;
            self.inner.parameters.push(slice_len);
        }
        self.inner.create_const_parameters()?;
        Ok(())
    }

    pub(in super::super::super) fn add_validity(&mut self) -> SpannedEncodingResult<()> {
        self.inner.add_validity(&self.current_snapshot)
    }

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
        let current_field_snapshot = self.inner.lowerer.obtain_struct_field_snapshot(
            self.inner.ty,
            field,
            self.current_snapshot.clone().into(),
            Default::default(),
        )?;
        // let mut builder = FracRefUseBuilder::new(
        //     self.inner.lowerer,
        //     CallContext::BuiltinMethod,
        //     &field.ty,
        //     &field.ty,
        //     field_place,
        //     self.inner.root_address.clone().into(),
        //     // current_field_snapshot,
        //     self.reference_lifetime.clone().into(),
        // )?;
        // builder.add_lifetime_arguments()?;
        // builder.add_const_arguments()?;
        // let expression = builder.build();
        let TODO_target_slice_len = None;
        let expression = self.inner.lowerer.frac_ref_predicate(
            CallContext::BuiltinMethod,
            &field.ty,
            &field.ty,
            field_place,
            self.inner.root_address.clone().into(),
            current_field_snapshot,
            self.reference_lifetime.clone().into(),
            TODO_target_slice_len,
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
        let current_discriminant_call = self.inner.lowerer.obtain_enum_discriminant(
            self.current_snapshot.clone().into(),
            self.inner.ty,
            self.inner.position,
        )?;
        let current_discriminant_snapshot = self.inner.lowerer.construct_constant_snapshot(
            &decl.discriminant_type,
            current_discriminant_call,
            self.inner.position,
        )?;
        // let builder = FracRefUseBuilder::new(
        //     self.inner.lowerer,
        //     CallContext::BuiltinMethod,
        //     &decl.discriminant_type,
        //     &decl.discriminant_type,
        //     discriminant_place,
        //     self.inner.root_address.clone().into(),
        //     // current_discriminant_snapshot,
        //     self.reference_lifetime.clone().into(),
        // )?;
        // let expression = builder.build();
        let expression = self.inner.lowerer.frac_ref_predicate(
            CallContext::BuiltinMethod,
            &decl.discriminant_type,
            &decl.discriminant_type,
            discriminant_place,
            self.inner.root_address.clone().into(),
            current_discriminant_snapshot,
            self.reference_lifetime.clone().into(),
            None,
        )?;
        self.inner.add_conjunct(expression)
    }

    pub(in super::super::super) fn add_frac_ref_target_predicate(
        &mut self,
        target_type: &vir_mid::Type,
        lifetime: &vir_mid::ty::LifetimeConst,
    ) -> SpannedEncodingResult<()> {
        let place = self.inner.place.clone();
        let root_address = self.inner.root_address.clone();
        self.inner.add_frac_ref_target_predicate(
            target_type,
            lifetime,
            place.into(),
            root_address,
            // &self.current_snapshot,
        )
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
            .add_snapshot_len_equal_to(&self.current_snapshot, array_length_mid)?;
        Ok(())
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
        let current_element_snapshot = self.inner.lowerer.obtain_array_element_snapshot(
            self.current_snapshot.clone().into(),
            index_int.clone(),
            self.inner.position,
        )?;
        // let mut builder = FracRefUseBuilder::new(
        //     self.inner.lowerer,
        //     CallContext::BuiltinMethod,
        //     element_type,
        //     element_type,
        //     element_place,
        //     self.inner.root_address.clone().into(),
        //     // current_element_snapshot,
        //     self.reference_lifetime.clone().into(),
        // )?;
        // builder.add_lifetime_arguments()?;
        // builder.add_const_arguments()?;
        // let element_predicate_acc = builder.build();
        let TODO_target_slice_len = None;
        let element_predicate_acc = self.inner.lowerer.frac_ref_predicate(
            CallContext::BuiltinMethod,
            element_type,
            element_type,
            element_place,
            self.inner.root_address.clone().into(),
            current_element_snapshot,
            self.reference_lifetime.clone().into(),
            TODO_target_slice_len,
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
        discriminant_value: vir_mid::DiscriminantValue,
        variant: &vir_mid::type_decl::Struct,
        variant_type: &vir_mid::Type,
    ) -> SpannedEncodingResult<(vir_low::Expression, vir_low::Expression)> {
        use vir_low::macros::*;
        let discriminant_call = self.inner.lowerer.obtain_enum_discriminant(
            self.current_snapshot.clone().into(),
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
            self.inner.place.clone().into(),
            self.inner.position,
        )?;
        let current_variant_snapshot = self.inner.lowerer.obtain_enum_variant_snapshot(
            self.inner.ty,
            &variant_index,
            self.current_snapshot.clone().into(),
            self.inner.position,
        )?;
        // let mut builder = FracRefUseBuilder::new(
        //     self.inner.lowerer,
        //     CallContext::BuiltinMethod,
        //     variant_type,
        //     variant_type,
        //     variant_place,
        //     self.inner.root_address.clone().into(),
        //     // current_variant_snapshot,
        //     self.reference_lifetime.clone().into(),
        // )?;
        // builder.add_lifetime_arguments()?;
        // builder.add_const_arguments()?;
        // let predicate = builder.build();
        let TODO_target_slice_len = None;
        let predicate = self.inner.lowerer.frac_ref_predicate(
            CallContext::BuiltinMethod,
            variant_type,
            variant_type,
            variant_place,
            self.inner.root_address.clone().into(),
            current_variant_snapshot,
            self.reference_lifetime.clone().into(),
            TODO_target_slice_len,
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
        self.inner.add_structural_invariant(
            decl,
            PredicateKind::FracRef {
                lifetime: self.reference_lifetime.clone().into(),
            },
        )
    }

    // pub(in super::super::super) fn add_structural_invariant(
    //     &mut self,
    //     decl: &vir_mid::type_decl::Struct,
    // ) -> SpannedEncodingResult<Vec<vir_mid::Type>> {
    //     if let Some(invariant) = &decl.structural_invariant {
    //         let mut encoder = SelfFramingAssertionToSnapshot::for_predicate_body(
    //             self.inner.place.clone(),
    //             self.inner.root_address.clone(),
    //             PredicateKind::FracRef {
    //                 lifetime: self.reference_lifetime.clone().into(),
    //             },
    //         );
    //         for assertion in invariant {
    //             let low_assertion =
    //                 encoder.expression_to_snapshot(self.inner.lowerer, assertion, true)?;
    //             self.inner.add_conjunct(low_assertion)?;
    //         }
    //         Ok(encoder.into_created_predicate_types())
    //     } else {
    //         Ok(Vec::new())
    //     }
    // }
}
