use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        addresses::AddressesInterface,
        builtin_methods::CallContext,
        footprint::FootprintInterface,
        lifetimes::LifetimesInterface,
        lowerer::Lowerer,
        places::PlacesInterface,
        predicates::{
            owned::builders::common::function_decl::FunctionDeclBuilder, PredicatesOwnedInterface,
        },
        snapshots::{
            AssertionToSnapshotConstructor, IntoPureSnapshot, PredicateKind,
            SnapshotValuesInterface,
        },
        type_layouts::TypeLayoutsInterface,
    },
};

use vir_crate::{
    common::{
        expression::{BinaryOperationHelpers, ExpressionIterator},
        identifier::WithIdentifier,
    },
    low::{self as vir_low},
    middle::{
        self as vir_mid,
        operations::{const_generics::WithConstArguments, lifetimes::WithLifetimes},
    },
};

use super::predicate_use::FracRefUseBuilder;

pub(in super::super::super) struct FracRefSnapFunctionBuilder<'l, 'p, 'v, 'tcx> {
    inner: FunctionDeclBuilder<'l, 'p, 'v, 'tcx>,
    // place: vir_low::VariableDecl,
    root_address: vir_low::VariableDecl,
    reference_lifetime: vir_low::VariableDecl,
    slice_len: Option<vir_mid::VariableDecl>,
}

impl<'l, 'p, 'v, 'tcx> FracRefSnapFunctionBuilder<'l, 'p, 'v, 'tcx> {
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
            root_address: vir_low::VariableDecl::new("root_address", lowerer.address_type()?),
            reference_lifetime: vir_low::VariableDecl::new(
                "reference_lifetime",
                lowerer.lifetime_type()?,
            ),
            slice_len,
            inner: FunctionDeclBuilder::new(
                lowerer,
                "snap_current_frac_ref",
                ty,
                type_decl,
                Default::default(),
            )?,
        })
    }

    pub(in super::super::super) fn create_parameters(&mut self) -> SpannedEncodingResult<()> {
        self.inner.parameters.push(self.inner.place.clone());
        self.inner.parameters.push(self.root_address.clone());
        self.inner.parameters.push(self.reference_lifetime.clone());
        self.inner.create_lifetime_parameters()?;
        if let Some(slice_len) = self.slice_len()? {
            self.inner.parameters.push(slice_len);
        }
        self.inner.create_const_parameters()?;
        Ok(())
    }

    pub(in super::super::super) fn add_frac_ref_precondition(
        &mut self,
    ) -> SpannedEncodingResult<()> {
        let predicate = self.precondition_predicate()?;
        self.inner.add_precondition(predicate)
    }

    // FIXME: Code duplication.
    fn slice_len(&mut self) -> SpannedEncodingResult<Option<vir_low::VariableDecl>> {
        self.slice_len
            .as_ref()
            .map(|slice_len_mid| slice_len_mid.to_pure_snapshot(self.inner.lowerer))
            .transpose()
    }

    // FIXME: Code duplication.
    fn slice_len_expression(&mut self) -> SpannedEncodingResult<Option<vir_low::Expression>> {
        Ok(self.slice_len()?.map(|slice_len| slice_len.into()))
    }

    fn precondition_predicate(&mut self) -> SpannedEncodingResult<vir_low::Expression> {
        self.frac_ref_predicate(
            self.inner.ty,
            self.inner.type_decl,
            self.inner.place.clone().into(),
            self.root_address.clone().into(),
            self.reference_lifetime.clone().into(),
        )
    }

    fn frac_ref_predicate<G>(
        &mut self,
        ty: &vir_mid::Type,
        generics: &G,
        place: vir_low::Expression,
        root_address: vir_low::Expression,
        reference_lifetime: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments,
    {
        // let slice_len = if let Some(slice_len_mid) = &self.slice_len {
        //     let slice_len = slice_len_mid.to_pure_snapshot(self.inner.lowerer)?;
        //     Some(slice_len.into())
        // } else {
        //     None
        // };
        let mut builder = FracRefUseBuilder::new(
            self.inner.lowerer,
            CallContext::BuiltinMethod,
            ty,
            generics,
            place,
            root_address,
            reference_lifetime,
            // slice_len,
        )?;
        builder.add_lifetime_arguments()?;
        builder.add_const_arguments()?;
        builder.build()
    }

    pub(in super::super::super) fn build(self) -> SpannedEncodingResult<vir_low::FunctionDecl> {
        self.inner.build()
    }

    // // FIXME: Code duplication.
    // fn create_field_snap_call(
    //     &mut self,
    //     field: &vir_mid::FieldDecl,
    // ) -> SpannedEncodingResult<vir_low::Expression> {
    //     let field_place = self.inner.lowerer.encode_field_place(
    //         self.inner.ty,
    //         field,
    //         self.inner.place.clone().into(),
    //         self.inner.position,
    //     )?;
    //     let target_slice_len = self.slice_len_expression()?;
    //     self.inner.lowerer.frac_ref_snap(
    //         CallContext::BuiltinMethod,
    //         &field.ty,
    //         &field.ty,
    //         field_place,
    //         self.root_address.clone().into(),
    //         self.reference_lifetime.clone().into(),
    //         target_slice_len,
    //     )
    // }

    // FIXME: Code duplication.
    pub(in super::super::super) fn create_field_snapshot_equality(
        &mut self,
        field: &vir_mid::FieldDecl,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        // use vir_low::macros::*;
        // let result = self.inner.result()?;
        // let field_snapshot = self.inner.lowerer.obtain_struct_field_snapshot(
        //     self.inner.ty,
        //     field,
        //     result.into(),
        //     self.inner.position,
        // )?;
        // let snap_call = self.create_field_snap_call(&field)?;
        // Ok(expr! {
        //     [field_snapshot] == [snap_call]
        // })
        // self.inner.create_field_snap_call(field, |builder, field, field_place| {
        //             let target_slice_len = self.slice_len_expression()?;
        // self.inner.lowerer.frac_ref_snap(
        //     CallContext::BuiltinMethod,
        //     &field.ty,
        //     &field.ty,
        //     field_place,
        //     self.root_address.clone().into(),
        //     self.reference_lifetime.clone().into(),
        //     target_slice_len,
        // )
        // })
        let frac_ref_call = self.field_frac_ref_snap()?;
        self.inner
            .create_field_snapshot_equality(field, frac_ref_call)
    }

    fn field_frac_ref_snap(
        &mut self,
    ) -> SpannedEncodingResult<
        impl Fn(
            &mut FunctionDeclBuilder,
            &vir_mid::FieldDecl,
            vir_low::Expression,
        ) -> SpannedEncodingResult<vir_low::Expression>,
    > {
        let target_slice_len = self.slice_len_expression()?;
        let root_address: vir_low::Expression = self.root_address.clone().into();
        let root_address = std::rc::Rc::new(root_address);
        let lifetime: vir_low::Expression = self.reference_lifetime.clone().into();
        let lifetime = std::rc::Rc::new(lifetime);
        Ok(
            move |builder: &mut FunctionDeclBuilder, field: &vir_mid::FieldDecl, field_place| {
                builder.lowerer.frac_ref_snap(
                    CallContext::BuiltinMethod,
                    &field.ty,
                    &field.ty,
                    field_place,
                    (*root_address).clone(),
                    (*lifetime).clone(),
                    target_slice_len.clone(),
                )
            },
        )
    }

    // FIXME: Code duplication.
    pub(in super::super::super) fn add_unfolding_postcondition(
        &mut self,
        body: vir_low::Expression,
    ) -> SpannedEncodingResult<()> {
        let predicate = self.precondition_predicate()?;
        let unfolding = predicate.into_unfolding(body);
        self.inner.add_postcondition(unfolding)
    }

    pub(in super::super::super) fn add_structural_invariant(
        &mut self,
        decl: &vir_mid::type_decl::Struct,
    ) -> SpannedEncodingResult<()> {
        let precondition_predicate = self.precondition_predicate()?;
        let predicate_kind = PredicateKind::FracRef {
            lifetime: self.reference_lifetime.clone().into(),
        };
        let snap_call = self.field_frac_ref_snap()?;
        self.inner.add_structural_invariant(
            decl,
            Some(precondition_predicate),
            predicate_kind,
            &snap_call,
        )
    }

    // // FIXME: Code duplication.
    // pub(in super::super::super) fn add_structural_invariant2(
    //     &mut self,
    //     decl: &vir_mid::type_decl::Struct,
    // ) -> SpannedEncodingResult<()> {
    //     if let Some(invariant) = decl.structural_invariant.clone() {
    //         let mut regular_field_arguments = Vec::new();
    //         for field in &decl.fields {
    //             let frac_ref_call = self.field_frac_ref_snap()?;
    //             let snap_call = self.inner.create_field_snap_call(field, frac_ref_call)?;
    //             regular_field_arguments.push(snap_call);
    //             // regular_field_arguments.push(self.create_field_snap_call(field)?);
    //         }
    //         let result = self.inner.result()?;
    //         let deref_fields = self
    //             .inner
    //             .lowerer
    //             .structural_invariant_to_deref_fields(&invariant)?;
    //         let mut constructor_encoder = AssertionToSnapshotConstructor::for_function_body(
    //             PredicateKind::FracRef {
    //                 lifetime: self.reference_lifetime.clone().into(),
    //             },
    //             self.inner.ty,
    //             regular_field_arguments,
    //             decl.fields.clone(),
    //             deref_fields,
    //             self.inner.position,
    //         );
    //         let invariant_expression = invariant.into_iter().conjoin();
    //         let permission_expression = invariant_expression.convert_into_permission_expression();
    //         let constructor = constructor_encoder
    //             .expression_to_snapshot_constructor(self.inner.lowerer, &permission_expression)?;
    //         self.add_unfolding_postcondition(vir_low::Expression::equals(
    //             result.into(),
    //             constructor,
    //         ))?;
    //     }
    //     Ok(())
    // }
}
