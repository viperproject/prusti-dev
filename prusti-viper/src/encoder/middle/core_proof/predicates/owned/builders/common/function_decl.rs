use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        addresses::AddressesInterface,
        arithmetic_wrappers::ArithmeticWrappersInterface,
        footprint::FootprintInterface,
        lifetimes::LifetimesInterface,
        lowerer::Lowerer,
        places::PlacesInterface,
        pointers::PointersInterface,
        snapshots::{
            AssertionToSnapshotConstructor, IntoPureSnapshot, IntoSnapshot, PredicateKind,
            SnapshotValidityInterface, SnapshotValuesInterface,
        },
        type_layouts::TypeLayoutsInterface,
    },
};
use vir_crate::{
    common::{
        expression::{BinaryOperationHelpers, ExpressionIterator, QuantifierHelpers},
        identifier::WithIdentifier,
    },
    low::{self as vir_low},
    middle::{self as vir_mid, operations::ty::Typed},
};

/// A builder for creating snapshot function declarations.
pub(in super::super::super) struct FunctionDeclBuilder<'l, 'p, 'v, 'tcx> {
    pub(in super::super) lowerer: &'l mut Lowerer<'p, 'v, 'tcx>,
    pub(in super::super) function_name: &'l str,
    pub(in super::super) ty: &'l vir_mid::Type,
    pub(in super::super) type_decl: &'l vir_mid::TypeDecl,
    pub(in super::super) parameters: Vec<vir_low::VariableDecl>,
    // pub(in super::super) pres: Vec<vir_low::Expression>,
    /// The predicate for which this function is a snapshot.
    pub(in super::super) predicate: Option<vir_low::ast::expression::PredicateAccessPredicate>,
    /// Postconditions that we can assume always when we have the predicate.
    pub(in super::super) snapshot_posts: Vec<vir_low::Expression>,
    /// Postconditions defining the body of the snapshot that are put inside
    /// `unfolding self.predicate in ...`.
    pub(in super::super) snapshot_body_posts: Vec<vir_low::Expression>,
    // pub(in super::super) conjuncts: Option<Vec<vir_low::Expression>>, FIXME: We have no body.
    pub(in super::super) position: vir_low::Position,
    pub(in super::super) place: vir_low::VariableDecl,
    pub(in super::super) address: vir_low::VariableDecl,
    pub(in super::super) owned_snapshot_functions_to_encode: Vec<vir_mid::Type>,
    pub(in super::super) owned_range_snapshot_functions_to_encode: Vec<vir_mid::Type>,
}

impl<'l, 'p, 'v, 'tcx> FunctionDeclBuilder<'l, 'p, 'v, 'tcx> {
    pub(in super::super::super) fn new(
        lowerer: &'l mut Lowerer<'p, 'v, 'tcx>,
        function_name: &'l str,
        ty: &'l vir_mid::Type,
        type_decl: &'l vir_mid::TypeDecl,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<Self> {
        let place = vir_low::VariableDecl::new("place", lowerer.place_option_type()?);
        let address = vir_low::VariableDecl::new("address", lowerer.address_type()?);
        Ok(Self {
            function_name,
            ty,
            type_decl,
            parameters: Vec::new(),
            predicate: None,
            snapshot_posts: Vec::new(),
            snapshot_body_posts: Vec::new(),
            // pres: Vec::new(),
            // posts: Vec::new(),
            // conjuncts: None,
            position,
            lowerer,
            place,
            address,
            owned_snapshot_functions_to_encode: Vec::new(),
            owned_range_snapshot_functions_to_encode: Vec::new(),
        })
    }

    pub(in super::super::super) fn get_snapshot_postconditions(
        &self,
    ) -> SpannedEncodingResult<Vec<vir_low::Expression>> {
        Ok(self.snapshot_posts.clone())
    }

    pub(in super::super::super) fn get_snapshot_body(
        &self,
    ) -> SpannedEncodingResult<Vec<vir_low::Expression>> {
        Ok(self.snapshot_body_posts.clone())
    }

    pub(in super::super::super) fn build(self) -> SpannedEncodingResult<vir_low::FunctionDecl> {
        let return_type = self.ty.to_snapshot(self.lowerer)?;
        let mut pres = Vec::new();
        let mut posts = self.snapshot_posts;
        if let Some(predicate) = self.predicate {
            for snapshot_body_post in self.snapshot_body_posts {
                posts.push(vir_low::Expression::unfolding(
                    predicate.clone(),
                    snapshot_body_post,
                    self.position,
                ));
            }
            pres.push(vir_low::Expression::PredicateAccessPredicate(predicate));
        } else {
            posts.extend(self.snapshot_body_posts);
        };
        let function = vir_low::FunctionDecl {
            name: format!("{}${}", self.function_name, self.ty.get_identifier()),
            kind: vir_low::FunctionKind::Snap,
            parameters: self.parameters,
            body: None,
            pres,
            // body: self
            //     .conjuncts
            //     .map(|conjuncts| conjuncts.into_iter().conjoin()),
            // pres: self.pres,
            // posts: self.posts,
            posts,
            return_type,
        };
        Ok(function)
    }

    pub(in super::super) fn create_lifetime_parameters(&mut self) -> SpannedEncodingResult<()> {
        self.parameters
            .extend(self.lowerer.create_lifetime_parameters(self.type_decl)?);
        Ok(())
    }

    pub(in super::super) fn create_const_parameters(&mut self) -> SpannedEncodingResult<()> {
        for parameter in self.type_decl.get_const_parameters() {
            self.parameters
                .push(parameter.to_pure_snapshot(self.lowerer)?);
        }
        Ok(())
    }

    pub(in super::super) fn add_precondition(
        &mut self,
        predicate: vir_low::Expression,
    ) -> SpannedEncodingResult<()> {
        // self.pres.push(assertion);
        assert!(
            self.predicate.is_none(),
            "precondition already set: {:?}",
            self.predicate
        );
        let vir_low::Expression::PredicateAccessPredicate(predicate) = predicate else {
            unreachable!("Must be a predicate: {predicate}");
        };
        self.predicate = Some(predicate);
        Ok(())
    }

    pub(in super::super) fn add_snapshot_postcondition(
        &mut self,
        assertion: vir_low::Expression,
    ) -> SpannedEncodingResult<()> {
        self.snapshot_posts.push(assertion);
        Ok(())
    }

    pub(in super::super::super) fn add_snapshot_body_postcondition(
        &mut self,
        assertion: vir_low::Expression,
    ) -> SpannedEncodingResult<()> {
        self.snapshot_body_posts.push(assertion);
        Ok(())
    }

    pub(in super::super) fn array_length_int(
        &mut self,
        array_length_mid: &vir_mid::VariableDecl,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let array_length = array_length_mid.to_pure_snapshot(self.lowerer)?;
        let size_type_mid = self.lowerer.size_type_mid()?;
        self.lowerer
            .obtain_constant_value(&size_type_mid, array_length.into(), self.position)
    }

    pub(in super::super) fn result_type(&mut self) -> SpannedEncodingResult<vir_low::Type> {
        self.ty.to_snapshot(self.lowerer)
    }

    pub(in super::super) fn result(&mut self) -> SpannedEncodingResult<vir_low::VariableDecl> {
        Ok(vir_low::VariableDecl::result_variable(self.result_type()?))
    }

    pub(in super::super) fn add_validity_postcondition(&mut self) -> SpannedEncodingResult<()> {
        let result = self.result()?;
        let validity = self
            .lowerer
            .encode_snapshot_valid_call_for_type(result.into(), self.ty)?;
        self.add_snapshot_postcondition(validity)
    }

    pub(in super::super) fn add_snapshot_len_equal_to_postcondition(
        &mut self,
        array_length_mid: &vir_mid::VariableDecl,
    ) -> SpannedEncodingResult<()> {
        use vir_low::macros::*;
        let snapshot = self.result()?;
        let snapshot_length = self
            .lowerer
            .obtain_array_len_snapshot(snapshot.into(), self.position)?;
        let array_length_int = self.array_length_int(array_length_mid)?;
        let expression = expr! {
            ([array_length_int] == [snapshot_length])
        };
        self.add_snapshot_postcondition(expression)
    }

    pub(in super::super) fn create_field_snap_call(
        &mut self,
        field: &vir_mid::FieldDecl,
        snap_call: impl FnOnce(
            &mut Self,
            &vir_mid::FieldDecl,
            vir_low::Expression,
            vir_low::Expression,
        ) -> SpannedEncodingResult<vir_low::Expression>,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let field_place = self.lowerer.encode_field_place(
            self.ty,
            field,
            self.place.clone().into(),
            self.position,
        )?;
        let field_address = self.lowerer.encode_field_address(
            self.ty,
            field,
            self.address.clone().into(),
            self.position,
        )?;
        snap_call(self, field, field_place, field_address)
        // let target_slice_len = self.slice_len_expression()?;
        // self.lowerer.frac_ref_snap(
        //     CallContext::BuiltinMethod,
        //     &field.ty,
        //     &field.ty,
        //     field_place,
        //     self.root_address.clone().into(),
        //     self.reference_lifetime.clone().into(),
        //     target_slice_len,
        // )
    }

    pub(in super::super) fn create_field_snapshot_equality(
        &mut self,
        field: &vir_mid::FieldDecl,
        snap_call: impl FnOnce(
            &mut Self,
            &vir_mid::FieldDecl,
            vir_low::Expression,
            vir_low::Expression,
        ) -> SpannedEncodingResult<vir_low::Expression>,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        use vir_low::macros::*;
        let result = self.result()?;
        let field_snapshot = self.lowerer.obtain_struct_field_snapshot(
            self.ty,
            field,
            result.into(),
            self.position,
        )?;
        let snap_call = self.create_field_snap_call(field, snap_call)?;
        Ok(expr! {
            [field_snapshot] == [snap_call]
        })
    }

    pub(in super::super::super) fn create_discriminant_snapshot_equality(
        &mut self,
        decl: &vir_mid::type_decl::Enum,
        snap_call: impl FnOnce(
            &mut FunctionDeclBuilder,
            &vir_mid::type_decl::Enum,
            vir_low::Expression,
            vir_low::Expression,
        ) -> SpannedEncodingResult<vir_low::Expression>,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        use vir_low::macros::*;
        let result = self.result()?;
        let discriminant_snapshot =
            self.lowerer
                .obtain_enum_discriminant(result.into(), self.ty, self.position)?;
        let discriminant_field = decl.discriminant_field();
        let discriminant_place = self.lowerer.encode_field_place(
            self.ty,
            &discriminant_field,
            self.place.clone().into(),
            self.position,
        )?;
        let discriminant_address = self.lowerer.encode_field_address(
            self.ty,
            &discriminant_field,
            self.address.clone().into(),
            self.position,
        )?;
        let snap_call = snap_call(self, decl, discriminant_place, discriminant_address)?;
        let snap_call_int = self.lowerer.obtain_constant_value(
            &decl.discriminant_type,
            snap_call,
            self.position,
        )?;
        Ok(expr! {
            [discriminant_snapshot] == [snap_call_int]
        })
    }

    pub(in super::super::super) fn create_variant_snapshot_equality(
        &mut self,
        discriminant_value: vir_mid::DiscriminantValue,
        variant: &vir_mid::type_decl::Struct,
        snap_call: impl FnOnce(
            &mut FunctionDeclBuilder,
            &vir_mid::Type,
            vir_low::Expression,
            vir_low::Expression,
        ) -> SpannedEncodingResult<vir_low::Expression>,
    ) -> SpannedEncodingResult<(vir_low::Expression, vir_low::Expression)> {
        use vir_low::macros::*;
        let result = self.result()?;
        let discriminant_call =
            self.lowerer
                .obtain_enum_discriminant(result.clone().into(), self.ty, self.position)?;
        let guard = expr! {
            [ discriminant_call ] == [ discriminant_value.into() ]
        };
        let variant_index = variant.name.clone().into();
        let variant_place = self.lowerer.encode_enum_variant_place(
            self.ty,
            &variant_index,
            self.place.clone().into(),
            self.position,
        )?;
        let variant_address = self.lowerer.encode_enum_variant_address(
            self.ty,
            &variant_index,
            self.address.clone().into(),
            self.position,
        )?;
        let variant_snapshot = self.lowerer.obtain_enum_variant_snapshot(
            self.ty,
            &variant_index,
            result.into(),
            self.position,
        )?;
        let ty = self.ty.clone();
        let variant_type = ty.variant(variant_index);
        let snap_call = snap_call(self, &variant_type, variant_place, variant_address)?;
        let equality = expr! {
            [variant_snapshot] == [snap_call]
        };
        Ok((guard, equality))
    }

    // pub(in super::super::super) fn add_snapshot_body_postcondition(
    //     &mut self,
    //     precondition_predicate: vir_low::Expression,
    //     body: vir_low::Expression,
    // ) -> SpannedEncodingResult<()> {
    //     let unfolding = precondition_predicate.into_unfolding(body);
    //     self.add_postcondition(unfolding)
    // }

    pub(in super::super::super) fn add_structural_invariant(
        &mut self,
        decl: &vir_mid::type_decl::Struct,
        is_invariant_pure: bool,
        predicate_kind: PredicateKind,
        snap_call: &impl Fn(
            &mut Self,
            &vir_mid::FieldDecl,
            vir_low::Expression,
            vir_low::Expression,
        ) -> SpannedEncodingResult<vir_low::Expression>,
    ) -> SpannedEncodingResult<()> {
        if let Some(invariant) = decl.structural_invariant.clone() {
            let mut regular_field_arguments = Vec::new();
            for field in &decl.fields {
                let field_snap_call = self.create_field_snap_call(field, snap_call)?;
                regular_field_arguments.push(field_snap_call);
                // regular_field_arguments.push(self.create_field_snap_call(field)?);
            }
            let result = self.result()?;
            let (deref_fields, deref_range_fields) = self
                .lowerer
                .structural_invariant_to_deref_fields(&invariant)?;
            for deref_owned in &deref_fields {
                self.owned_snapshot_functions_to_encode
                    .push(deref_owned.place.get_type().clone());
            }
            for deref_range_owned in &deref_range_fields {
                self.owned_range_snapshot_functions_to_encode
                    .push(deref_range_owned.address.get_type().clone());
            }
            let mut constructor_encoder = AssertionToSnapshotConstructor::for_function_body(
                predicate_kind,
                self.ty,
                regular_field_arguments,
                decl.fields.clone(),
                (deref_fields, deref_range_fields),
                self.position,
            );
            let invariant_expression = invariant.into_iter().conjoin();
            let permission_expression = invariant_expression.convert_into_permission_expression();
            let constructor = constructor_encoder
                .expression_to_snapshot_constructor(self.lowerer, &permission_expression)?;
            let body = vir_low::Expression::equals(result.into(), constructor);
            if !is_invariant_pure {
                self.add_snapshot_body_postcondition(body)?;
            } else {
                self.add_snapshot_postcondition(body)?;
            }
        }
        Ok(())
    }

    pub(in super::super) fn range_result_type(&mut self) -> SpannedEncodingResult<vir_low::Type> {
        let vir_mid::Type::Pointer(pointer_type) = self.ty else {
            unreachable!("{} must be a pointer type", self.ty);
        };
        let element_type = pointer_type.target_type.to_snapshot(self.lowerer)?;
        let return_type = vir_low::Type::seq(element_type);
        Ok(return_type)
    }

    pub(in super::super) fn range_result(
        &mut self,
    ) -> SpannedEncodingResult<vir_low::VariableDecl> {
        Ok(vir_low::VariableDecl::result_variable(
            self.range_result_type()?,
        ))
    }

    pub(in super::super) fn create_range_postcondition(
        &mut self,
        posts: &mut Vec<vir_low::Expression>,
        address: &vir_low::VariableDecl,
        start_index: &vir_low::VariableDecl,
        end_index: &vir_low::VariableDecl,
        snap_call_constructor: impl Fn(
            &mut Lowerer,
            &vir_mid::Type,
            vir_low::Expression,
            vir_low::Position,
        ) -> SpannedEncodingResult<vir_low::Expression>,
    ) -> SpannedEncodingResult<()> {
        use vir_low::macros::*;
        let size_type = self.lowerer.size_type_mid()?;
        var_decls! {
            index: Int
        }
        let vir_mid::Type::Pointer(ty) = self.ty else {
            unreachable!()
        };
        let initial_address =
            self.lowerer
                .pointer_address(self.ty, address.clone().into(), self.position)?;
        let vir_mid::Type::Pointer(pointer_type) = self.ty else {
            unreachable!()
        };
        let size = self
            .lowerer
            .encode_type_size_expression2(&pointer_type.target_type, &*pointer_type.target_type)?;
        let start_index = self.lowerer.obtain_constant_value(
            &size_type,
            start_index.clone().into(),
            self.position,
        )?;
        let end_index = self.lowerer.obtain_constant_value(
            &size_type,
            end_index.clone().into(),
            self.position,
        )?;
        let offset_index =
            self.lowerer
                .int_add_call(start_index.clone(), index.clone().into(), self.position)?;
        let element_address =
            self.lowerer
                .address_offset(size, initial_address, offset_index, self.position)?;
        let snap_call = snap_call_constructor(
            self.lowerer,
            &ty.target_type,
            element_address.clone(),
            self.position,
        )?;
        let result_type = self.range_result_type()?;
        let result = self.range_result()?;
        let result_len = vir_low::Expression::container_op(
            vir_low::ContainerOpKind::SeqLen,
            result_type.clone(),
            vec![result.clone().into()],
            self.position,
        );
        let index_diff = vir_low::Expression::subtract(end_index, start_index);
        posts.push(expr!([result_len.clone()] == [index_diff]));
        let element_snap = vir_low::Expression::container_op(
            vir_low::ContainerOpKind::SeqIndex,
            result_type,
            vec![result.into(), index.clone().into()],
            self.position,
        );
        let body = expr!(
            (([0.into()] <= index) && (index < [result_len])) ==>
            ([snap_call] == [element_snap.clone()])
        );
        let expression = vir_low::Expression::forall(
            vec![index],
            vec![
                vir_low::Trigger::new(vec![element_address]),
                vir_low::Trigger::new(vec![element_snap]),
            ],
            body,
        );
        posts.push(expression);
        Ok(())
    }
}
