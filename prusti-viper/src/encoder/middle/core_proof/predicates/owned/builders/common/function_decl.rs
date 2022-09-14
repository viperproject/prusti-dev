use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        footprint::FootprintInterface,
        lifetimes::LifetimesInterface,
        lowerer::Lowerer,
        places::PlacesInterface,
        snapshots::{
            AssertionToSnapshotConstructor, IntoPureSnapshot, IntoSnapshot, PredicateKind,
            SnapshotValidityInterface, SnapshotValuesInterface,
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
    middle as vir_mid,
};

pub(in super::super::super) struct FunctionDeclBuilder<'l, 'p, 'v, 'tcx> {
    pub(in super::super) lowerer: &'l mut Lowerer<'p, 'v, 'tcx>,
    pub(in super::super) function_name: &'l str,
    pub(in super::super) ty: &'l vir_mid::Type,
    pub(in super::super) type_decl: &'l vir_mid::TypeDecl,
    pub(in super::super) parameters: Vec<vir_low::VariableDecl>,
    pub(in super::super) pres: Vec<vir_low::Expression>,
    pub(in super::super) posts: Vec<vir_low::Expression>,
    pub(in super::super) conjuncts: Option<Vec<vir_low::Expression>>,
    pub(in super::super) position: vir_low::Position,
    pub(in super::super) place: vir_low::VariableDecl,
}

impl<'l, 'p, 'v, 'tcx> FunctionDeclBuilder<'l, 'p, 'v, 'tcx> {
    pub(in super::super::super) fn new(
        lowerer: &'l mut Lowerer<'p, 'v, 'tcx>,
        function_name: &'l str,
        ty: &'l vir_mid::Type,
        type_decl: &'l vir_mid::TypeDecl,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<Self> {
        let place = vir_low::VariableDecl::new("place", lowerer.place_type()?);
        Ok(Self {
            function_name,
            ty,
            type_decl,
            parameters: Vec::new(),
            pres: Vec::new(),
            posts: Vec::new(),
            conjuncts: None,
            position,
            lowerer,
            place,
        })
    }

    pub(in super::super::super) fn build(self) -> SpannedEncodingResult<vir_low::FunctionDecl> {
        let return_type = self.ty.to_snapshot(self.lowerer)?;
        let function = vir_low::FunctionDecl {
            name: format!("{}${}", self.function_name, self.ty.get_identifier()),
            kind: vir_low::FunctionKind::Snap,
            parameters: self.parameters,
            body: self
                .conjuncts
                .map(|conjuncts| conjuncts.into_iter().conjoin()),
            pres: self.pres,
            posts: self.posts,
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
        assertion: vir_low::Expression,
    ) -> SpannedEncodingResult<()> {
        self.pres.push(assertion);
        Ok(())
    }

    pub(in super::super) fn add_postcondition(
        &mut self,
        assertion: vir_low::Expression,
    ) -> SpannedEncodingResult<()> {
        self.posts.push(assertion);
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
        Ok(vir_low::VariableDecl::new("__result", self.result_type()?))
    }

    pub(in super::super) fn add_validity_postcondition(&mut self) -> SpannedEncodingResult<()> {
        let result = self.result()?;
        let validity = self
            .lowerer
            .encode_snapshot_valid_call_for_type(result.into(), self.ty)?;
        self.add_postcondition(validity)
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
        self.add_postcondition(expression)
    }

    pub(in super::super) fn create_field_snap_call(
        &mut self,
        field: &vir_mid::FieldDecl,
        snap_call: impl FnOnce(
            &mut Self,
            &vir_mid::FieldDecl,
            vir_low::Expression,
        ) -> SpannedEncodingResult<vir_low::Expression>,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let field_place = self.lowerer.encode_field_place(
            self.ty,
            field,
            self.place.clone().into(),
            self.position,
        )?;
        snap_call(self, field, field_place.into())
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
        let snap_call = self.create_field_snap_call(&field, snap_call)?;
        Ok(expr! {
            [field_snapshot] == [snap_call]
        })
    }

    pub(in super::super::super) fn add_unfolding_postcondition(
        &mut self,
        precondition_predicate: vir_low::Expression,
        body: vir_low::Expression,
    ) -> SpannedEncodingResult<()> {
        let unfolding = precondition_predicate.into_unfolding(body);
        self.add_postcondition(unfolding)
    }

    pub(in super::super::super) fn add_structural_invariant(
        &mut self,
        decl: &vir_mid::type_decl::Struct,
        precondition_predicate: Option<vir_low::Expression>,
        predicate_kind: PredicateKind,
        snap_call: &impl Fn(
            &mut Self,
            &vir_mid::FieldDecl,
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
            let deref_fields = self
                .lowerer
                .structural_invariant_to_deref_fields(&invariant)?;
            let mut constructor_encoder = AssertionToSnapshotConstructor::for_function_body(
                predicate_kind,
                self.ty,
                regular_field_arguments,
                decl.fields.clone(),
                deref_fields,
                self.position,
            );
            let invariant_expression = invariant.into_iter().conjoin();
            let permission_expression = invariant_expression.convert_into_permission_expression();
            let constructor = constructor_encoder
                .expression_to_snapshot_constructor(self.lowerer, &permission_expression)?;
            let body = vir_low::Expression::equals(result.into(), constructor);
            if let Some(precondition_predicate) = precondition_predicate {
                self.add_unfolding_postcondition(precondition_predicate, body)?;
            } else {
                self.add_postcondition(body)?;
            }
        }
        Ok(())
    }
}
