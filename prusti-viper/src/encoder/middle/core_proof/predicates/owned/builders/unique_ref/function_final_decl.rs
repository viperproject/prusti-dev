use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        addresses::AddressesInterface,
        builtin_methods::CallContext,
        function_gas::FunctionGasInterface,
        lifetimes::LifetimesInterface,
        lowerer::{DomainsLowererInterface, Lowerer},
        predicates::{
            owned::builders::common::function_decl::FunctionDeclBuilder, PredicatesOwnedInterface,
        },
        snapshots::{IntoPureSnapshot, IntoSnapshot, PredicateKind},
        type_layouts::TypeLayoutsInterface,
    },
};
use vir_crate::{
    common::{
        expression::{ExpressionIterator, QuantifierHelpers},
        identifier::WithIdentifier,
    },
    low::{self as vir_low},
    middle::{self as vir_mid},
};

pub(in super::super::super) struct UniqueRefFinalSnapFunctionBuilder<'l, 'p, 'v, 'tcx> {
    inner: FunctionDeclBuilder<'l, 'p, 'v, 'tcx>,
    // place: vir_low::VariableDecl,
    address: vir_low::VariableDecl,
    reference_lifetime: vir_low::VariableDecl,
    slice_len: Option<vir_mid::VariableDecl>,
}

impl<'l, 'p, 'v, 'tcx> UniqueRefFinalSnapFunctionBuilder<'l, 'p, 'v, 'tcx> {
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
        let function_name = "snap_final_unique_ref";
        Ok(Self {
            address: vir_low::VariableDecl::new("address", lowerer.address_type()?),
            reference_lifetime: vir_low::VariableDecl::new(
                "reference_lifetime",
                lowerer.lifetime_type()?,
            ),
            slice_len,
            inner: FunctionDeclBuilder::new(
                lowerer,
                function_name,
                ty,
                type_decl,
                Default::default(),
            )?,
        })
    }

    pub(in super::super::super) fn get_snapshot_postconditions(
        &self,
    ) -> SpannedEncodingResult<Vec<vir_low::Expression>> {
        self.inner.get_snapshot_postconditions()
    }

    pub(in super::super::super) fn get_snapshot_body(
        &self,
    ) -> SpannedEncodingResult<Vec<vir_low::Expression>> {
        let body = self.inner.get_snapshot_body()?;
        assert_eq!(body.len(), 0);
        Ok(body)
    }

    pub(in super::super::super) fn build(self) -> SpannedEncodingResult<(String, vir_low::Type)> {
        use vir_low::macros::*;
        let return_type = self.inner.ty.to_snapshot(self.inner.lowerer)?;
        let function_name = format!(
            "{}${}",
            self.inner.function_name,
            self.inner.ty.get_identifier()
        );
        let gas = self.inner.lowerer.function_gas_parameter()?;
        let parameters = {
            let mut parameters = self.inner.parameters.clone();
            parameters.push(gas.clone());
            parameters
        };
        let mut arguments_succ_gas: Vec<_> = self
            .inner
            .parameters
            .into_iter()
            .map(|parameter| parameter.into())
            .collect();
        let mut arguments_gas = arguments_succ_gas.clone();
        arguments_succ_gas.push(
            self.inner
                .lowerer
                .add_function_gas_level(gas.clone().into())?,
        );
        arguments_gas.push(gas.into());
        let call_succ_gas = self.inner.lowerer.create_domain_func_app(
            "UniqueRefSnapFunctions",
            function_name.clone(),
            arguments_succ_gas,
            return_type.clone(),
            Default::default(),
        )?;
        let call_gas = vir_low::Expression::domain_function_call(
            "UniqueRefSnapFunctions",
            function_name.clone(),
            arguments_gas,
            return_type.clone(),
        );
        assert_eq!(self.inner.snapshot_body_posts.len(), 0);
        let result: vir_low::Expression = var! { __result: {return_type.clone()} }.into();
        let posts_expression = self
            .inner
            .snapshot_posts
            .into_iter()
            .conjoin()
            .replace_place(&result, &call_succ_gas);
        let axiom_body = vir_low::Expression::forall(
            parameters,
            vec![vir_low::Trigger::new(vec![call_succ_gas.clone()])],
            expr! {
                [posts_expression] && ([call_succ_gas] == [call_gas])
            },
        );
        let axiom = vir_low::DomainAxiomDecl {
            comment: None,
            name: format!("{function_name}$definitional_axiom"),
            body: axiom_body,
        };
        self.inner
            .lowerer
            .declare_axiom("UniqueRefSnapFunctions", axiom)?;
        Ok((function_name, return_type))
    }

    pub(in super::super::super) fn create_parameters(&mut self) -> SpannedEncodingResult<()> {
        self.inner.parameters.push(self.inner.place.clone());
        self.inner.parameters.push(self.address.clone());
        self.inner.parameters.push(self.reference_lifetime.clone());
        self.inner.create_lifetime_parameters()?;
        if let Some(slice_len_mid) = &self.slice_len {
            let slice_len = slice_len_mid.to_pure_snapshot(self.inner.lowerer)?;
            self.inner.parameters.push(slice_len);
        }
        self.inner.create_const_parameters()?;
        Ok(())
    }

    pub(in super::super::super) fn add_snapshot_postcondition(
        &mut self,
        expression: vir_low::Expression,
    ) -> SpannedEncodingResult<()> {
        self.inner.add_snapshot_postcondition(expression)
    }

    pub(in super::super::super) fn add_structural_invariant(
        &mut self,
        decl: &vir_mid::type_decl::Struct,
    ) -> SpannedEncodingResult<()> {
        let predicate_kind = PredicateKind::UniqueRef {
            lifetime: self.reference_lifetime.clone().into(),
            is_final: true,
        };
        let snap_call = self.field_unique_ref_snap()?;
        self.inner
            .add_structural_invariant(decl, true, predicate_kind, &snap_call)
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

    pub(in super::super::super) fn create_field_snapshot_equality(
        &mut self,
        field: &vir_mid::FieldDecl,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let unique_ref_call = self.field_unique_ref_snap()?;
        self.inner
            .create_field_snapshot_equality(field, unique_ref_call)
    }

    fn field_unique_ref_snap(
        &mut self,
    ) -> SpannedEncodingResult<
        impl Fn(
            &mut FunctionDeclBuilder,
            &vir_mid::FieldDecl,
            vir_low::Expression,
            vir_low::Expression,
        ) -> SpannedEncodingResult<vir_low::Expression>,
    > {
        let target_slice_len = self.slice_len_expression()?;
        let lifetime: vir_low::Expression = self.reference_lifetime.clone().into();
        let lifetime = std::rc::Rc::new(lifetime);
        let is_final = true; // FIXME: Unused field.
        Ok(
            move |builder: &mut FunctionDeclBuilder,
                  field: &vir_mid::FieldDecl,
                  field_place,
                  field_address| {
                builder.lowerer.unique_ref_snap(
                    CallContext::BuiltinMethod,
                    &field.ty,
                    &field.ty,
                    field_place,
                    field_address,
                    (*lifetime).clone(),
                    target_slice_len.clone(),
                    is_final,
                    builder.position,
                )
            },
        )
    }

    pub(in super::super::super) fn create_discriminant_snapshot_equality(
        &mut self,
        decl: &vir_mid::type_decl::Enum,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let call = self.discriminant_unique_ref_snap()?;
        self.inner.create_discriminant_snapshot_equality(decl, call)
    }

    fn discriminant_unique_ref_snap(
        &mut self,
    ) -> SpannedEncodingResult<
        impl Fn(
            &mut FunctionDeclBuilder,
            &vir_mid::type_decl::Enum,
            vir_low::Expression,
            vir_low::Expression,
        ) -> SpannedEncodingResult<vir_low::Expression>,
    > {
        let target_slice_len = self.slice_len_expression()?;
        let lifetime: vir_low::Expression = self.reference_lifetime.clone().into();
        let lifetime = std::rc::Rc::new(lifetime);
        Ok(
            move |builder: &mut FunctionDeclBuilder,
                  decl: &vir_mid::type_decl::Enum,
                  discriminant_place,
                  discriminant_address| {
                builder.lowerer.unique_ref_snap(
                    CallContext::BuiltinMethod,
                    &decl.discriminant_type,
                    &decl.discriminant_type,
                    discriminant_place,
                    discriminant_address,
                    (*lifetime).clone(),
                    target_slice_len.clone(),
                    true,
                    builder.position,
                )
            },
        )
    }

    pub(in super::super::super) fn create_variant_snapshot_equality(
        &mut self,
        discriminant_value: vir_mid::DiscriminantValue,
        variant: &vir_mid::type_decl::Struct,
    ) -> SpannedEncodingResult<(vir_low::Expression, vir_low::Expression)> {
        let call = self.variant_unique_ref_snap()?;
        self.inner
            .create_variant_snapshot_equality(discriminant_value, variant, call)
    }

    fn variant_unique_ref_snap(
        &mut self,
    ) -> SpannedEncodingResult<
        impl Fn(
            &mut FunctionDeclBuilder,
            &vir_mid::Type,
            vir_low::Expression,
            vir_low::Expression,
        ) -> SpannedEncodingResult<vir_low::Expression>,
    > {
        let target_slice_len = self.slice_len_expression()?;
        let lifetime: vir_low::Expression = self.reference_lifetime.clone().into();
        let lifetime = std::rc::Rc::new(lifetime);
        Ok(
            move |builder: &mut FunctionDeclBuilder,
                  variant_type: &vir_mid::Type,
                  variant_place,
                  variant_address| {
                builder.lowerer.unique_ref_snap(
                    CallContext::BuiltinMethod,
                    variant_type,
                    // Enum variant and enum have the same set of lifetime parameters,
                    // so we use type_decl here. We cannot use `variant_type` because
                    // `ty` is normalized.
                    builder.type_decl,
                    variant_place,
                    variant_address,
                    (*lifetime).clone(),
                    target_slice_len.clone(),
                    true,
                    builder.position,
                )
            },
        )
    }
}
