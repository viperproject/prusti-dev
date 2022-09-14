use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        builtin_methods::CallContext,
        function_gas::FunctionGasInterface,
        lifetimes::LifetimesInterface,
        lowerer::{DomainsLowererInterface, Lowerer},
        places::PlacesInterface,
        predicates::owned::builders::common::function_decl::FunctionDeclBuilder,
        snapshots::{IntoPureSnapshot, IntoSnapshot},
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

use super::function_final_use::UniqueRefFinalSnapCallBuilder;

// FIXME: Code duplication with FracRefRangeSnapFunctionBuilder
pub(in super::super::super) struct UniqueRefFinalRangeSnapFunctionBuilder<'l, 'p, 'v, 'tcx> {
    inner: FunctionDeclBuilder<'l, 'p, 'v, 'tcx>,
    address: vir_low::VariableDecl,
    start_index: vir_low::VariableDecl,
    end_index: vir_low::VariableDecl,
    reference_lifetime: vir_low::VariableDecl,
    slice_len: Option<vir_mid::VariableDecl>,
    posts: Vec<vir_low::Expression>,
}

impl<'l, 'p, 'v, 'tcx> UniqueRefFinalRangeSnapFunctionBuilder<'l, 'p, 'v, 'tcx> {
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
            address: vir_low::VariableDecl::new("address", ty.to_snapshot(lowerer)?),
            start_index: vir_low::VariableDecl::new("start_index", lowerer.size_type()?),
            end_index: vir_low::VariableDecl::new("end_index", lowerer.size_type()?),
            reference_lifetime: vir_low::VariableDecl::new("lifetime", lowerer.lifetime_type()?),
            slice_len,
            inner: FunctionDeclBuilder::new(
                lowerer,
                "snap_unique_ref_final_range_aliased",
                ty,
                type_decl,
                Default::default(),
            )?,
            posts: Default::default(),
        })
    }

    fn gas_amount(&mut self) -> SpannedEncodingResult<vir_low::VariableDecl> {
        self.inner.lowerer.function_gas_parameter()
    }

    pub(in super::super::super) fn build(mut self) -> SpannedEncodingResult<()> {
        use vir_low::macros::*;
        let return_type = self.inner.range_result_type()?;
        let function_name = format!(
            "{}${}",
            self.inner.function_name,
            self.inner.ty.get_identifier()
        );
        let gas = self.gas_amount()?;
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
        let result: vir_low::Expression = var! { __result: {return_type} }.into();
        let posts_expression = self
            .posts
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
        Ok(())
    }

    // pub(in super::super::super) fn build(mut self) -> SpannedEncodingResult<vir_low::FunctionDecl> {
    //     let return_type = self.inner.range_result_type()?;
    //     let function = vir_low::FunctionDecl {
    //         name: format!(
    //             "{}${}",
    //             self.inner.function_name,
    //             self.inner.ty.get_identifier()
    //         ),
    //         kind: vir_low::FunctionKind::SnapRange,
    //         parameters: self.inner.parameters,
    //         body: None,
    //         pres: self.pres,
    //         posts: self.posts,
    //         return_type,
    //     };
    //     Ok(function)
    // }

    pub(in super::super::super) fn create_parameters(&mut self) -> SpannedEncodingResult<()> {
        self.inner.parameters.push(self.address.clone());
        self.inner.parameters.push(self.start_index.clone());
        self.inner.parameters.push(self.end_index.clone());
        self.inner.parameters.push(self.reference_lifetime.clone());
        self.inner.create_lifetime_parameters()?;
        if let Some(slice_len_mid) = &self.slice_len {
            let slice_len = slice_len_mid.to_pure_snapshot(self.inner.lowerer)?;
            self.inner.parameters.push(slice_len);
        }
        self.inner.create_const_parameters()?;
        Ok(())
    }

    pub(in super::super::super) fn add_postcondition(&mut self) -> SpannedEncodingResult<()> {
        let gas = self.gas_amount()?;
        self.inner.create_range_postcondition(
            &mut self.posts,
            &self.address,
            &self.start_index,
            &self.end_index,
            |lowerer, ty, element_address, position| {
                let element_place = lowerer.place_option_none_constructor(position)?;
                let TODO_target_slice_len = None;
                // lowerer.unique_ref_snap(
                //     CallContext::BuiltinMethod,
                //     ty,
                //     ty,
                //     element_place,
                //     element_address.clone(),
                //     self.reference_lifetime.clone().into(),
                //     TODO_target_slice_len,
                //     true,
                //     position,
                // )
                let mut builder = UniqueRefFinalSnapCallBuilder::new(
                    lowerer,
                    CallContext::BuiltinMethod,
                    ty,
                    ty,
                    element_place,
                    element_address,
                    self.reference_lifetime.clone().into(),
                    TODO_target_slice_len,
                    position,
                )?;
                builder.add_lifetime_arguments()?;
                builder.add_const_arguments()?;
                builder.set_gas_amount(gas.clone().into())?;
                builder.build()
            },
        )?;
        Ok(())
    }
}
