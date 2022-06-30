use crate::encoder::{
    errors::SpannedEncodingResult,
    high::pure_functions::HighPureFunctionEncoderInterface,
    middle::core_proof::{
        function_gas::FunctionGasInterface,
        lowerer::{DomainsLowererInterface, Lowerer},
        snapshots::{
            IntoPureBoolExpression, IntoPureSnapshot, IntoSnapshot, SnapshotValidityInterface, SnapshotValuesInterface,
        },
        types::TypesInterface,
    },
};
use std::collections::BTreeMap;
use vir_crate::{
    common::expression::{ExpressionIterator, QuantifierHelpers},
    low::{self as vir_low},
    middle as vir_mid,
};
use log::info;
use prusti_common::config;
use crate::encoder::high::types::HighTypeEncoderInterface;


#[derive(Default)]
pub(in super::super) struct FunctionsLowererState {
    functions: BTreeMap<String, vir_low::FunctionDecl>,
}

impl FunctionsLowererState {
    pub fn destruct(self) -> Vec<vir_low::FunctionDecl> {
        self.functions.into_values().collect()
    }
}

trait Private {
    fn caller_function_name(&mut self, function_name: &str) -> String;
    fn ensure_pure_function_lowered(&mut self, function_name: String) -> SpannedEncodingResult<()>;
    fn ensure_all_types_lowered(
        &mut self,
        function_decl: &vir_mid::FunctionDecl,
    ) -> SpannedEncodingResult<()>;
}

impl<'p, 'v: 'p, 'tcx: 'v> Private for Lowerer<'p, 'v, 'tcx> {
    fn caller_function_name(&mut self, function_name: &str) -> String {
        format!("caller_for${}", function_name)
    }
    fn ensure_pure_function_lowered(&mut self, function_name: String) -> SpannedEncodingResult<()> {
        if !self.functions_state.functions.contains_key(&function_name) {
            let function_decl = self.encoder.get_pure_function_decl_mid(&function_name)?;
            self.ensure_all_types_lowered(&function_decl)?;
            let caller_function_name = self.caller_function_name(&function_name);
            let mut pres = function_decl.pres.to_pure_bool_expression(self)?;
            let mut posts = function_decl.posts.to_pure_bool_expression(self)?;
            let mut parameters = function_decl.parameters.to_pure_snapshot(self)?;
            let mut arguments = Vec::new();
            for (parameter, parameter_mid) in parameters.iter().zip(&function_decl.parameters) {
                let argument: vir_low::Expression = parameter.clone().into();
                arguments.push(argument.clone());
                let argument_validity =
                    self.encode_snapshot_valid_call_for_type(argument, &parameter_mid.ty)?;
                pres.push(argument_validity);
            }
            use vir_low::macros::*;
            let return_type = function_decl.return_type.to_snapshot(self)?;
            let mut model_call: vir_low::Expression = true.into();
            let gas_amount2 = self.function_gas_constant(2)?;
            if config::counterexample(){
                //m_PrustiVecWrapperi32ToModel_67bf3082853847e28b9942b97fb78b1a$$model$trusted$m_VecWrapper$I32$$           
                info!("function name: {}", function_name);
                if function_name.contains("ToModel") {
                    info!("to model function");
                    let type_decl = self.encoder.get_type_decl_mid(&function_decl.return_type)?;
                    if let vir_mid::TypeDecl::Struct(vir_mid::type_decl::Struct{name: _, fields}) = type_decl {
                        
                        let call = vir_low::Expression::domain_function_call(
                            "Functions",
                            function_name.clone(),
                            parameters
                                .iter()
                                .map(|parameter| parameter.clone().into())
                                .chain(std::iter::once(gas_amount2))
                                .collect(),
                            return_type.clone(),
                        );
                        for field in fields{
                            let destructor = 
                                self.obtain_struct_field_snapshot(&function_decl.return_type, &field, call.clone(), Default::default())?;
                            //destructors.push(destructor.clone());
                            let const_typ = field.ty.to_snapshot(self)?;//self.encoder.get_type_decl_mid(&field.ty)?;
                            info!("const typ: {:?}", const_typ);
                            
                            let destructor_2 = 
                            self.obtain_constant_value(&field.ty, destructor, Default::default())?;
                            let dummy_function = format!("dummy_model${}", &const_typ);
                            let argument: vir_low::Expression = var! { __result: {vir_low::Type::int()} }.into(); 
                            self.create_domain_func_app(
                                "Functions",
                                dummy_function.clone(),
                                vec![argument],
                                vir_low::Type::Bool,
                                Default::default(),
                            )?;
                            let model_call_2 = vir_low::Expression::domain_function_call(
                                "Functions",
                                dummy_function.clone(),
                                vec![destructor_2.clone()],
                                vir_low::Type::Bool,
                            );
                            model_call = model_call_2
                        }
                    }
                }
            }
            let result: vir_low::Expression = var! { __result: {return_type.clone()} }.into();
            let result_validity = self
                .encode_snapshot_valid_call_for_type(result.clone(), &function_decl.return_type)?;
            posts.push(result_validity);
            let gas_amount = self.function_gas_constant(2)?;
            let function =
                vir_low::FunctionDecl::new(
                    caller_function_name,
                    parameters.clone(),
                    return_type.clone(),
                    pres.clone(),
                    posts.clone(),
                    Some(self.create_domain_func_app(
                        "Functions",
                        function_name.clone(),
                        parameters
                            .iter()
                            .map(|parameter| parameter.clone().into())
                            .chain(std::iter::once(gas_amount))
                            .collect(),
                        return_type.clone(),
                        Default::default(),
                    )?),
                );
            self.functions_state
                .functions
                .insert(function_name.clone(), function);

            // Encode the function body and postconditions if any.
            //
            // TODO: This should be done as a fix-point finalization action that
            // takes into account gas, (potentially mutual) recursion, predicate
            // unfoldings.
            if function_decl.body.is_some() || !posts.is_empty() {
                let gas = self.function_gas_parameter()?;
                parameters.push(gas.clone());
                let mut arguments_without_gas_level = arguments.clone();
                arguments.push(self.add_function_gas_level(gas.clone().into())?);
                arguments_without_gas_level.push(gas.into());
                let call = vir_low::Expression::domain_function_call(
                    "Functions",
                    function_name.clone(),
                    arguments,
                    return_type.clone(),
                );
                let call_without_gas_level = vir_low::Expression::domain_function_call(
                    "Functions",
                    function_name.clone(),
                    arguments_without_gas_level,
                    return_type,
                );
                let body = if let Some(body) = function_decl.body {
                    expr! { ([call.clone()] == [body.to_pure_snapshot(self)?]) }
                } else {
                    true.into()
                };
                let posts_expression = posts.into_iter().conjoin().replace_place(&result, &call);
                let axiom_body = vir_low::Expression::forall(
                    parameters,
                    vec![vir_low::Trigger::new(vec![call.clone()])],
                    expr! {
                        ([pres.into_iter().conjoin()] ==>
                            ([body] && [posts_expression])) &&
                        ([call] == [call_without_gas_level]) &&
                        ([model_call])
                    },
                );
                let axiom = vir_low::DomainAxiomDecl {
                    name: format!("{}$definitional_axiom", function_name),
                    body: axiom_body,
                };
                self.declare_axiom("Functions", axiom)?;
            }
        }
        Ok(())
    }
    fn ensure_all_types_lowered(
        &mut self,
        function_decl: &vir_mid::FunctionDecl,
    ) -> SpannedEncodingResult<()> {
        function_decl.walk_types(|ty| self.ensure_type_definition(ty))
    }
}

pub(in super::super::super) trait FunctionsLowererInterface {
    /// Intended to be called from code contexts such as assertions and assumptions.
    fn call_pure_function_in_procedure_context(
        &mut self,
        function_name: impl ToString,
        arguments: Vec<vir_low::Expression>,
        return_type: vir_low::Type,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::expression::FuncApp>;
    /// Intended to be called from pure contexts such as domain axioms.
    fn call_pure_function_in_pure_context(
        &mut self,
        function_name: impl ToString,
        arguments: Vec<vir_low::Expression>,
        return_type: vir_low::Type,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::expression::DomainFuncApp>;
    fn declare_function(&mut self, function: vir_low::FunctionDecl) -> SpannedEncodingResult<()>;
}

impl<'p, 'v: 'p, 'tcx: 'v> FunctionsLowererInterface for Lowerer<'p, 'v, 'tcx> {
    fn call_pure_function_in_procedure_context(
        &mut self,
        function_name: impl ToString,
        arguments: Vec<vir_low::Expression>,
        return_type: vir_low::Type,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::expression::FuncApp> {
        assert!(
            !return_type.is_ref(),
            "return_type of a pure function cannot be Ref"
        );
        let function_name = function_name.to_string();
        let caller_function_name = self.caller_function_name(&function_name);
        let parameters = self.create_parameters(&arguments);
        self.ensure_pure_function_lowered(function_name)?;
        Ok(vir_low::expression::FuncApp {
            function_name: caller_function_name,
            arguments,
            parameters,
            return_type,
            position,
        })
    }
    fn call_pure_function_in_pure_context(
        &mut self,
        function_name: impl ToString,
        mut arguments: Vec<vir_low::Expression>,
        return_type: vir_low::Type,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::expression::DomainFuncApp> {
        assert!(
            !return_type.is_ref(),
            "return_type of a pure function cannot be Ref"
        );
        let function_name = function_name.to_string();
        let mut parameters = self.create_parameters(&arguments);
        let gas = self.function_gas_parameter()?;
        parameters.push(gas.clone());
        arguments.push(gas.into());
        self.ensure_pure_function_lowered(function_name.clone())?;
        Ok(vir_low::expression::DomainFuncApp {
            domain_name: "Functions".to_string(),
            function_name,
            arguments,
            parameters,
            return_type,
            position,
        })
    }
    /// The function must not be already declared.
    fn declare_function(&mut self, function: vir_low::FunctionDecl) -> SpannedEncodingResult<()> {
        assert!(!self.functions_state.functions.contains_key(&function.name));
        self.functions_state
            .functions
            .insert(function.name.clone(), function);
        Ok(())
    }
}
