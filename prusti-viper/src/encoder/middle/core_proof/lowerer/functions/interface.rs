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
    //fn unroll_model(&mut self, typ: vir_mid::Type, expr: vir_low::Expression, bound: usize) -> SpannedEncodingResult<vir_low::Expression>;
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
            /*let mut destructor_calls: Vec<vir_low::Expression> = vec![];
            if config::counterexample(){
                let gas = self.function_gas_parameter()?;
                let gas_expression = gas.clone().into();
                if function_name.contains("ToModel") {
                    let type_decl = self.encoder.get_type_decl_mid(&function_decl.return_type)?;
                    let function_call = vir_low::Expression::domain_function_call(
                        "Functions",
                        function_name.clone(),
                        parameters
                            .iter()
                            .map(|parameter| parameter.clone().into())
                            .chain(std::iter::once(gas_expression))
                            .collect(),
                        return_type.clone(),
                    );
                    if let vir_mid::TypeDecl::Struct(vir_mid::type_decl::Struct{name: _, fields}) = type_decl {
                        for field in fields{
                            let field_snapshot = self.obtain_struct_field_snapshot(&function_decl.return_type, &field, function_call.clone(), Default::default())?;
                            destructor_calls.push(self.unroll_model(field.ty.clone(), field_snapshot.clone(), config::unroll_model())?);                    
                        }
                    }
                }
            }*/
            let result: vir_low::Expression = var! { __result: {return_type.clone()} }.into();
            let result_validity = self
                .encode_snapshot_valid_call_for_type(result.clone(), &function_decl.return_type)?;
            posts.push(result_validity);
            let gas = self.function_gas_parameter()?;
            let gas_expression = gas.clone().into();
            let gas_amount = self.function_gas_constant(2)?;
            let caller_for_pres: Vec<_> = pres
                .clone()
                .into_iter()
                .map(|expression| expression.replace_place(&gas_expression, &gas_amount))
                .collect();
            let caller_for_posts: Vec<_> = posts
                .clone()
                .into_iter()
                .map(|expression| expression.replace_place(&gas_expression, &gas_amount))
                .collect();
            let function = vir_low::FunctionDecl::new(
                caller_function_name,
                parameters.clone(),
                return_type.clone(),
                caller_for_pres,
                caller_for_posts,
                Some(
                    self.create_domain_func_app(
                        "Functions",
                        function_name.clone(),
                        parameters
                            .iter()
                            .map(|parameter| parameter.clone().into())
                            .chain(std::iter::once(gas_amount))
                            .collect(),
                        return_type.clone(),
                        Default::default(),
                    )?,
                ),
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
                        ([call] == [call_without_gas_level]) 
                        //([destructor_calls.into_iter().fold(true.into(), |acc, x| expr! {[acc] && [x]})])
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
    /*
    This has not needed at moment, as long as their is an axioms in snapshot domains that compares 
    a snapshot variable directly with its constructors/destructors, e.g.
    forall value: Snap :: valid(value) ==> value == constructor$Snap$$(destructor$Snap$$value(value)))

    Details are found in Markus Limbeck BA

    fn unroll_model(&mut self, typ: vir_mid::Type, expr: vir_low::Expression, bound: usize) -> SpannedEncodingResult<vir_low::Expression>{
        use vir_low::macros::*;
        if bound > 0{
            match &typ {
                vir_mid::Type::Bool => {
                    let const_value = self.obtain_constant_value(&typ, expr, Default::default())?;
                    let dummy_function_name = format!("dummy_model$Bool");
                    let argument: vir_low::Expression = var! { __result: {vir_low::Type::Bool} }.into();
                    self.create_domain_func_app(
                        "Functions",
                        dummy_function_name.clone(),
                        vec![argument],
                        vir_low::Type::Bool,
                        Default::default(),
                    )?;
                    let destructor_call = vir_low::Expression::domain_function_call(
                        "Functions",
                        dummy_function_name.clone(),
                        vec![const_value.clone()],
                        vir_low::Type::Bool,
                    );
                    return Ok(destructor_call);
                },
                vir_mid::Type::Int(_) => {
                    let const_value = self.obtain_constant_value(&typ, expr, Default::default())?;
                    let dummy_function_name = format!("dummy_model$Int");
                    let argument: vir_low::Expression = var! { __result: {vir_low::Type::Int} }.into();
                    self.create_domain_func_app(
                        "Functions",
                        dummy_function_name.clone(),
                        vec![argument],
                        vir_low::Type::Bool,
                        Default::default(),
                    )?;
                    let destructor_call = vir_low::Expression::domain_function_call(
                        "Functions",
                        dummy_function_name.clone(),
                        vec![const_value.clone()],
                        vir_low::Type::Bool,
                    );
                    return Ok(destructor_call);
                },
                vir_mid::Type::Struct(_) => {
                    if let vir_mid::TypeDecl::Struct(vir_mid::type_decl::Struct{name: _, fields}) = self.encoder.get_type_decl_mid(&typ)?{
                        let mut exprs: Vec<vir_low::Expression> = vec![];
                        for field in fields{
                            let field_expr = self.obtain_struct_field_snapshot(&typ, &field, expr.clone(), Default::default())?;
                            exprs.push(self.unroll_model(field.ty, field_expr, bound-1)?);
                        }
                        return Ok(exprs.into_iter().fold(true.into(), |acc, x| expr! {[acc] && [x]}));
                    }
                    unreachable!("Snapshot Type and TypeDecl should always match")
                },
                _ => (),
            }
        }
        //Either type is not supported for unrolling or the max number of iterations has been reached
        let snap_type = typ.to_snapshot(self)?;
        let dummy_function_name = format!("dummy_model${}", snap_type);
        let argument: vir_low::Expression = var! { __result: {snap_type.clone()} }.into();
        self.create_domain_func_app(
            "Functions",
            dummy_function_name.clone(),
            vec![argument],
            vir_low::Type::Bool,
            Default::default(),
        )?;
        let destructor_call = vir_low::Expression::domain_function_call(
            "Functions",
            dummy_function_name.clone(),
            vec![expr],
            vir_low::Type::Bool,
        );
        Ok(destructor_call)
    }*/
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
