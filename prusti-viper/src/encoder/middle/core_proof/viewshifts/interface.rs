use super::state::{ViewShiftBody, ViewShiftSignature};
use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::lowerer::{Lowerer, MethodsLowererInterface, PredicatesLowererInterface},
};
use rustc_hash::FxHashMap;
use vir_crate::low::{self as vir_low, operations::ty::Typed};

pub(in super::super) trait ViewShiftsInterface {
    fn encode_view_shift_predicate(
        &mut self,
        name: &str,
        arguments: Vec<vir_low::Expression>,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>;

    /// Encode a viewshift to be used in the postcondition of a method and
    /// declare its dependencies:
    ///
    /// 1.  An opaque predicate used as a resource for the viewshift.
    /// 2.  A helper method that applies the viewshift.
    fn encode_view_shift_return(
        &mut self,
        name: &str,
        arguments: Vec<vir_low::Expression>,
        precondition: Vec<vir_low::Expression>,
        postcondition: Vec<vir_low::Expression>,
        predicate_kind: vir_low::PredicateKind,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>;

    fn encode_apply_view_shift(
        &mut self,
        name: &str,
        condition: Option<vir_low::Expression>,
        arguments: Vec<vir_low::Expression>,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Statement>;
}

impl<'p, 'v: 'p, 'tcx: 'v> Lowerer<'p, 'v, 'tcx> {
    fn encode_predicate_name(&mut self, name: &str) -> String {
        format!("view_shift${name}")
    }

    fn encode_method_name(&mut self, name: &str) -> String {
        format!("apply_view_shift${name}")
    }

    fn encode_view_shift_predicate_and_apply_method(
        &mut self,
        name: &str,
        arguments: Vec<vir_low::Expression>,
        mut precondition: Vec<vir_low::Expression>,
        mut postcondition: Vec<vir_low::Expression>,
        predicate_kind: vir_low::PredicateKind,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        let mut parameters = Vec::new();
        let mut replacements = FxHashMap::default();
        for (i, argument) in arguments.iter().enumerate() {
            if let vir_low::Expression::Local(local) = argument {
                parameters.push(local.variable.clone());
            } else {
                let parameter =
                    vir_low::VariableDecl::new(format!("arg${i}"), argument.get_type().clone());
                let parameter_expression = parameter.clone().into();
                replacements.insert(argument.clone(), parameter_expression);
                parameters.push(parameter);
            }
        }
        // precondition = precondition
        //     .into_iter()
        //     .map(|expression| expression.replace_subexpressions(&replacements))
        //     .collect();
        // postcondition = postcondition
        //     .into_iter()
        //     .map(|expression| expression.replace_subexpressions(&replacements))
        //     .collect();
        precondition = self.apply_replacements(precondition, &replacements);
        postcondition = self.apply_replacements(postcondition, &replacements);
        let predicate_name = self.encode_predicate_name(name);
        // let view_shift_predicate = vir_low::Expression::predicate_access_predicate(
        //     predicate_name.clone(),
        //     parameters
        //         .iter()
        //         .map(|parameter| parameter.clone().into())
        //         .collect(),
        //     vir_low::Expression::full_permission(),
        //     position,
        // );
        let view_shift_predicate = self.encode_view_shift_predicate(
            name,
            parameters
                .iter()
                .map(|parameter| parameter.clone().into())
                .collect(),
            position,
        )?;
        let view_shift_predicate_decl = vir_low::PredicateDecl::new(
            predicate_name,
            predicate_kind,
            // ::WithoutSnapshotWhole,
            parameters.clone(),
            None,
        );
        self.declare_predicate(view_shift_predicate_decl)?;
        precondition.push(view_shift_predicate);
        let apply_view_shift_method = vir_low::MethodDecl::new(
            self.encode_method_name(name),
            vir_low::MethodKind::MirOperation,
            parameters,
            Vec::new(),
            precondition,
            postcondition,
            None,
        );
        self.declare_method(apply_view_shift_method)?;
        Ok(())
    }

    fn construct_view_shift_signature(
        &mut self,
        name: &str,
        arguments: &[vir_low::Expression],
    ) -> ViewShiftSignature {
        let types = arguments
            .iter()
            .map(|argument| argument.get_type().clone())
            .collect();
        (name.to_string(), types)
    }

    fn construct_replacements(
        &self,
        arguments: &[vir_low::Expression],
    ) -> FxHashMap<vir_low::Expression, vir_low::Expression> {
        let mut replacements = FxHashMap::default();
        for (i, argument) in arguments.iter().enumerate() {
            let parameter =
                vir_low::VariableDecl::new(format!("arg${i}"), argument.get_type().clone());
            let parameter_expression = parameter.clone().into();
            replacements.insert(argument.clone(), parameter_expression);
        }
        replacements
    }

    fn apply_replacements(
        &self,
        expression: Vec<vir_low::Expression>,
        replacements: &FxHashMap<vir_low::Expression, vir_low::Expression>,
    ) -> Vec<vir_low::Expression> {
        expression
            .into_iter()
            .map(|expression| expression.replace_subexpressions(replacements))
            .collect()
    }

    fn construct_view_shift_body(
        &mut self,
        _name: &str,
        arguments: &[vir_low::Expression],
        precondition: &[vir_low::Expression],
        postcondition: &[vir_low::Expression],
    ) -> ViewShiftBody {
        let replacements = self.construct_replacements(arguments);
        let precondition = self.apply_replacements(precondition.to_vec(), &replacements);
        let postcondition = self.apply_replacements(postcondition.to_vec(), &replacements);
        (precondition, postcondition)
    }

    fn register_view_shift_body(
        &mut self,
        name: &str,
        arguments: &[vir_low::Expression],
        precondition: &[vir_low::Expression],
        postcondition: &[vir_low::Expression],
    ) {
        if !cfg!(debug_assertions) {
            return;
        }
        let signature = self.construct_view_shift_signature(name, arguments);
        let body = self.construct_view_shift_body(name, arguments, precondition, postcondition);
        self.view_shifts_state
            .encoded_view_content
            .insert(signature, body);
    }

    fn assert_same_view_shift(
        &mut self,
        name: &str,
        arguments: &[vir_low::Expression],
        precondition: &[vir_low::Expression],
        postcondition: &[vir_low::Expression],
    ) {
        if !cfg!(debug_assertions) {
            return;
        }
        let signature = self.construct_view_shift_signature(name, arguments);
        let body = self.construct_view_shift_body(name, arguments, precondition, postcondition);
        let old_body = self
            .view_shifts_state
            .encoded_view_content
            .get(&signature)
            .unwrap();
        assert_eq!(body, *old_body);
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> ViewShiftsInterface for Lowerer<'p, 'v, 'tcx> {
    fn encode_view_shift_predicate(
        &mut self,
        name: &str,
        arguments: Vec<vir_low::Expression>,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let predicate_name = self.encode_predicate_name(name);
        let predicate_access = vir_low::Expression::predicate_access_predicate(
            predicate_name,
            arguments,
            vir_low::Expression::full_permission(),
            position,
        );
        Ok(predicate_access)
    }

    fn encode_view_shift_return(
        &mut self,
        name: &str,
        arguments: Vec<vir_low::Expression>,
        precondition: Vec<vir_low::Expression>,
        postcondition: Vec<vir_low::Expression>,
        predicate_kind: vir_low::PredicateKind,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let signature = self.construct_view_shift_signature(name, &arguments);
        if !self
            .view_shifts_state
            .encoded_view_shifts
            .contains(&signature)
        {
            self.register_view_shift_body(name, &arguments, &precondition, &postcondition);
            self.encode_view_shift_predicate_and_apply_method(
                name,
                arguments.clone(),
                precondition,
                postcondition,
                predicate_kind,
                position,
            )?;
            self.view_shifts_state.encoded_view_shifts.insert(signature);
        } else {
            self.assert_same_view_shift(name, &arguments, &precondition, &postcondition);
        }
        // let predicate_name = self.encode_predicate_name(name);
        // let view_shift_predicate = vir_low::Expression::predicate_access_predicate(
        //     predicate_name,
        //     arguments,
        //     vir_low::Expression::full_permission(),
        //     position,
        // );
        let view_shift_predicate = self.encode_view_shift_predicate(name, arguments, position)?;
        Ok(view_shift_predicate)
    }

    fn encode_apply_view_shift(
        &mut self,
        name: &str,
        condition: Option<vir_low::Expression>,
        arguments: Vec<vir_low::Expression>,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Statement> {
        let method_name = self.encode_method_name(name);
        let method_call =
            vir_low::Statement::method_call(method_name, arguments, Vec::new(), position);
        let statement = if let Some(condition) = condition {
            vir_low::Statement::conditional(condition, vec![method_call], Vec::new(), position)
        } else {
            method_call
        };
        Ok(statement)
    }
}
