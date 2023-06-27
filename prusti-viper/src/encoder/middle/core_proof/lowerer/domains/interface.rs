use crate::encoder::{errors::SpannedEncodingResult, middle::core_proof::lowerer::Lowerer};
use std::collections::{BTreeMap, BTreeSet};
use vir_crate::{
    common::identifier::WithIdentifier,
    low::{self as vir_low},
    middle as vir_mid,
};

#[derive(Default)]
pub(in super::super::super) struct DomainsInfo {}

#[derive(Default)]
pub(in super::super) struct DomainsLowererState {
    functions: BTreeSet<String>,
    domains: BTreeMap<String, vir_low::DomainDecl>,
    domains_info: DomainsInfo,
}

impl DomainsLowererState {
    pub fn destruct(self) -> (Vec<vir_low::DomainDecl>, DomainsInfo) {
        (self.domains.into_values().collect(), self.domains_info)
    }
}

// trait DomainsLowererInterfacePrivate {
//     /// Returns a borrow of a domain. Creates the domain if it does not exist.
//     fn borrow_domain(
//         &mut self,
//         domain_name: String,
//     ) -> SpannedEncodingResult<&mut vir_low::DomainDecl>;
//     fn create_domain_func_app_custom(
//         &mut self,
//         domain_name: String,
//         function_name: String,
//         arguments: Vec<vir_low::Expression>,
//         return_type: vir_low::Type,
//         is_unique: bool,
//         position: vir_low::Position,
//     ) -> SpannedEncodingResult<vir_low::Expression>;
// }

impl<'p, 'v: 'p, 'tcx: 'v> Lowerer<'p, 'v, 'tcx> {
    fn borrow_domain(
        &mut self,
        domain_name: String,
    ) -> SpannedEncodingResult<&mut vir_low::DomainDecl> {
        let domain = self
            .domains_state
            .domains
            .entry(domain_name.clone())
            .or_insert_with(|| {
                vir_low::DomainDecl::new(domain_name, Vec::new(), Vec::new(), Vec::new())
            });
        Ok(domain)
    }

    fn create_domain_func_app_custom(
        &mut self,
        domain_name: String,
        function_name: String,
        arguments: Vec<vir_low::Expression>,
        return_type: vir_low::Type,
        is_unique: bool,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let parameters = self.create_parameters(&arguments);
        self.declare_domain_function(
            &domain_name,
            std::borrow::Cow::Borrowed(&function_name),
            is_unique,
            std::borrow::Cow::Borrowed(&parameters),
            std::borrow::Cow::Borrowed(&return_type),
        )?;
        Ok(vir_low::Expression::domain_func_app(
            domain_name,
            function_name,
            arguments,
            parameters,
            return_type,
            position,
        ))
    }
}

pub(in super::super::super) trait DomainsLowererInterface {
    fn ensure_domain(&mut self, domain_name: impl ToString) -> SpannedEncodingResult<()>;
    fn domain_type(&mut self, domain_name: impl ToString) -> SpannedEncodingResult<vir_low::Type>;
    fn declare_axiom(
        &mut self,
        domain_name: &str,
        axiom: vir_low::DomainAxiomDecl,
    ) -> SpannedEncodingResult<()>;
    fn declare_rewrite_rule(
        &mut self,
        domain_name: &str,
        axiom: vir_low::DomainRewriteRuleDecl,
    ) -> SpannedEncodingResult<()>;
    fn insert_domain_function(
        &mut self,
        domain_name: &str,
        domain_function: vir_low::DomainFunctionDecl,
    ) -> SpannedEncodingResult<()>;
    fn declare_domain_function(
        &mut self,
        domain_name: &str,
        function_name: std::borrow::Cow<'_, String>,
        is_unique: bool,
        parameters: std::borrow::Cow<'_, Vec<vir_low::VariableDecl>>,
        return_type: std::borrow::Cow<'_, vir_low::Type>,
    ) -> SpannedEncodingResult<()>;
    // /// Declare a domain function that is a binary operator.
    // fn declare_domain_function_maybe_binary_op(
    //     &mut self,
    //     domain_name: &str,
    //     function_name: std::borrow::Cow<'_, String>,
    //     operation: Option<(vir_mid::BinaryOpKind, vir_mid::Type)>,
    //     parameters: std::borrow::Cow<'_, Vec<vir_low::VariableDecl>>,
    //     return_type: std::borrow::Cow<'_, vir_low::Type>,
    // ) -> SpannedEncodingResult<()>;
    fn create_domain_func_app(
        &mut self,
        domain_name: impl ToString,
        function_name: impl ToString,
        arguments: Vec<vir_low::Expression>,
        return_type: vir_low::Type,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn create_unique_domain_func_app(
        &mut self,
        domain_name: impl ToString,
        function_name: impl ToString,
        arguments: Vec<vir_low::Expression>,
        return_type: vir_low::Type,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn encode_field_access_function_app(
        &mut self,
        domain_name: &str,
        base: vir_low::Expression,
        base_type: &vir_mid::Type,
        field: &vir_mid::FieldDecl,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::ast::expression::Expression>;
    fn encode_variant_access_function_app(
        &mut self,
        domain_name: &str,
        base: vir_low::Expression,
        base_type: &vir_mid::Type,
        variant: &vir_mid::ty::VariantIndex,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::ast::expression::Expression>;
    fn encode_index_access_function_app(
        &mut self,
        domain_name: &str,
        base: vir_low::Expression,
        base_type: &vir_mid::Type,
        index: vir_low::Expression,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::ast::expression::Expression>;
}

impl<'p, 'v: 'p, 'tcx: 'v> DomainsLowererInterface for Lowerer<'p, 'v, 'tcx> {
    fn ensure_domain(&mut self, domain_name: impl ToString) -> SpannedEncodingResult<()> {
        self.borrow_domain(domain_name.to_string())?;
        Ok(())
    }
    fn domain_type(&mut self, domain_name: impl ToString) -> SpannedEncodingResult<vir_low::Type> {
        self.ensure_domain(domain_name.to_string())?;
        Ok(vir_low::Type::domain(domain_name.to_string()))
    }
    fn declare_axiom(
        &mut self,
        domain_name: &str,
        axiom: vir_low::DomainAxiomDecl,
    ) -> SpannedEncodingResult<()> {
        let domain = self.domains_state.domains.get_mut(domain_name).unwrap();
        domain.axioms.push(axiom);
        Ok(())
    }
    fn declare_rewrite_rule(
        &mut self,
        domain_name: &str,
        axiom: vir_low::DomainRewriteRuleDecl,
    ) -> SpannedEncodingResult<()> {
        let domain = self.domains_state.domains.get_mut(domain_name).unwrap();
        domain.rewrite_rules.push(axiom);
        Ok(())
    }
    fn insert_domain_function(
        &mut self,
        domain_name: &str,
        domain_function: vir_low::DomainFunctionDecl,
    ) -> SpannedEncodingResult<()> {
        assert!(
            !self.domains_state.functions.contains(&domain_function.name),
            "already exists: {}",
            domain_function.name
        );
        self.domains_state
            .functions
            .insert(domain_function.name.clone());
        let domain_name = domain_name.to_string();
        let domain = self.borrow_domain(domain_name)?;
        domain.functions.push(domain_function);
        Ok(())
    }
    fn declare_domain_function(
        &mut self,
        domain_name: &str,
        function_name: std::borrow::Cow<'_, String>,
        is_unique: bool,
        parameters: std::borrow::Cow<'_, Vec<vir_low::VariableDecl>>,
        return_type: std::borrow::Cow<'_, vir_low::Type>,
    ) -> SpannedEncodingResult<()> {
        if !self.domains_state.functions.contains(&*function_name) {
            let domain_function = vir_low::DomainFunctionDecl {
                name: function_name.to_string(),
                is_unique,
                parameters: parameters.into_owned(),
                return_type: return_type.into_owned(),
            };
            self.insert_domain_function(domain_name, domain_function)?;
        }
        Ok(())
    }
    // fn declare_domain_function_maybe_binary_op(
    //     &mut self,
    //     domain_name: &str,
    //     function_name: std::borrow::Cow<'_, String>,
    //     operation: Option<(vir_mid::BinaryOpKind, vir_mid::Type)>,
    //     parameters: std::borrow::Cow<'_, Vec<vir_low::VariableDecl>>,
    //     return_type: std::borrow::Cow<'_, vir_low::Type>,
    // ) -> SpannedEncodingResult<()> {
    //     if !self.domains_state.functions.contains(&*function_name) {
    //         if let Some((op, ty)) = operation {
    //             assert!(self
    //                 .domains_state
    //                 .domains_info
    //                 .snapshot_binary_operators
    //                 .insert(function_name.to_string(), (op, ty),)
    //                 .is_none());
    //         }
    //         self.declare_domain_function(
    //             domain_name,
    //             function_name,
    //             false,
    //             parameters,
    //             return_type,
    //         )?;
    //     }
    //     Ok(())
    // }
    /// Note: You are likely to want to call one of this function's wrappers.
    fn create_domain_func_app(
        &mut self,
        domain_name: impl ToString,
        function_name: impl ToString,
        arguments: Vec<vir_low::Expression>,
        return_type: vir_low::Type,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        self.create_domain_func_app_custom(
            domain_name.to_string(),
            function_name.to_string(),
            arguments,
            return_type,
            false,
            position,
        )
    }
    fn create_unique_domain_func_app(
        &mut self,
        domain_name: impl ToString,
        function_name: impl ToString,
        arguments: Vec<vir_low::Expression>,
        return_type: vir_low::Type,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        self.create_domain_func_app_custom(
            domain_name.to_string(),
            function_name.to_string(),
            arguments,
            return_type,
            true,
            position,
        )
    }
    fn encode_field_access_function_app(
        &mut self,
        domain_name: &str,
        base: vir_low::Expression,
        base_type: &vir_mid::Type,
        field: &vir_mid::FieldDecl,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::ast::expression::Expression> {
        let base_type_identifier = base_type.get_identifier();
        let return_type = self.domain_type(domain_name)?;
        self.create_domain_func_app(
            domain_name,
            format!(
                "field_{}$${}$${}",
                domain_name.to_lowercase(),
                base_type_identifier,
                field.name
            ),
            vec![base],
            return_type,
            position,
        )
    }
    fn encode_variant_access_function_app(
        &mut self,
        domain_name: &str,
        base: vir_low::Expression,
        base_type: &vir_mid::Type,
        variant: &vir_mid::ty::VariantIndex,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::ast::expression::Expression> {
        let base_type_identifier = base_type.get_identifier();
        let return_type = self.domain_type(domain_name)?;
        self.create_domain_func_app(
            domain_name,
            format!(
                "variant_{}$${}$${}",
                domain_name.to_lowercase(),
                base_type_identifier,
                variant.index
            ),
            vec![base],
            return_type,
            position,
        )
    }
    fn encode_index_access_function_app(
        &mut self,
        domain_name: &str,
        base: vir_low::Expression,
        base_type: &vir_mid::Type,
        index: vir_low::Expression,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::ast::expression::Expression> {
        let base_type_identifier = base_type.get_identifier();
        let return_type = self.domain_type(domain_name)?;
        self.create_domain_func_app(
            domain_name,
            format!(
                "index_{}$${}",
                domain_name.to_lowercase(),
                base_type_identifier,
            ),
            vec![base, index],
            return_type,
            position,
        )
    }
}
