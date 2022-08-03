use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        lowerer::{DomainsLowererInterface, Lowerer, PredicatesLowererInterface},
        snapshots::IntoProcedureSnapshot,
    },
};
use rustc_hash::FxHashSet;
use std::collections::VecDeque;
use vir_crate::{
    common::expression::{BinaryOperationHelpers, QuantifierHelpers},
    low as vir_low, middle as vir_mid,
    middle::operations::lifetimes::WithLifetimes,
};

#[derive(Default)]
pub(in super::super) struct LifetimesState {
    is_lifetime_token_encoded: bool,
    is_lifetime_included_encoded: bool,
    encoded_lifetime_intersect: FxHashSet<usize>,
    encoded_lifetime_included_intersect_axiom: FxHashSet<usize>,
}

trait Private {
    fn encode_lifetime_included_intersect_axiom_body(
        &mut self,
        expressions: &mut VecDeque<vir_low::Expression>,
    ) -> vir_low::Expression;
}

pub(in super::super) trait LifetimesInterface {
    fn lifetime_domain_name(&self) -> SpannedEncodingResult<String>;
    fn lifetime_type(&mut self) -> SpannedEncodingResult<vir_low::Type>;
    fn create_lifetime_var_decls(
        &mut self,
        lft_count: usize,
    ) -> SpannedEncodingResult<Vec<vir_low::VariableDecl>>;
    fn create_lifetime_expressions(
        &mut self,
        lft_count: usize,
    ) -> SpannedEncodingResult<Vec<vir_low::Expression>>;
    fn encode_lifetime_intersect(&mut self, lft_count: usize) -> SpannedEncodingResult<()>;
    fn encode_lifetime_included(&mut self) -> SpannedEncodingResult<()>;
    fn encode_lifetime_included_in_itself_axiom(&mut self) -> SpannedEncodingResult<()>;
    fn encode_lifetime_included_intersect_axiom(
        &mut self,
        lft_count: usize,
    ) -> SpannedEncodingResult<()>;
    fn encode_lifetime_token_predicate(&mut self) -> SpannedEncodingResult<()>;
    fn encode_lifetime_const_into_variable(
        &mut self,
        lifetime: vir_mid::ty::LifetimeConst,
    ) -> SpannedEncodingResult<vir_low::VariableDecl>;
    fn encode_lifetime_token(
        &mut self,
        lifetime: vir_low::VariableDecl,
        permission: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn extract_lifetime_variables(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<Vec<vir_low::VariableDecl>>;
    fn extract_lifetime_variables_as_expr(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<Vec<vir_low::Expression>>;
}

impl<'p, 'v: 'p, 'tcx: 'v> Private for Lowerer<'p, 'v, 'tcx> {
    fn encode_lifetime_included_intersect_axiom_body(
        &mut self,
        expressions: &mut VecDeque<vir_low::Expression>,
    ) -> vir_low::Expression {
        assert!(!expressions.is_empty());
        if expressions.len() == 1 {
            return expressions.pop_front().unwrap();
        }
        let first = expressions.pop_front().unwrap();
        BinaryOperationHelpers::and(
            first,
            self.encode_lifetime_included_intersect_axiom_body(expressions),
        )
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> LifetimesInterface for Lowerer<'p, 'v, 'tcx> {
    fn lifetime_domain_name(&self) -> SpannedEncodingResult<String> {
        Ok("Lifetime".to_string())
    }

    fn lifetime_type(&mut self) -> SpannedEncodingResult<vir_low::Type> {
        self.domain_type(self.lifetime_domain_name()?)
    }

    fn create_lifetime_var_decls(
        &mut self,
        lft_count: usize,
    ) -> SpannedEncodingResult<Vec<vir_low::VariableDecl>> {
        let ty = self.domain_type("Lifetime")?;
        let mut lifetimes: Vec<vir_low::VariableDecl> = vec![];
        for i in 1..(lft_count + 1) {
            lifetimes.push(vir_low::VariableDecl::new(format!("lft_{}", i), ty.clone()));
        }
        Ok(lifetimes)
    }

    fn create_lifetime_expressions(
        &mut self,
        lft_count: usize,
    ) -> SpannedEncodingResult<Vec<vir_low::Expression>> {
        Ok(self
            .create_lifetime_var_decls(lft_count)?
            .into_iter()
            .map(vir_low::Expression::local_no_pos)
            .collect())
    }

    fn encode_lifetime_intersect(&mut self, lft_count: usize) -> SpannedEncodingResult<()> {
        if !self
            .lifetimes_state
            .encoded_lifetime_intersect
            .contains(&lft_count)
        {
            self.lifetimes_state
                .encoded_lifetime_intersect
                .insert(lft_count);
            self.encode_lifetime_included()?;
            self.encode_lifetime_included_intersect_axiom(lft_count)?;
            let return_type = self.domain_type("Lifetime")?;
            let arguments = self.create_lifetime_expressions(lft_count).unwrap();
            self.create_domain_func_app(
                "Lifetime",
                format!("intersect${lft_count}"),
                arguments,
                return_type,
                Default::default(),
            )?;
        }
        Ok(())
    }

    fn encode_lifetime_included(&mut self) -> SpannedEncodingResult<()> {
        if !self.lifetimes_state.is_lifetime_included_encoded {
            self.lifetimes_state.is_lifetime_included_encoded = true;
            use vir_low::macros::*;
            var_decls!(lft_1: Lifetime);
            var_decls!(lft_2: Lifetime);
            let arguments: Vec<vir_low::Expression> = vec![lft_1.into(), lft_2.into()];
            self.create_domain_func_app(
                "Lifetime",
                "included",
                arguments,
                vir_low::ty::Type::Bool,
                Default::default(),
            )?;
            self.encode_lifetime_included_in_itself_axiom()?;
        }
        Ok(())
    }

    fn encode_lifetime_included_in_itself_axiom(&mut self) -> SpannedEncodingResult<()> {
        use vir_low::macros::*;
        var_decls!(lft: Lifetime);
        let quantifier_body = self.create_domain_func_app(
            "Lifetime",
            "included",
            vec![lft.clone().into(), lft.clone().into()],
            vir_low::ty::Type::Bool,
            Default::default(),
        )?;
        let axiom = vir_low::DomainAxiomDecl {
            name: "included_in_itself$".to_string(),
            body: QuantifierHelpers::forall(vec![lft], vec![], quantifier_body),
        };
        self.declare_axiom("Lifetime", axiom)?;
        Ok(())
    }

    fn encode_lifetime_included_intersect_axiom(
        &mut self,
        lft_count: usize,
    ) -> SpannedEncodingResult<()> {
        if !self
            .lifetimes_state
            .encoded_lifetime_included_intersect_axiom
            .contains(&lft_count)
        {
            self.lifetimes_state
                .encoded_lifetime_included_intersect_axiom
                .insert(lft_count);

            let ty = self.domain_type("Lifetime")?;

            // Variables
            let mut variables = vec![];
            for i in 1..(lft_count + 1) {
                variables.push(vir_low::VariableDecl::new(format!("lft_{i}"), ty.clone()))
            }

            // Arguments for Triggers and Body
            let arguments_all_lifetimes = self.create_lifetime_expressions(lft_count).unwrap();

            // Expression arguments
            let mut arguments: Vec<Vec<vir_low::Expression>> = vec![];
            for i in 1..(lft_count + 1) {
                arguments.push(vec![
                    vir_low::Expression::local_no_pos(vir_low::VariableDecl::new(
                        format!("lft_{i}"),
                        ty.clone(),
                    )),
                    vir_low::Expression::domain_function_call(
                        "Lifetime",
                        format!("intersect${lft_count}"),
                        arguments_all_lifetimes.clone(),
                        ty.clone(),
                    ),
                ]);
            }

            // Triggers
            let mut trigger_expressions = vec![];
            for i in 1..(lft_count + 1) {
                trigger_expressions.push(self.create_domain_func_app(
                    "Lifetime",
                    "included",
                    arguments.get_mut(i - 1).unwrap().clone(),
                    vir_low::ty::Type::Bool,
                    Default::default(),
                )?);
            }
            let triggers: Vec<vir_low::Trigger> = trigger_expressions
                .clone()
                .into_iter()
                .map(|e| vir_low::Trigger { terms: vec![e] })
                .collect();

            // Body
            let quantifier_body = self.encode_lifetime_included_intersect_axiom_body(
                &mut trigger_expressions.clone().into(),
            );

            let axiom = vir_low::DomainAxiomDecl {
                name: format!("included_intersect${lft_count}"),
                body: QuantifierHelpers::forall(variables, triggers, quantifier_body),
            };
            self.declare_axiom("Lifetime", axiom)?;
        }
        Ok(())
    }

    fn encode_lifetime_token_predicate(&mut self) -> SpannedEncodingResult<()> {
        if !self.lifetimes_state.is_lifetime_token_encoded {
            self.lifetimes_state.is_lifetime_token_encoded = true;
            let predicate = vir_low::PredicateDecl::new(
                "LifetimeToken",
                vec![vir_low::VariableDecl::new(
                    "lifetime",
                    self.lifetime_type()?,
                )],
                None,
            );
            self.declare_predicate(predicate)?;
            let predicate = vir_low::PredicateDecl::new(
                "DeadLifetimeToken",
                vec![vir_low::VariableDecl::new(
                    "lifetime",
                    self.lifetime_type()?,
                )],
                None,
            );
            self.declare_predicate(predicate)?;
        }
        Ok(())
    }

    fn encode_lifetime_const_into_variable(
        &mut self,
        lifetime: vir_mid::ty::LifetimeConst,
    ) -> SpannedEncodingResult<vir_low::VariableDecl> {
        let lifetime_variable = vir_mid::VariableDecl::new(lifetime.name, vir_mid::Type::Lifetime);
        lifetime_variable.to_procedure_snapshot(self)
    }

    fn encode_lifetime_token(
        &mut self,
        lifetime: vir_low::VariableDecl,
        permission: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        Ok(vir_low::Expression::predicate_access_predicate_no_pos(
            "LifetimeToken".to_string(),
            vec![lifetime.into()],
            permission,
        ))
    }

    fn extract_lifetime_variables(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<Vec<vir_low::VariableDecl>> {
        let mut lifetimes = Vec::new();
        for lifetime in ty.get_lifetimes() {
            lifetimes.push(self.encode_lifetime_const_into_variable(lifetime)?);
        }
        Ok(lifetimes)
    }

    fn extract_lifetime_variables_as_expr(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<Vec<vir_low::Expression>> {
        Ok(self
            .extract_lifetime_variables(ty)?
            .into_iter()
            .map(|lifetime| lifetime.into())
            .collect())
    }
}
