use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        builtin_methods::CallContext,
        lowerer::{DomainsLowererInterface, Lowerer, PredicatesLowererInterface},
        snapshots::{IntoProcedureSnapshot, IntoPureSnapshot, SnapshotVariablesInterface},
    },
};
use std::collections::{BTreeMap, VecDeque};
use vir_crate::{
    common::{
        builtin_constants::LIFETIME_DOMAIN_NAME,
        expression::{BinaryOperationHelpers, QuantifierHelpers},
    },
    low as vir_low, middle as vir_mid,
    middle::operations::lifetimes::WithLifetimes,
};

#[derive(Default)]
pub(in super::super) struct LifetimesState {
    is_lifetime_token_encoded: bool,
    is_lifetime_included_encoded: bool,
    lifetime_is_alive_initialization: BTreeMap<vir_mid::VariableDecl, vir_low::Statement>,
}

impl LifetimesState {
    pub(in super::super) fn lifetime_is_alive_initialization(self) -> Vec<vir_low::Statement> {
        self.lifetime_is_alive_initialization
            .into_values()
            .collect()
    }
}

trait Private {
    fn encode_lifetime_included_intersect_axiom_body(
        &mut self,
        expressions: &mut VecDeque<vir_low::Expression>,
    ) -> vir_low::Expression;
}

pub(in super::super) trait LifetimesInterface {
    fn lifetime_domain_name(&self) -> SpannedEncodingResult<String>;
    fn lifetime_set_type(&mut self) -> SpannedEncodingResult<vir_low::Type>;
    fn lifetime_type(&mut self) -> SpannedEncodingResult<vir_low::Type>;
    fn create_lifetime_var_decls(
        &mut self,
        lft_count: usize,
    ) -> SpannedEncodingResult<Vec<vir_low::VariableDecl>>;
    fn create_lifetime_parameters<G>(
        &mut self,
        generics: &G,
    ) -> SpannedEncodingResult<Vec<vir_low::VariableDecl>>
    where
        G: WithLifetimes;
    fn create_lifetime_arguments<G>(
        &mut self,
        context: CallContext,
        generics: &G,
    ) -> SpannedEncodingResult<Vec<vir_low::Expression>>
    where
        G: WithLifetimes;
    fn create_lifetime_expressions(
        &mut self,
        lft_count: usize,
    ) -> SpannedEncodingResult<Vec<vir_low::Expression>>;
    fn encode_lifetime_included(&mut self) -> SpannedEncodingResult<()>;
    fn encode_lifetime_included_in_itself_axiom(&mut self) -> SpannedEncodingResult<()>;
    fn encode_lifetime_included_intersect_axiom(&mut self) -> SpannedEncodingResult<()>;
    fn encode_lifetime_token_predicate(&mut self) -> SpannedEncodingResult<()>;
    fn encode_lifetime_const_into_procedure_variable(
        &mut self,
        lifetime: vir_mid::ty::LifetimeConst,
    ) -> SpannedEncodingResult<vir_low::VariableDecl>;
    fn encode_lifetime_const_into_procedure_is_alive_variable(
        &mut self,
        lifetime: &vir_mid::ty::LifetimeConst,
    ) -> SpannedEncodingResult<vir_low::VariableDecl>;
    fn encode_lifetime_const_into_is_alive_variable(
        &mut self,
        lifetime: &vir_mid::ty::LifetimeConst,
    ) -> SpannedEncodingResult<vir_mid::VariableDecl>;
    fn encode_lifetime_const_into_pure_is_alive_variable(
        &mut self,
        lifetime: &vir_mid::ty::LifetimeConst,
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
        Ok(LIFETIME_DOMAIN_NAME.to_string())
    }

    fn lifetime_type(&mut self) -> SpannedEncodingResult<vir_low::Type> {
        self.domain_type(self.lifetime_domain_name()?)
    }

    fn lifetime_set_type(&mut self) -> SpannedEncodingResult<vir_low::Type> {
        Ok(vir_low::Type::set(
            self.domain_type(self.lifetime_domain_name()?)?,
        ))
    }

    fn create_lifetime_var_decls(
        &mut self,
        lft_count: usize,
    ) -> SpannedEncodingResult<Vec<vir_low::VariableDecl>> {
        let ty = self.domain_type(LIFETIME_DOMAIN_NAME)?;
        let mut lifetimes: Vec<vir_low::VariableDecl> = vec![];
        for i in 1..(lft_count + 1) {
            lifetimes.push(vir_low::VariableDecl::new(format!("lft_{i}"), ty.clone()));
        }
        Ok(lifetimes)
    }

    fn create_lifetime_parameters<G>(
        &mut self,
        generics: &G,
    ) -> SpannedEncodingResult<Vec<vir_low::VariableDecl>>
    where
        G: WithLifetimes,
    {
        let mut parameters = Vec::new();
        for lifetime in generics.get_lifetimes() {
            parameters.push(self.encode_lifetime_const_into_pure_is_alive_variable(&lifetime)?);
            parameters.push(lifetime.to_pure_snapshot(self)?);
        }
        Ok(parameters)
    }

    fn create_lifetime_arguments<G>(
        &mut self,
        context: CallContext,
        generics: &G,
    ) -> SpannedEncodingResult<Vec<vir_low::Expression>>
    where
        G: WithLifetimes,
    {
        let mut arguments = Vec::new();
        for lifetime in generics.get_lifetimes() {
            let is_alive_variable = match context {
                CallContext::BuiltinMethod => {
                    self.encode_lifetime_const_into_pure_is_alive_variable(&lifetime)?
                }
                CallContext::Procedure => {
                    self.encode_lifetime_const_into_procedure_is_alive_variable(&lifetime)?
                }
            };
            arguments.push(is_alive_variable.into());
            let lifetime_variable = match context {
                CallContext::BuiltinMethod => lifetime.to_pure_snapshot(self)?,
                CallContext::Procedure => {
                    self.encode_lifetime_const_into_procedure_variable(lifetime)?
                }
            };
            arguments.push(lifetime_variable.into());
        }
        Ok(arguments)
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

    fn encode_lifetime_included(&mut self) -> SpannedEncodingResult<()> {
        if !self.lifetimes_state.is_lifetime_included_encoded {
            self.lifetimes_state.is_lifetime_included_encoded = true;
            use vir_low::macros::*;
            var_decls!(lft_1: Lifetime);
            var_decls!(lft_2: Lifetime);
            let arguments: Vec<vir_low::Expression> = vec![lft_1.into(), lft_2.into()];
            self.create_domain_func_app(
                LIFETIME_DOMAIN_NAME,
                "included",
                arguments,
                vir_low::ty::Type::Bool,
                Default::default(),
            )?;
            self.encode_lifetime_included_in_itself_axiom()?;
            self.encode_lifetime_included_intersect_axiom()?;
        }
        Ok(())
    }

    fn encode_lifetime_included_in_itself_axiom(&mut self) -> SpannedEncodingResult<()> {
        use vir_low::macros::*;
        var_decls!(lft: Lifetime);
        let quantifier_body = self.create_domain_func_app(
            LIFETIME_DOMAIN_NAME,
            "included",
            vec![lft.clone().into(), lft.clone().into()],
            vir_low::ty::Type::Bool,
            Default::default(),
        )?;
        let axiom = vir_low::DomainAxiomDecl {
            comment: None,
            name: "included_in_itself$".to_string(),
            body: QuantifierHelpers::forall(
                vec![lft],
                vec![vir_low::Trigger::new(vec![quantifier_body.clone()])],
                quantifier_body,
            ),
        };
        self.declare_axiom(LIFETIME_DOMAIN_NAME, axiom)?;
        Ok(())
    }

    fn encode_lifetime_included_intersect_axiom(&mut self) -> SpannedEncodingResult<()> {
        use vir_low::macros::*;
        let lifetime_set_type = self.lifetime_set_type()?;
        let included = ty! { Bool };
        let intersect = ty! { Lifetime };
        {
            var_decls! {
                lft_1: {lifetime_set_type.clone()},
                lft_2: {lifetime_set_type.clone()}
            }
            let trigger = expr! {
                Lifetime::included(
                    (Lifetime::intersect(lft_1)),
                    (Lifetime::intersect(lft_2))
                )
            };
            let body = expr! {
                (
                    Lifetime::included(
                        (Lifetime::intersect(lft_1)),
                        (Lifetime::intersect(lft_2))
                    )
                ) == (lft_2 subset lft_1)
            };

            let axiom = vir_low::DomainAxiomDecl {
                comment: None,
                name: "included_intersect$1".to_string(),
                body: QuantifierHelpers::forall(
                    vec![lft_1, lft_2],
                    vec![vir_low::Trigger::new(vec![trigger])],
                    body,
                ),
            };
            self.declare_axiom(LIFETIME_DOMAIN_NAME, axiom)?;
        }
        {
            var_decls! {
                lft_1: {lifetime_set_type.clone()},
                lft_2: Lifetime
            }
            let trigger = expr! {
                Lifetime::included(
                    (Lifetime::intersect(lft_1)),
                    lft_2
                )
            };
            let body = expr! {
                (
                    Lifetime::included(
                        (Lifetime::intersect(lft_1)),
                        lft_2
                    )
                ) == (lft_2 in lft_1)
            };
            let axiom = vir_low::DomainAxiomDecl {
                comment: None,
                name: "included_intersect$2".to_string(),
                body: QuantifierHelpers::forall(
                    vec![lft_1, lft_2],
                    vec![vir_low::Trigger::new(vec![trigger])],
                    body,
                ),
            };
            self.declare_axiom(LIFETIME_DOMAIN_NAME, axiom)?;
        }
        {
            var_decls! {
                lft: Lifetime
            }
            let lft_set = vir_low::Expression::container_op_no_pos(
                vir_low::ContainerOpKind::SetConstructor,
                lifetime_set_type,
                vec![lft.clone().into()],
            );
            let intersect = expr! {
                Lifetime::intersect([lft_set])
            };
            let trigger = intersect.clone();
            let body = expr! {
                [intersect] == lft
            };
            let axiom = vir_low::DomainAxiomDecl {
                comment: None,
                name: "intersect_singleton$".to_string(),
                body: QuantifierHelpers::forall(
                    vec![lft],
                    vec![vir_low::Trigger::new(vec![trigger])],
                    body,
                ),
            };
            self.declare_axiom(LIFETIME_DOMAIN_NAME, axiom)?;
        }
        Ok(())
    }

    fn encode_lifetime_token_predicate(&mut self) -> SpannedEncodingResult<()> {
        if !self.lifetimes_state.is_lifetime_token_encoded {
            self.lifetimes_state.is_lifetime_token_encoded = true;
            let predicate = vir_low::PredicateDecl::new(
                "LifetimeToken",
                vir_low::PredicateKind::LifetimeToken,
                vec![vir_low::VariableDecl::new(
                    "lifetime",
                    self.lifetime_type()?,
                )],
                None,
            );
            self.declare_predicate(predicate)?;
            let predicate = vir_low::PredicateDecl::new(
                "DeadLifetimeToken",
                vir_low::PredicateKind::DeadLifetimeToken,
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

    fn encode_lifetime_const_into_procedure_variable(
        &mut self,
        lifetime: vir_mid::ty::LifetimeConst,
    ) -> SpannedEncodingResult<vir_low::VariableDecl> {
        let lifetime_variable = vir_mid::VariableDecl::new(lifetime.name, vir_mid::Type::Lifetime);
        lifetime_variable.to_procedure_snapshot(self)
    }

    fn encode_lifetime_const_into_is_alive_variable(
        &mut self,
        lifetime: &vir_mid::ty::LifetimeConst,
    ) -> SpannedEncodingResult<vir_mid::VariableDecl> {
        Ok(vir_mid::VariableDecl::new(
            format!("{}$alive", lifetime.name),
            vir_mid::Type::MBool,
        ))
    }

    fn encode_lifetime_const_into_procedure_is_alive_variable(
        &mut self,
        lifetime: &vir_mid::ty::LifetimeConst,
    ) -> SpannedEncodingResult<vir_low::VariableDecl> {
        let is_alive_variable = self.encode_lifetime_const_into_is_alive_variable(lifetime)?;
        if !self
            .lifetimes_state
            .lifetime_is_alive_initialization
            .contains_key(&is_alive_variable)
        {
            let variable = self.initial_snapshot_variable_version(&is_alive_variable)?;
            let position = self.procedure_position.unwrap();
            self.lifetimes_state
                .lifetime_is_alive_initialization
                .insert(
                    is_alive_variable.clone(),
                    vir_low::Statement::assume(variable.into(), position),
                );
        }
        is_alive_variable.to_procedure_snapshot(self)
    }

    fn encode_lifetime_const_into_pure_is_alive_variable(
        &mut self,
        lifetime: &vir_mid::ty::LifetimeConst,
    ) -> SpannedEncodingResult<vir_low::VariableDecl> {
        let is_alive_variable = self.encode_lifetime_const_into_is_alive_variable(lifetime)?;
        is_alive_variable.to_pure_snapshot(self)
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
            lifetimes.push(self.encode_lifetime_const_into_procedure_variable(lifetime)?);
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
