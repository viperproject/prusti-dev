use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        function_gas::FunctionGasInterface,
        lowerer::{DomainsLowererInterface, Lowerer},
    },
};
use prusti_common::config;
use rustc_hash::FxHashSet;
use std::borrow::Cow;
use vir_crate::{
    common::expression::{ExpressionIterator, QuantifierHelpers},
    low::{self as vir_low},
};

#[derive(Default)]
pub(in super::super) struct AdtsState {
    /// Registered default constructors for a given domain.
    ///
    /// These are typically used in cases where the ADT has only a single
    /// constructor.
    main_constructors: FxHashSet<vir_low::ty::Domain>,
    /// Registered variant constructors for a given domain.
    ///
    /// These are typically used in cases where an ADT has multiple variants.
    variant_constructors: FxHashSet<(vir_low::ty::Domain, String)>,
}

const NO_VARIANT_NAME: &str = "";

pub(in super::super) trait AdtsInterface {
    // Names.

    fn adt_constructor_main_name(&mut self, domain_name: &str) -> SpannedEncodingResult<String> {
        self.adt_constructor_variant_name(domain_name, NO_VARIANT_NAME)
    }
    fn adt_constructor_variant_name(
        &mut self,
        domain_name: &str,
        variant_name: &str,
    ) -> SpannedEncodingResult<String>;
    fn adt_snapshot_equality_variant_name(
        &mut self,
        domain_name: &str,
        variant_name: &str,
    ) -> SpannedEncodingResult<String>;
    fn adt_destructor_main_name(
        &mut self,
        domain_name: &str,
        parameter_name: &str,
    ) -> SpannedEncodingResult<String> {
        self.adt_destructor_variant_name(domain_name, NO_VARIANT_NAME, parameter_name)
    }
    fn adt_destructor_variant_name(
        &mut self,
        domain_name: &str,
        variant_name: &str,
        parameter_name: &str,
    ) -> SpannedEncodingResult<String>;

    // Calls.

    fn adt_constructor_main_call(
        &mut self,
        domain_name: &str,
        arguments: Vec<vir_low::Expression>,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        self.adt_constructor_variant_call(domain_name, NO_VARIANT_NAME, arguments)
    }
    fn adt_constructor_variant_call(
        &mut self,
        domain_name: &str,
        variant_name: &str,
        arguments: Vec<vir_low::Expression>,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn adt_destructor_main_call(
        &mut self,
        domain_name: &str,
        parameter_name: &str,
        parameter_type: vir_low::Type,
        argument: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        self.adt_destructor_variant_call(
            domain_name,
            NO_VARIANT_NAME,
            parameter_name,
            parameter_type,
            argument,
        )
    }
    fn adt_destructor_variant_call(
        &mut self,
        domain_name: &str,
        variant_name: &str,
        parameter_name: &str,
        parameter_type: vir_low::Type,
        argument: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn adt_snapshot_equality_variant_call(
        &mut self,
        domain_name: &str,
        variant_name: &str,
        left: vir_low::Expression,
        right: vir_low::Expression,
        gas: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression>;

    // Registration.

    /// Register the main constructor and derive injectivity axioms for it. If
    /// `top_down_injectivity_guard` is not `None`, when deriving the top-down
    /// injectivity axiom, it is called with the quantified variable and its
    /// result is used to guard the injectivity property. This is intended to be
    /// used by the snapshot encoder to supply call to the validity function.
    fn adt_register_main_constructor<F>(
        &mut self,
        domain_name: &str,
        parameters: Vec<vir_low::VariableDecl>,
        generate_injectivity_axioms: bool,
        top_down_injectivity_guard: Option<F>,
    ) -> SpannedEncodingResult<()>
    where
        F: for<'a> FnOnce(
            &'a str,
            &'a vir_low::VariableDecl,
        )
            -> SpannedEncodingResult<(vir_low::Expression, vir_low::Expression)>;
    /// Register the variant constructor and derive injectivity axioms for it.
    /// If `top_down_injectivity_guard` is not `None`, when deriving the
    /// top-down injectivity axiom, it is called with the quantified variable
    /// and its result is used to guard the injectivity property. This is
    /// intended to be used by the snapshot encoder to supply call to the
    /// validity function.
    ///
    /// If `use_main_constructor_destructors` is true, do not generate
    /// destructors and for injectivity axioms use destructors with
    /// `variant_name==""`. This assumes that this variant's parameters are a
    /// subset of the main constructor's parameters.
    fn adt_register_variant_constructor<F>(
        &mut self,
        domain_name: &str,
        variant_name: &str,
        // operation: Option<(vir_mid::BinaryOpKind, vir_mid::Type)>,
        use_main_constructor_destructors: bool,
        parameters: Vec<vir_low::VariableDecl>,
        generate_injectivity_axioms: bool,
        top_down_injectivity_guard: Option<F>,
    ) -> SpannedEncodingResult<()>
    where
        F: for<'a> FnOnce(
            &'a str,
            &'a vir_low::VariableDecl,
        )
            -> SpannedEncodingResult<(vir_low::Expression, vir_low::Expression)>;
}

impl<'p, 'v: 'p, 'tcx: 'v> AdtsInterface for Lowerer<'p, 'v, 'tcx> {
    fn adt_constructor_variant_name(
        &mut self,
        domain_name: &str,
        variant_name: &str,
    ) -> SpannedEncodingResult<String> {
        Ok(format!("constructor${domain_name}${variant_name}"))
    }
    fn adt_snapshot_equality_variant_name(
        &mut self,
        domain_name: &str,
        variant_name: &str,
    ) -> SpannedEncodingResult<String> {
        Ok(format!("snapshot_equality${domain_name}${variant_name}"))
    }
    fn adt_destructor_variant_name(
        &mut self,
        domain_name: &str,
        variant_name: &str,
        parameter_name: &str,
    ) -> SpannedEncodingResult<String> {
        Ok(format!(
            "destructor${domain_name}${variant_name}${parameter_name}"
        ))
    }
    fn adt_constructor_variant_call(
        &mut self,
        domain_name: &str,
        variant_name: &str,
        arguments: Vec<vir_low::Expression>,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        Ok(vir_low::Expression::domain_function_call(
            domain_name.to_string(),
            self.adt_constructor_variant_name(domain_name, variant_name)?,
            arguments,
            vir_low::Type::domain(domain_name.to_string()),
        ))
    }
    fn adt_destructor_variant_call(
        &mut self,
        domain_name: &str,
        variant_name: &str,
        parameter_name: &str,
        parameter_type: vir_low::Type,
        argument: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        Ok(vir_low::Expression::domain_function_call(
            domain_name.to_string(),
            self.adt_destructor_variant_name(domain_name, variant_name, parameter_name)?,
            vec![argument],
            parameter_type,
        ))
    }
    fn adt_snapshot_equality_variant_call(
        &mut self,
        domain_name: &str,
        variant_name: &str,
        left: vir_low::Expression,
        right: vir_low::Expression,
        gas: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let name = self.adt_snapshot_equality_variant_name(domain_name, variant_name)?;
        // FIXME: This is a hack: this function call should be in
        // SnapshotAdtsInterface::snapshot_equality_call. However, we cannot do
        // that because the actual call is done only by the symbolic execution
        // (only it has enough information to emit the comparison).
        self.snapshots_state
            .snapshot_domains_info
            .register_snapshot_equality(domain_name, &name)?;
        Ok(vir_low::Expression::domain_function_call(
            domain_name.to_string(),
            name,
            vec![left, right, gas],
            vir_low::Type::Bool,
        ))
    }
    fn adt_register_main_constructor<F>(
        &mut self,
        domain_name: &str,
        parameters: Vec<vir_low::VariableDecl>,
        generate_injectivity_axioms: bool,
        top_down_injectivity_guard: Option<F>,
    ) -> SpannedEncodingResult<()>
    where
        F: for<'a> FnOnce(
            &'a str,
            &'a vir_low::VariableDecl,
        )
            -> SpannedEncodingResult<(vir_low::Expression, vir_low::Expression)>,
    {
        assert!(self
            .adts_state
            .main_constructors
            .insert(vir_low::ty::Domain::new(domain_name)));
        self.adt_register_variant_constructor(
            domain_name,
            "",
            // None,
            false,
            parameters,
            generate_injectivity_axioms,
            top_down_injectivity_guard,
        )
    }
    fn adt_register_variant_constructor<F>(
        &mut self,
        domain_name: &str,
        variant_name: &str,
        // operation: Option<(vir_mid::BinaryOpKind, vir_mid::Type)>,
        use_main_constructor_destructors: bool,
        parameters: Vec<vir_low::VariableDecl>,
        generate_injectivity_axioms: bool,
        top_down_injectivity_guard: Option<F>,
    ) -> SpannedEncodingResult<()>
    where
        F: for<'a> FnOnce(
            &'a str,
            &'a vir_low::VariableDecl,
        )
            -> SpannedEncodingResult<(vir_low::Expression, vir_low::Expression)>,
    {
        assert!(self.adts_state.variant_constructors.insert((
            vir_low::ty::Domain::new(domain_name),
            variant_name.to_string()
        )));
        let ty = vir_low::Type::domain(domain_name.to_string());

        let destructor_variant_name = if use_main_constructor_destructors {
            ""
        } else {
            variant_name
        };

        // Constructor.
        let constructor_name = self.adt_constructor_variant_name(domain_name, variant_name)?;
        self.declare_domain_function(
            domain_name,
            Cow::Borrowed(&constructor_name),
            false,
            Cow::Borrowed(&parameters),
            Cow::Borrowed(&ty),
        )?;

        // Destructors.
        let value = vir_low::VariableDecl::new("value", ty.clone());
        for parameter in &parameters {
            let destructor_name = self.adt_destructor_variant_name(
                domain_name,
                destructor_variant_name,
                &parameter.name,
            )?;
            self.declare_domain_function(
                domain_name,
                Cow::Owned(destructor_name),
                false,
                Cow::Owned(vec![value.clone()]),
                Cow::Borrowed(&parameter.ty),
            )?;
        }

        // Snapshot equality. This function is used to trigger extensionality
        // axioms for types that have Viper sequences as their constituents.
        let snapshot_equality_name =
            self.adt_snapshot_equality_variant_name(domain_name, variant_name)?;
        let left = vir_low::VariableDecl::new("left", ty.clone());
        let right = vir_low::VariableDecl::new("right", ty.clone());
        let gas = self.function_gas_parameter()?;
        self.declare_domain_function(
            domain_name,
            Cow::Owned(snapshot_equality_name),
            false,
            Cow::Owned(vec![left, right, gas]),
            Cow::Owned(vir_low::Type::Bool),
        )?;

        // Injectivity axioms.
        if generate_injectivity_axioms {
            // We do not generate injectivity axioms for alternative
            // constructors (that would be unsound).

            use vir_low::macros::*;
            // Bottom-up injectivity axiom.
            if !parameters.is_empty() {
                // We need something to quantify over, so parameters cannot be empty.
                let mut triggers = Vec::new();
                // let mut conjuncts = Vec::new();
                let constructor_call = self.adt_constructor_variant_call(
                    domain_name,
                    variant_name,
                    parameters
                        .iter()
                        .map(|argument| argument.clone().into())
                        .collect(),
                )?;
                triggers.push(vir_low::Trigger::new(vec![constructor_call.clone()]));
                for parameter in &parameters {
                    let destructor_call = self.adt_destructor_variant_call(
                        domain_name,
                        destructor_variant_name,
                        &parameter.name,
                        parameter.ty.clone(),
                        constructor_call.clone(),
                    )?;
                    // conjuncts.push(expr! { [destructor_call] == parameter });
                    let axiom = vir_low::DomainRewriteRuleDecl {
                        comment: None,
                        name: format!(
                            "{constructor_name}$bottom_up_injectivity_axiom${}",
                            parameter.name
                        ),
                        egg_only: false,
                        variables: parameters.clone(),
                        triggers: Some(triggers.clone()),
                        source: destructor_call,
                        target: parameter.clone().into(),
                    };
                    self.declare_rewrite_rule(domain_name, axiom)?;
                }
                // let body = vir_low::Expression::forall(
                //     parameters.clone(),
                //     triggers,
                //     conjuncts.into_iter().conjoin(),
                // );
                // let axiom = vir_low::DomainAxiomDecl {
                //     comment: None,
                //     name: format!("{constructor_name}$bottom_up_injectivity_axiom"),
                //     body,
                // };
                // self.declare_axiom(domain_name, axiom)?;
            }

            // Top-down injectivity axiom.

            var_decls! { value: {ty.clone()} };
            let (trigger_guard, guard) = if let Some(guard_constructor) = top_down_injectivity_guard
            {
                let (trigger, guard) = guard_constructor(domain_name, &value)?;
                (Some(trigger), Some(guard))
            } else {
                (None, None)
            };
            let mut triggers = Vec::new();
            let mut arguments = Vec::new();
            for parameter in &parameters {
                let destructor_call = self.adt_destructor_variant_call(
                    domain_name,
                    destructor_variant_name,
                    &parameter.name,
                    parameter.ty.clone(),
                    value.clone().into(),
                )?;
                if let Some(guard) = &trigger_guard {
                    let mut terms = vec![guard.clone()];
                    if parameters.len() != 1 {
                        terms.push(destructor_call.clone());
                    }
                    triggers.push(vir_low::Trigger::new(terms));
                } else {
                    unimplemented!("figure out what triggers to choose to avoid matching loop!");
                }
                arguments.push(destructor_call);
            }
            let constructor_call =
                self.adt_constructor_variant_call(domain_name, variant_name, arguments)?;
            if parameters.is_empty() {
                if let Some(guard) = &trigger_guard {
                    triggers.push(vir_low::Trigger::new(vec![guard.clone()]));
                } else {
                    unimplemented!("figure out what triggers to choose!");
                }
            }
            if !config::use_snapshot_parameters_in_predicates() && !parameters.is_empty() {
                triggers.push(vir_low::Trigger::new(vec![constructor_call.clone()]));
            }
            let equality = expr! { value == [constructor_call] };
            let forall_body = if let Some(guard) = guard {
                expr! { [guard] ==> [equality] }
            } else {
                equality
            };
            assert!(
                !triggers.is_empty(),
                "empty triggers for {constructor_name}"
            );
            let axiom = vir_low::DomainAxiomDecl {
                comment: None,
                name: format!("{constructor_name}$top_down_injectivity_axiom"),
                body: vir_low::Expression::forall(vec![value], triggers, forall_body),
            };
            self.declare_axiom(domain_name, axiom)?;
        } else {
            assert!(
                top_down_injectivity_guard.is_none(),
                "top-down injectivity guard is Some while generate_injectivity_axioms is false"
            );
        }

        // Snapshot equality axioms.
        {
            use vir_low::macros::*;
            var_decls! { left: {ty.clone()}, right: {ty} };
            let gas = self.function_gas_parameter()?;
            let gas_succ = self.add_function_gas_level(gas.clone().into())?;
            let snapshot_equality_call_gas = self.adt_snapshot_equality_variant_call(
                domain_name,
                variant_name,
                left.clone().into(),
                right.clone().into(),
                gas.clone().into(),
            )?;
            let snapshot_equality_call_gas_succ = self.adt_snapshot_equality_variant_call(
                domain_name,
                variant_name,
                left.clone().into(),
                right.clone().into(),
                gas_succ,
            )?;
            let snapshot_equality_def = if parameters.is_empty() {
                true.into()
            } else {
                let mut parameter_equalities = Vec::new();
                for parameter in &parameters {
                    let destructor_call_left = self.adt_destructor_variant_call(
                        domain_name,
                        destructor_variant_name,
                        &parameter.name,
                        parameter.ty.clone(),
                        left.clone().into(),
                    )?;
                    let destructor_call_right = self.adt_destructor_variant_call(
                        domain_name,
                        destructor_variant_name,
                        &parameter.name,
                        parameter.ty.clone(),
                        right.clone().into(),
                    )?;
                    parameter_equalities.push(expr! {
                        [destructor_call_left] == [destructor_call_right]
                    });
                }
                expr! {
                    ([snapshot_equality_call_gas.clone()]
                    ==
                    [parameter_equalities.into_iter().conjoin()])
                }
            };
            let axiom = vir_low::DomainAxiomDecl {
                comment: Some(
                    "Used to trigger extensionality for snapshots that contain Viper sequences."
                        .to_string(),
                ),
                name: format!("{constructor_name}$snapshot_equality_axiom"),
                body: vir_low::Expression::forall(
                    vec![left.clone(), right.clone(), gas],
                    vec![vir_low::Trigger::new(vec![
                        snapshot_equality_call_gas_succ.clone()
                    ])],
                    expr![
                        ([snapshot_equality_call_gas.clone()] == [snapshot_equality_call_gas_succ])
                            && (([snapshot_equality_call_gas] == (left == right))
                                && [snapshot_equality_def])
                    ],
                ),
            };
            self.declare_axiom(domain_name, axiom)?;
        }

        Ok(())
    }
}
