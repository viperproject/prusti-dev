use crate::encoder::middle::core_proof::svirpti::smt::SmtSolverError;

use super::{
    super::super::transformations::{
        encoder_context::EncoderContext, symbolic_execution_new::ProgramContext,
    },
    configuration::Configuration,
    errors::SmtSolverResult,
    expressions::Expr2SmtWrap,
    parser::SmtParser,
};
use prusti_common::Stopwatch;
use rsmt2::{print::Sort2Smt, Solver};
use rustc_hash::{FxHashMap, FxHashSet};
use vir_crate::{
    common::expression::BinaryOperationHelpers,
    low::{
        self as vir_low,
        expression::visitors::{default_fallible_walk_expression, ExpressionFallibleWalker},
    },
};

#[derive(Debug, PartialEq, Eq)]
pub enum SatResult {
    Unsat,
    Unknown,
    Sat,
}

impl SatResult {
    pub fn is_sat(&self) -> bool {
        matches!(self, SatResult::Sat)
    }
    pub fn is_unsat(&self) -> bool {
        matches!(self, SatResult::Unsat)
    }
    pub fn is_sat_or_unknown(&self) -> bool {
        matches!(self, SatResult::Sat | SatResult::Unknown)
    }
}

pub struct Info<'a, 'c, EC: EncoderContext> {
    pub(in super::super) program_context: &'a ProgramContext<'c, EC>,
}

impl<'a, 'c, EC: EncoderContext> Clone for Info<'a, 'c, EC> {
    fn clone(&self) -> Self {
        Self {
            program_context: self.program_context,
        }
    }
}

impl<'a, 'c, EC: EncoderContext> Copy for Info<'a, 'c, EC> {}

pub struct SmtSolver {
    check_sat_counter: u64,
    solver: Solver<SmtParser>,
    /// Triggerring function name → Vec<(trigger, quantifier)>
    axiom_quantifiers: FxHashMap<String, Vec<(vir_low::Expression, vir_low::Quantifier)>>,
    matched_terms: FxHashSet<vir_low::Expression>,
}

impl SmtSolver {
    pub fn new(conf: Configuration) -> SmtSolverResult<Self> {
        let parser = SmtParser {};
        let mut solver = Solver::new(conf.smt_conf, parser)?;
        if let Some(tee_path) = conf.tee_path {
            solver.path_tee(tee_path).unwrap();
        }
        for attribute in &conf.attributes {
            solver.set_info(attribute)?;
        }
        for (option, value) in &conf.options {
            solver.set_option(option, value)?;
        }
        Ok(Self {
            solver,
            check_sat_counter: 0,
            axiom_quantifiers: Default::default(),
            matched_terms: Default::default(),
        })
    }
    /// Add an axiom to be automatically instantiated.
    pub fn add_axiom(&mut self, axiom: vir_low::DomainAxiomDecl) -> SmtSolverResult<bool> {
        eprintln!("axiom: {axiom}");
        match axiom.body {
            vir_low::Expression::Quantifier(mut quantifier) => {
                for mut trigger in std::mem::take(&mut quantifier.triggers) {
                    if trigger.terms.len() != 1 {
                        return Ok(false);
                    }
                    match &trigger.terms[0] {
                        vir_low::Expression::DomainFuncApp(vir_low::DomainFuncApp {
                            function_name,
                            ..
                        }) => {
                            let entry = self
                                .axiom_quantifiers
                                .entry(function_name.clone())
                                .or_default();
                            entry.push((trigger.terms.pop().unwrap(), quantifier.clone()));
                        }
                        _ => unimplemented!(),
                    }
                }
                return Ok(true);
            }
            vir_low::Expression::DomainFuncApp(_) => {
                return Ok(false);
            }
            vir_low::Expression::BinaryOp(vir_low::BinaryOp {
                op_kind: vir_low::BinaryOpKind::EqCmp,
                ..
            }) => {
                return Ok(false);
            }
            _ => unimplemented!(),
        }
        unreachable!();
    }
    /// We cannot use the `Default` trait because this is potentially failing
    /// operation.
    pub fn default() -> SmtSolverResult<Self> {
        Self::new(Default::default())
    }
    pub fn check_sat(&mut self) -> SmtSolverResult<SatResult> {
        self.solver
            .comment(&format!("Check-sat id: {}", self.check_sat_counter))
            .unwrap();
        self.check_sat_counter += 1;
        let stopwatch = Stopwatch::start("svirpti", "check-sat");
        let result = match self.solver.check_sat_or_unk()? {
            Some(true) => SatResult::Sat,
            Some(false) => SatResult::Unsat,
            None => SatResult::Unknown,
        };
        let duration = stopwatch.finish();
        self.solver
            .comment(&format!("Check-sat duration: {:?}", duration))?;
        Ok(result)
    }
    pub fn push(&mut self) -> SmtSolverResult<()> {
        self.solver.push(1)?;
        Ok(())
    }
    pub fn pop(&mut self) -> SmtSolverResult<()> {
        self.solver.pop(1)?;
        Ok(())
    }
    pub fn declare_sort(&mut self, sort: &str) -> SmtSolverResult<()> {
        self.solver.declare_sort(sort, 0)?;
        Ok(())
    }
    pub fn declare_variable<Sort>(&mut self, name: &str, sort: Sort) -> SmtSolverResult<()>
    where
        Sort: Sort2Smt,
    {
        self.solver.declare_const(name, sort)?;
        Ok(())
    }
    pub fn declare_function<ParameterSorts, ResultSort>(
        &mut self,
        domain_name: &str,
        function_name: &str,
        parameter_types: ParameterSorts,
        result_type: ResultSort,
    ) -> SmtSolverResult<()>
    where
        ParameterSorts: IntoIterator,
        ParameterSorts::Item: Sort2Smt,
        ResultSort: Sort2Smt,
    {
        let full_function_name = format!("{domain_name}@{function_name}");
        self.solver
            .declare_fun(full_function_name, parameter_types, result_type)?;
        Ok(())
    }
    pub fn comment(&mut self, comment: &str) -> SmtSolverResult<()> {
        self.solver.comment(comment)?;
        Ok(())
    }
    pub fn assert<'a, 'c, EC: EncoderContext>(
        &mut self,
        assertion: &vir_low::Expression,
        info: Info<'a, 'c, EC>,
    ) -> SmtSolverResult<()> {
        self.trigger_axioms(assertion, info)?;
        self.solver.assert_with(assertion.wrap(), info)?;
        Ok(())
    }
    fn trigger_axioms<'a, 'c, EC: EncoderContext>(
        &mut self,
        assertion: &vir_low::Expression,
        info: Info<'a, 'c, EC>,
    ) -> SmtSolverResult<()> {
        struct Instantiator<'a, 'c, EC: EncoderContext> {
            solver: &'a mut SmtSolver,
            info: Info<'a, 'c, EC>,
        }
        fn try_match<'a>(
            expression: &'a vir_low::Expression,
            trigger: &'a vir_low::Expression,
            replacements: &mut FxHashMap<&'a vir_low::VariableDecl, &'a vir_low::Expression>,
        ) -> bool {
            match (expression, trigger) {
                (_, vir_low::Expression::Local(local)) => {
                    assert!(replacements.insert(&local.variable, expression).is_none());
                    true
                }
                (
                    vir_low::Expression::DomainFuncApp(app1),
                    vir_low::Expression::DomainFuncApp(app2),
                ) if app1.domain_name == app2.domain_name
                    && app1.function_name == app2.function_name =>
                {
                    for (arg1, arg2) in app1.arguments.iter().zip(app2.arguments.iter()) {
                        if !try_match(arg1, arg2, replacements) {
                            return false;
                        }
                    }
                    true
                }
                _ => false,
            }
        }
        impl<'a, 'c, EC: EncoderContext> ExpressionFallibleWalker for Instantiator<'a, 'c, EC> {
            type Error = SmtSolverError;
            fn fallible_walk_expression(
                &mut self,
                expression: &vir_low::Expression,
            ) -> Result<(), Self::Error> {
                match expression {
                    vir_low::Expression::DomainFuncApp(domain_func_app) => {
                        if self.solver.matched_terms.contains(expression) {
                            return Ok(());
                        }
                        let mut assertions = Vec::new();
                        if let Some(quantifiers) = self
                            .solver
                            .axiom_quantifiers
                            .get(&domain_func_app.function_name)
                        {
                            for (trigger, quantifier) in quantifiers {
                                let mut replacements = FxHashMap::default();
                                if try_match(expression, trigger, &mut replacements) {
                                    eprintln!(
                                        "matched:\nexpression: {expression}\ntrigger: {trigger}"
                                    );
                                    eprintln!("quantifier: {quantifier}");
                                    assert_eq!(quantifier.variables.len(), replacements.len());
                                    for variable in &quantifier.variables {
                                        assert!(
                                            replacements.contains_key(variable),
                                            "Missing variable: {variable}"
                                        );
                                    }
                                    let assertion =
                                        quantifier.body.clone().substitute_variables(&replacements);
                                    assertions.push(assertion);
                                } else {
                                    eprintln!(
                                        "unmatched:\nexpression: {expression}\ntrigger: {trigger}"
                                    );
                                    eprintln!("quantifier: {quantifier}");
                                    if domain_func_app.function_name == "valid$Snap$Usize" {
                                        assert_eq!(domain_func_app.arguments.len(), 1);
                                        let argument = &domain_func_app.arguments[0];
                                        let value = vir_low::Expression::domain_function_call(
                                            "Snap$Usize",
                                            "destructor$Snap$Usize$$value",
                                            vec![argument.clone()],
                                            vir_low::Type::Int,
                                        );
                                        let assertion = vir_low::Expression::and(
                                            vir_low::Expression::less_equals(
                                                0.into(),
                                                value.clone(),
                                            ),
                                            vir_low::Expression::less_equals(
                                                value.clone(),
                                                18446744073709551615u64.into(),
                                            ),
                                        );
                                        eprintln!("assertion: {assertion}");
                                        assertions.push(assertion);
                                    }
                                    // assert_ne!(
                                    //     &domain_func_app.function_name,
                                    //     "mul_wrapper$"
                                    // );
                                    // unimplemented!();
                                }
                            }
                        }
                        if !assertions.is_empty() {
                            self.solver.matched_terms.insert(expression.clone());
                        }
                        for assertion in assertions {
                            self.solver.comment("quantifier trigger")?;
                            self.solver.assert(&assertion, self.info)?;
                        }
                    }
                    vir_low::Expression::Quantifier(_) => {
                        // FIXME: In such cases, we should emit axioms to Z3 so
                        // that it can instantiate them itself.
                        return Ok(());
                    }
                    _ => {}
                }
                default_fallible_walk_expression(self, expression)
            }
        }
        let mut instantiator = Instantiator { solver: self, info };
        instantiator.fallible_walk_expression(assertion)?;
        Ok(())
    }
}
