use self::language::ExpressionLanguage;
use super::consistency_tracker::ConsistencyTracker;
use crate::encoder::{
    errors::{SpannedEncodingError, SpannedEncodingResult},
    middle::core_proof::{
        snapshots::SnapshotDomainInfo,
        transformations::symbolic_execution::egg::{
            rule_applier::RuleApplier, term_interner::TermInterner,
        },
    },
};
use egg::{EGraph, Id, Language};
use rustc_hash::{FxHashMap, FxHashSet};
use std::{collections::BTreeMap, io::Write};
use vir_crate::low::{
    self as vir_low,
    expression::visitors::{default_fallible_walk_expression, ExpressionFallibleWalker},
};

mod language;
mod term_interner;
mod rule_applier;
mod graphviz;

// impl<'a> ProcedureExecutor<'a> {
//     /// Returns true if all arguments are valid terms; that is they are heap
//     /// independent.
//     pub(super) fn check_and_register_terms(
//         &mut self,
//         arguments: &[vir_low::Expression],
//     ) -> SpannedEncodingResult<bool> {
//         let mut all_arguments_heap_independent = true;
//         for argument in arguments {
//             if argument.is_heap_independent() {
//                 self.execution_trace_builder
//                     .current_egraph_state()
//                     .intern_term(argument)?;
//             } else {
//                 all_arguments_heap_independent = false;
//             }
//         }
//         Ok(all_arguments_heap_independent)
//     }
// }

#[derive(Clone)]
pub(super) struct EGraphState {
    egraph: EGraph<ExpressionLanguage, ()>,
    simplification_rules: Vec<egg::Rewrite<ExpressionLanguage, ()>>,
    false_id: Id,
    true_id: Id,
    interned_terms: FxHashMap<vir_low::Expression, Id>,
    consistency_tracker: ConsistencyTracker,
}

impl EGraphState {
    pub(super) fn new(
        domains: &[vir_low::DomainDecl],
        bool_type: vir_low::Type,
        bool_domain_info: SnapshotDomainInfo,
    ) -> SpannedEncodingResult<Self> {
        let mut egraph = EGraph::default();
        let true_id = egraph.add(ExpressionLanguage::True);
        let false_id = egraph.add(ExpressionLanguage::False);
        let mut simplification_rules = Vec::new();
        for domain in domains {
            for rule in &domain.rewrite_rules {
                let mut variables = BTreeMap::new();
                let mut source_pattern_ast: egg::RecExpr<egg::ENodeOrVar<ExpressionLanguage>> =
                    egg::RecExpr::default();
                let true_id =
                    source_pattern_ast.add(egg::ENodeOrVar::ENode(ExpressionLanguage::True));
                let false_id =
                    source_pattern_ast.add(egg::ENodeOrVar::ENode(ExpressionLanguage::False));
                for variable in &rule.variables {
                    let egg_variable: egg::Var = format!("?{}", variable.name).parse().unwrap();
                    let variable_id = source_pattern_ast.add(egg::ENodeOrVar::Var(egg_variable));
                    variables.insert(variable.name.clone(), variable_id);
                }
                let mut target_pattern_ast = source_pattern_ast.clone();
                let mut trigger_pattern = source_pattern_ast.clone();
                source_pattern_ast.intern_pattern(&rule.source, true_id, false_id, &variables)?;
                target_pattern_ast.intern_pattern(&rule.target, true_id, false_id, &variables)?;
                let egg_rule = if let Some(triggers) = &rule.triggers {
                    assert_eq!(
                        triggers.len(),
                        1,
                        "Currently only single term triggers are implemented."
                    );
                    assert_eq!(
                        triggers[0].terms.len(),
                        1,
                        "Currently only single term triggers are implemented."
                    );
                    trigger_pattern.intern_pattern(
                        &triggers[0].terms[0],
                        true_id,
                        false_id,
                        &variables,
                    )?;
                    let trigger_pattern = egg::Pattern::new(trigger_pattern);
                    egg::rewrite!(&rule.name; trigger_pattern => {
                        RuleApplier::new(source_pattern_ast, target_pattern_ast)
                    })
                } else {
                    let source_pattern = egg::Pattern::new(source_pattern_ast);
                    let target_pattern = egg::Pattern::new(target_pattern_ast);
                    egg::rewrite!(&rule.name; source_pattern => target_pattern)
                };
                simplification_rules.push(egg_rule);
            }
        }
        // let rule = {
        //     let place_var: egg::Var = "?place".parse().unwrap();
        //     let address_var: egg::Var = "?address".parse().unwrap();
        //     let mut pattern: egg::RecExpr<egg::ENodeOrVar<ExpressionLanguage>> =
        //         egg::RecExpr::default();
        //     let place = pattern.add(egg::ENodeOrVar::Var(place_var));
        //     let address = pattern.add(egg::ENodeOrVar::Var(address_var));
        //     pattern.add(egg::ENodeOrVar::ENode(ExpressionLanguage::FuncApp(
        //         Symbol::from("compute_address"),
        //         vec![place, address],
        //     )));
        //     let match_pattern = egg::Pattern::new(pattern);
        //     let mut pattern: egg::RecExpr<egg::ENodeOrVar<ExpressionLanguage>> =
        //         egg::RecExpr::default();
        //     pattern.add(egg::ENodeOrVar::Var(address_var));
        //     let target_pattern = egg::Pattern::new(pattern);
        //     egg::rewrite!("evaluate_compute_address"; match_pattern => target_pattern)
        // };
        // let simplification_rules = vec![rule];
        Ok(Self {
            egraph,
            simplification_rules,
            true_id,
            false_id,
            interned_terms: Default::default(),
            consistency_tracker: ConsistencyTracker::new(bool_type, bool_domain_info),
        })
    }

    /// Assume all internable conjuncts. Conjuncts are internable if they are
    /// heap independent and do not contain quantifiers, conditionals, and let
    /// expressions.
    pub(super) fn try_assume_heap_independent_conjuncts(
        &mut self,
        expression: &vir_low::Expression,
    ) -> SpannedEncodingResult<()> {
        if let vir_low::Expression::BinaryOp(binary_expression) = expression {
            match binary_expression.op_kind {
                vir_low::BinaryOpKind::EqCmp => {
                    if expression.is_heap_independent() {
                        self.assume_equal(&binary_expression.left, &binary_expression.right)?;
                        return Ok(());
                    }
                }
                vir_low::BinaryOpKind::And => {
                    self.try_assume_heap_independent_conjuncts(&binary_expression.left)?;
                    self.try_assume_heap_independent_conjuncts(&binary_expression.right)?;
                    return Ok(());
                }
                _ => {}
            }
        }
        if expression.is_heap_independent() {
            self.try_assume(expression)?;
        }
        Ok(())
    }

    pub(super) fn try_intern_heap_independent_conjuncts(
        &mut self,
        expression: &vir_low::Expression,
    ) -> SpannedEncodingResult<()> {
        if let vir_low::Expression::BinaryOp(binary_expression) = expression {
            if let vir_low::BinaryOpKind::And = binary_expression.op_kind {
                self.try_intern_heap_independent_conjuncts(&binary_expression.left)?;
                self.try_intern_heap_independent_conjuncts(&binary_expression.right)?;
                return Ok(());
            }
        }
        if expression.is_heap_independent() {
            self.try_intern_term(expression)?;
        }
        Ok(())
    }

    /// Returns true if any new terms were interned.
    pub(super) fn intern_heap_independent_terms(
        &mut self,
        terms: &[vir_low::Expression],
    ) -> SpannedEncodingResult<bool> {
        let mut newly_interned = false;
        for term in terms {
            if term.is_heap_independent() && self.try_lookup_term(term)?.is_none() {
                self.intern_term(term)?;
                newly_interned = true;
            }
        }
        Ok(newly_interned)
    }

    pub(super) fn intern_heap_independent_subexpressions(
        &mut self,
        expression: &vir_low::Expression,
    ) -> SpannedEncodingResult<()> {
        // eprintln!("intern_heap_independent_subexpressions: {expression}");
        struct Walker<'a> {
            egraph: &'a mut EGraphState,
        }
        impl<'a> ExpressionFallibleWalker for Walker<'a> {
            type Error = SpannedEncodingError;
            fn fallible_walk_trigger(
                &mut self,
                trigger: &vir_low::Trigger,
            ) -> Result<(), Self::Error> {
                for term in &trigger.terms {
                    self.fallible_walk_expression(term)?;
                }
                Ok(())
            }
            fn fallible_walk_expression(
                &mut self,
                expression: &vir_low::Expression,
            ) -> Result<(), Self::Error> {
                if expression.is_heap_independent() {
                    // eprintln!("Try interning: {expression}");
                    self.egraph.try_intern_term(expression)?;
                    // return Ok(()); –  FIXME: We cannot return early here
                    // because `try_intern_term` stores only the id  of the
                    // whole expression, not the ids of its subexpressions.
                }
                default_fallible_walk_expression(self, expression)
            }
        }
        let mut walker = Walker { egraph: self };
        walker.fallible_walk_expression(expression)?;

        // struct Walker2<'a> {
        //     egraph: &'a mut EGraphState,
        // }
        // impl<'a> ExpressionFallibleWalker for Walker2<'a> {
        //     type Error = SpannedEncodingError;
        //     fn fallible_walk_domain_func_app(
        //             &mut self,
        //             domain_func_app: &vir_low::DomainFuncApp,
        //         ) -> Result<(), Self::Error> {
        //         // assert_ne!(domain_func_app.function_name, "constructor$Snap$Usize$Mul_Usize");
        //         // assert_ne!(domain_func_app.function_name, "Size$I32$");
        //         if domain_func_app.function_name == "destructor$Snap$Usize$$value" {
        //             if let vir_low::Expression::DomainFuncApp(domain_func_app2) = &domain_func_app.arguments[0] {
        //                 assert_ne!(domain_func_app2.function_name, "Size$I32$", "{domain_func_app}");
        //             }
        //         }
        //         // assert_ne!(domain_func_app.function_name, "destructor$Snap$Usize$$value", "{domain_func_app}");
        //         vir_low::expression::visitors::default_fallible_walk_domain_func_app(self, domain_func_app)
        //     }
        // }
        // let mut walker = Walker2 {
        //     egraph: self.execution_trace_builder.current_egraph_state(),
        // };
        // walker.fallible_walk_expression(expression)?;

        Ok(())
    }

    pub(super) fn assume(&mut self, term: &vir_low::Expression) -> SpannedEncodingResult<()> {
        self.consistency_tracker.try_assume(term)?;
        let term_id = self.intern_term(term)?;
        self.egraph.union(term_id, self.true_id);
        Ok(())
    }

    fn try_assume(&mut self, term: &vir_low::Expression) -> SpannedEncodingResult<()> {
        self.consistency_tracker.try_assume(term)?;
        if let Some(term_id) = self.try_intern_term(term)? {
            self.egraph.union(term_id, self.true_id);
        }
        Ok(())
    }

    pub(super) fn assume_equal(
        &mut self,
        left: &vir_low::Expression,
        right: &vir_low::Expression,
    ) -> SpannedEncodingResult<()> {
        self.consistency_tracker.try_assume_equal(left, right)?;
        let left_id = self.intern_term(left)?;
        let right_id = self.intern_term(right)?;
        self.egraph.union(left_id, right_id);
        Ok(())
    }

    /// If the graph was modified, `saturate` must be called before `is_equal` can
    /// be used.
    pub(super) fn is_equal(
        &self,
        left: &vir_low::Expression,
        right: &vir_low::Expression,
    ) -> SpannedEncodingResult<bool> {
        let left_id = self.lookup_term(left)?;
        let right_id = self.lookup_term(right)?;
        Ok(self.egraph.find(left_id) == self.egraph.find(right_id))
    }

    pub(super) fn is_true(&self, term: &vir_low::Expression) -> SpannedEncodingResult<bool> {
        let term_id = self.lookup_term(term)?;
        Ok(self.egraph.find(term_id) == self.egraph.find(self.true_id))
    }

    pub(super) fn try_is_true(
        &self,
        term: &vir_low::Expression,
    ) -> SpannedEncodingResult<Option<bool>> {
        if let Some(term_id) = self.try_lookup_term(term)? {
            Ok(Some(
                self.egraph.find(term_id) == self.egraph.find(self.true_id),
            ))
        } else {
            Ok(None)
        }
    }

    /// Check whether the term is known to be a constant.
    ///
    /// Returns:
    ///
    /// * `Some((Some(constructor_name), constant))` if the term is equivalent
    ///   to a given constantat wrapped in the specified constructor.
    /// * `Some(None, constant)` if the term is directly equivalent to a constant.
    /// * `None` if the term is not equivalent to a constant.
    pub(super) fn resolve_constant(
        &self,
        term: &vir_low::Expression,
        constant_constructors: &FxHashSet<String>,
    ) -> SpannedEncodingResult<Option<(Option<String>, vir_low::Expression)>> {
        let Some(id) = self.try_lookup_term(term)? else {
            // eprintln!("not interned: {term}");
            return Ok(None);
        };
        struct PreferConstantsCostFunction<'a> {
            constant_constructors: &'a FxHashSet<String>,
        }
        impl<'a> egg::CostFunction<ExpressionLanguage> for PreferConstantsCostFunction<'a> {
            type Cost = f64;
            fn cost<C>(&mut self, enode: &ExpressionLanguage, mut costs: C) -> Self::Cost
            where
                C: FnMut(Id) -> Self::Cost,
            {
                let op_cost = match enode {
                    ExpressionLanguage::True
                    | ExpressionLanguage::False
                    | ExpressionLanguage::Int(_)
                    | ExpressionLanguage::BigInt(_) => 1.0,
                    ExpressionLanguage::FuncApp(symbol, _)
                    | ExpressionLanguage::BuiltinFuncApp(symbol, _)
                        if self.constant_constructors.contains(symbol.as_str()) =>
                    {
                        2.0
                    }
                    _ => 10.0,
                };
                enode
                    .children()
                    .iter()
                    .fold(op_cost, |sum, id| sum + costs(*id))
            }
        }
        let cost_func = PreferConstantsCostFunction {
            constant_constructors,
        };
        let extractor = egg::Extractor::new(&self.egraph, cost_func);
        let (_best_cost, node) = extractor.find_best(id);
        let last: Id = (node.as_ref().len() - 1).into();
        match &node[last] {
            ExpressionLanguage::FuncApp(name, arguments) if arguments.len() == 1 => {
                match node[arguments[0]] {
                    ExpressionLanguage::Int(constant) => {
                        return Ok(Some((Some(name.to_string()), constant.into())));
                    }
                    ExpressionLanguage::BigInt(_) => todo!(),
                    _ => {}
                }
            }
            ExpressionLanguage::Int(constant) => {
                return Ok(Some((None, (*constant).into())));
            }
            ExpressionLanguage::BigInt(constant) => {
                let constant_value = vir_low::ConstantValue::BigInt(constant.to_string());
                let expression =
                    vir_low::Expression::constant_no_pos(constant_value, vir_low::Type::Int);
                return Ok(Some((None, expression)));
            }
            _ => {}
        }
        Ok(None)
    }

    pub(super) fn saturate(&mut self) -> SpannedEncodingResult<()> {
        self.egraph.rebuild();
        let runner: egg::Runner<_, _, ()> = egg::Runner::new(())
            .with_egraph(std::mem::take(&mut self.egraph))
            // .with_node_limit(200)
            .run(&self.simplification_rules);
        if !(matches!(runner.stop_reason.unwrap(), egg::StopReason::Saturated)) {
            runner
                .egraph
                .dot()
                .to_dot("/tmp/egraph-unsaturated.dot")
                .unwrap();
            panic!("simplification rules did not saturate; see /tmp/egraph-unsaturated.dot");
        }
        self.egraph = runner.egraph;
        Ok(())
    }

    pub(super) fn is_inconsistent(&mut self) -> SpannedEncodingResult<bool> {
        self.consistency_tracker.is_inconsistent()
        // if self.consistency_tracker.is_inconsistent()? {
        //     Ok(true)
        // } else {
        //     // self.egraph.rebuild();
        //     Ok(self.egraph.find(self.true_id) == self.egraph.find(self.false_id))
        // }
    }

    /// Lookup the id of a previously interned term.
    fn lookup_term(&self, term: &vir_low::Expression) -> SpannedEncodingResult<Id> {
        Ok(self.try_lookup_term(term)?.unwrap_or_else(|| {
            panic!("term {term} is not interned");
        }))
    }

    /// Lookup the id of a previously interned term.
    fn try_lookup_term(&self, term: &vir_low::Expression) -> SpannedEncodingResult<Option<Id>> {
        Ok(self.interned_terms.get(term).cloned())
    }

    pub(super) fn intern_term(&mut self, term: &vir_low::Expression) -> SpannedEncodingResult<Id> {
        let id = self.try_intern_term(term)?.unwrap_or_else(|| {
            panic!("term {term} cannot be interned");
        });
        Ok(id)
        // if let Some(id) = self.interned_terms.get(term) {
        //     Ok(*id)
        // } else {
        //     assert!(term.is_heap_independent(), "{term} is heap independent");
        //     let id = self.egraph.intern_term(term, self.true_id, self.false_id)?;
        //     self.interned_terms.insert(term.clone(), id);
        //     Ok(id)
        // }
    }

    pub(super) fn try_intern_term(
        &mut self,
        term: &vir_low::Expression,
    ) -> SpannedEncodingResult<Option<Id>> {
        if let Some(id) = self.interned_terms.get(term) {
            Ok(Some(*id))
        } else {
            assert!(term.is_heap_independent(), "{term} is heap dependent");
            if let Some(id) = self
                .egraph
                .try_intern_term(term, self.true_id, self.false_id)?
            {
                self.interned_terms.insert(term.clone(), id);
                Ok(Some(id))
            } else {
                Ok(None)
            }
        }
    }

    pub(super) fn to_graphviz(&self, writer: &mut dyn Write) -> std::io::Result<()> {
        write!(writer, "{}", self.egraph.dot())
    }

    #[allow(unused)]
    pub(super) fn dump_dot(&self, path: &str) -> SpannedEncodingResult<()> {
        self.egraph.dot().to_dot(path).unwrap();
        Ok(())
    }

    // pub(super) fn get_dump_eclass_of(
    //     &self,
    //     term: &vir_low::Expression,
    // ) -> SpannedEncodingResult<String> {
    //     use std::fmt::Write;
    //     let id = self.lookup_term(term)?;
    //     // if id == 337.into() {
    //     //     println!("eclass of {term}: {id}");
    //     //     for node in &self.egraph[id].nodes {
    //     //         println!("  {node}");
    //     //     }
    //     //     // self.dump_dot("/tmp/egraph-337.dot").unwrap();
    //     //     self.eclass_to_dot_file(id, "/tmp/egraph-337.dot")?;
    //     //     self.eclass_to_dot_file(322.into(), "/tmp/egraph-322.dot")?;
    //     //     self.eclass_to_dot_file(134.into(), "/tmp/egraph-134.dot")?;
    //     //     panic!();
    //     // }
    //     let mut buf = String::new();
    //     writeln!(buf, "//   eclass of {term}: {id}").unwrap();
    //     for node in &self.egraph[id].nodes {
    //         writeln!(buf, "//     {node}").unwrap();
    //     }
    //     Ok(buf)
    // }
}
