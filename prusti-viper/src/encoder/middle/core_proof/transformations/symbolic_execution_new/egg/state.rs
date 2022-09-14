use super::{language::ExpressionLanguage, rule_applier::RuleApplier, term_interner::TermInterner};
use crate::encoder::{
    errors::{SpannedEncodingError, SpannedEncodingResult},
    middle::core_proof::snapshots::SnapshotDomainInfo,
};
use egg::{EGraph, Id, Language};
use rustc_hash::{FxHashMap, FxHashSet};
use std::{collections::BTreeMap, io::Write};
use vir_crate::low::{
    self as vir_low,
    expression::visitors::{default_fallible_walk_expression, ExpressionFallibleWalker},
};

#[derive(Clone)]
pub(in super::super) struct EGraphState {
    pub(super) egraph: EGraph<ExpressionLanguage, ()>,
    pub(super) simplification_rules: Vec<egg::Rewrite<ExpressionLanguage, ()>>,
    pub(super) false_id: Id,
    pub(super) true_id: Id,
    pub(super) non_aliased_address_id: Id,
}

impl EGraphState {
    pub(in super::super) fn new(
        domains: &[vir_low::DomainDecl],
        bool_type: vir_low::Type,
        bool_domain_info: SnapshotDomainInfo,
    ) -> SpannedEncodingResult<Self> {
        let mut egraph = EGraph::default().with_explanations_enabled();
        let true_id = egraph.add(ExpressionLanguage::True);
        let false_id = egraph.add(ExpressionLanguage::False);
        let non_aliased_address_id = egraph.add(ExpressionLanguage::NonAliasedAddress);
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
        Ok(Self {
            egraph,
            simplification_rules,
            true_id,
            false_id,
            non_aliased_address_id,
        })
    }

    pub(in super::super) fn merge_in(&mut self, other: &EGraphState) -> SpannedEncodingResult<()> {
        self.egraph.egraph_union(&other.egraph);
        Ok(())
    }

    pub(in super::super) fn intersect_with(
        &mut self,
        other: &EGraphState,
    ) -> SpannedEncodingResult<()> {
        let new_egraph = self
            .egraph
            .egraph_intersect(&other.egraph, self.egraph.analysis);
        let old_egraph = std::mem::replace(&mut self.egraph, new_egraph);
        Ok(())
    }

    pub(in super::super) fn assume_equal(
        &mut self,
        left_id: Id,
        right_id: Id,
    ) -> SpannedEncodingResult<()> {
        self.egraph.union(left_id, right_id);
        Ok(())
    }

    /// If the graph was modified, `saturate` must be called before `is_equal` can
    /// be used.
    pub(in super::super) fn is_equal(
        &self,
        left_id: Id,
        right_id: Id,
    ) -> SpannedEncodingResult<bool> {
        Ok(self.egraph.find(left_id) == self.egraph.find(right_id))
    }

    /// Check whether the term is known to be a constant.
    ///
    /// Returns:
    ///
    /// * `Some((Some(constructor_name), constant))` if the term is equivalent
    ///   to a given constantat wrapped in the specified constructor.
    /// * `Some(None, constant)` if the term is directly equivalent to a constant.
    /// * `None` if the term is not equivalent to a constant.
    pub(in super::super) fn resolve_constant(
        &self,
        expression_id: Id,
        constant_constructors: &FxHashSet<String>,
    ) -> SpannedEncodingResult<Option<(Option<String>, vir_low::Expression)>> {
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
        let (_best_cost, node) = extractor.find_best(expression_id);
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

    pub(in super::super) fn saturate(&mut self) -> SpannedEncodingResult<()> {
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

    pub(in super::super) fn try_intern_term(
        &mut self,
        term: &vir_low::Expression,
    ) -> SpannedEncodingResult<Option<Id>> {
        self.egraph
            .try_intern_term(term, self.true_id, self.false_id)
    }
}
