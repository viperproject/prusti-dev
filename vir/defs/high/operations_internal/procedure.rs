use super::super::{
    ast::{
        expression::Expression, predicate::visitors::PredicateWalker,
        statement::visitors::StatementWalker,
    },
    cfg::procedure::{BasicBlock, BasicBlockId, ProcedureDecl, Successor},
    visitors::ExpressionWalker,
    Predicate, Quantifier, Statement, Type, VariableDecl,
};
use crate::common::cfg::Cfg;
use std::collections::{BTreeMap, BTreeSet};

impl ProcedureDecl {
    /// Note: The traversal order is undefined.
    pub fn walk<Walker: StatementWalker + ExpressionWalker>(&self, walker: &mut Walker) {
        for block in self.basic_blocks.values() {
            for statement in &block.statements {
                walker.walk_statement(statement);
            }
            match &block.successor {
                Successor::Goto(_) => {}
                Successor::GotoSwitch(targets) => {
                    for (test, _) in targets {
                        ExpressionWalker::walk_expression(walker, test);
                    }
                }
                Successor::NonDetChoice(_, _) => {}
                Successor::Exit => {}
            }
        }
    }
    /// Note: The traversal order is undefined.
    pub fn walk_expressions<Walker: ExpressionWalker>(&self, expression_walker: &mut Walker) {
        struct Delegate<'a, Walker: ExpressionWalker> {
            expression_walker: &'a mut Walker,
        }
        impl<'a, Walker: ExpressionWalker> PredicateWalker for Delegate<'a, Walker> {
            fn walk_expression(&mut self, expression: &Expression) {
                self.expression_walker.walk_expression(expression);
            }
        }
        impl<'a, Walker: ExpressionWalker> StatementWalker for Delegate<'a, Walker> {
            fn walk_expression(&mut self, expression: &Expression) {
                self.expression_walker.walk_expression(expression);
            }
            fn walk_predicate(&mut self, predicate: &Predicate) {
                PredicateWalker::walk_predicate(self, predicate);
            }
        }
        impl<'a, Walker: ExpressionWalker> ExpressionWalker for Delegate<'a, Walker> {}
        let mut statement_walker = Delegate { expression_walker };
        self.walk(&mut statement_walker);
    }
    pub fn collect_locals(&self) -> Vec<VariableDecl> {
        #[derive(Default)]
        struct LocalCollector {
            locals: BTreeMap<String, Type>,
            bound_variables: Vec<BTreeSet<String>>,
        }
        impl ExpressionWalker for LocalCollector {
            fn walk_variable_decl(&mut self, variable: &VariableDecl) {
                if !self
                    .bound_variables
                    .iter()
                    .any(|set| set.contains(&variable.name))
                {
                    self.locals
                        .insert(variable.name.clone(), variable.ty.clone());
                }
            }
            fn walk_quantifier(&mut self, quantifier: &Quantifier) {
                self.bound_variables.push(
                    quantifier
                        .variables
                        .iter()
                        .map(|variable| variable.name.clone())
                        .collect(),
                );
                for trigger in &quantifier.triggers {
                    self.walk_trigger(trigger);
                }
                self.walk_expression(&quantifier.body);
                self.bound_variables.pop();
            }
        }
        let mut collector = LocalCollector::default();
        self.walk_expressions(&mut collector);
        collector
            .locals
            .into_iter()
            .map(|(name, ty)| VariableDecl { name, ty })
            .collect()
    }
    pub fn get_topological_sort(&self) -> Vec<BasicBlockId> {
        if self.basic_blocks.is_empty() {
            Vec::new()
        } else {
            let mut visited: BTreeMap<_, _> = self
                .basic_blocks
                .keys()
                .map(|label| (label.clone(), false))
                .collect();
            let mut topo_sorted = Vec::<BasicBlockId>::with_capacity(self.basic_blocks.len());
            *visited.get_mut(&self.entry).unwrap() = true;
            for label in self.basic_blocks.keys() {
                if !visited[label] {
                    self.topological_sort_impl(&mut visited, &mut topo_sorted, label);
                }
            }
            topo_sorted.push(self.entry.clone());
            topo_sorted.reverse();
            topo_sorted
        }
    }
    fn topological_sort_impl(
        &self,
        visited: &mut BTreeMap<BasicBlockId, bool>,
        topo_sorted: &mut Vec<BasicBlockId>,
        current_label: &BasicBlockId,
    ) {
        assert!(!visited[current_label]);
        *visited.get_mut(current_label).unwrap() = true;
        let current_block = &self.basic_blocks[current_label];
        for block_index in current_block.successor.get_following() {
            if !visited[block_index] {
                self.topological_sort_impl(visited, topo_sorted, block_index);
            }
        }
        topo_sorted.push(current_label.clone())
    }
    /// To know which trace was taken to reach a specific basic block, we
    /// sometimes keep a record of visited blocks. However, this method fails if
    /// one trace is a strict subset of another trace. This, for example,
    /// happens in the following CFG:
    /// ```ignore
    /// bb1 {
    ///   visited_bb1 := true;
    ///   switch bb2, bb3;
    /// }
    /// bb2 {
    ///   visited_bb2 := true;
    ///   goto bb3;
    /// }
    /// bb3 {
    /// }
    /// ```
    /// In block bb3, if we check `visited_bb1` we still do not know whether we
    /// visited bb2. For this, we need to check `visited_bb2` flag.
    ///
    /// This method returns a list of flags that need to be negated in case we
    /// want to be sure that we taken `(from, to)` edge. For example, for `(bb1,
    /// bb3)` this map will contain the entry `bb2`.
    pub fn get_path_disambiguators(
        &self,
    ) -> BTreeMap<(BasicBlockId, BasicBlockId), Vec<BasicBlockId>> {
        let traversal_order = self.get_topological_sort();

        // A set of blocks that we visited before coming to a specific block.
        let mut visited_block_map: BTreeMap<_, BTreeSet<_>> = BTreeMap::new();
        for block in &traversal_order {
            let mut visited_blocks = visited_block_map.get(block).cloned().unwrap_or_default();
            visited_blocks.insert(block.clone());
            for successor in self.basic_blocks[block].successor.get_following() {
                visited_block_map.insert(successor.clone(), visited_blocks.clone());
            }
        }

        let predecessors = self.predecessors();
        let mut result: BTreeMap<_, Vec<_>> = BTreeMap::new();
        for to in traversal_order {
            for &from in &predecessors[&to] {
                for &potentially_ambiguous_from in &predecessors[&to] {
                    if let Some(visited_blocks) = visited_block_map.get(potentially_ambiguous_from)
                    {
                        if visited_blocks.contains(from) {
                            let entry = result.entry((from.clone(), to.clone())).or_default();
                            entry.push(potentially_ambiguous_from.clone());
                        }
                    }
                }
            }
        }

        result
    }
}

impl Cfg for ProcedureDecl {
    type BasicBlockId = BasicBlockId;
    type BasicBlock = BasicBlock;
    type Statement = Statement;
    type BasicBlockIdIterator<'a> =
        std::collections::btree_map::Keys<'a, Self::BasicBlockId, Self::BasicBlock>;

    fn get_basic_block(&self, bb: &Self::BasicBlockId) -> Option<&Self::BasicBlock> {
        self.basic_blocks.get(bb)
    }

    fn get_basic_block_statement<'a>(
        &'a self,
        block: &'a Self::BasicBlock,
        statement_index: usize,
    ) -> Option<&'a Self::Statement> {
        block.statements.get(statement_index)
    }

    fn iter_basic_block_ids(&self) -> Self::BasicBlockIdIterator<'_> {
        self.basic_blocks.keys()
    }

    fn successors(&self, bb: &Self::BasicBlockId) -> Vec<&Self::BasicBlockId> {
        self.basic_blocks[bb].successor.get_following()
    }
}
