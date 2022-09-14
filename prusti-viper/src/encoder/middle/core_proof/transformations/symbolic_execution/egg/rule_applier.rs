use super::language::ExpressionLanguage;

pub(super) struct RuleApplier {
    // source: egg::Pattern<ExpressionLanguage>, target: egg::Pattern<ExpressionLanguage>,
    source: egg::PatternAst<ExpressionLanguage>,
    target: egg::PatternAst<ExpressionLanguage>,
}

impl RuleApplier {
    // pub(super) fn new(source: egg::Pattern<ExpressionLanguage>, target: egg::Pattern<ExpressionLanguage>) -> Self {
    pub(super) fn new(
        source: egg::PatternAst<ExpressionLanguage>,
        target: egg::PatternAst<ExpressionLanguage>,
    ) -> Self {
        Self { source, target }
    }
}

impl egg::Applier<ExpressionLanguage, ()> for RuleApplier {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<ExpressionLanguage, ()>,
        _eclass: egg::Id,
        subst: &egg::Subst,
        _searcher_ast: Option<&egg::PatternAst<ExpressionLanguage>>,
        rule_name: egg::Symbol,
    ) -> Vec<egg::Id> {
        let (new_id, unified) =
            egraph.union_instantiations(&self.source, &self.target, subst, rule_name);
        if unified {
            vec![new_id]
        } else {
            Vec::new()
        }
        // let source = self.source.apply_one(egraph, eclass, subst, searcher_ast, rule_name);
        // let target = self.target.apply_one(egraph, eclass, subst, searcher_ast, rule_name);
        // assert_eq!(source.len(), 1);
        // assert_eq!(target.len(), 1);
        // let source = source[0];
        // let target = target[0];
        // let source = egraph.find(source);
        // let target = egraph.find(target);
        // if source == target {
        //     Vec::new()
        // } else {
        //     vec![source, target]
        // }
    }
}
