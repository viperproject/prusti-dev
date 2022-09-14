use super::language::ExpressionLanguage;

pub(super) struct RuleApplier {
    source: egg::PatternAst<ExpressionLanguage>,
    target: egg::PatternAst<ExpressionLanguage>,
}

impl RuleApplier {
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
    }
}
