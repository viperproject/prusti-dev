use super::common::*;
use crate::{
    environment::{EnvQuery, Environment},
    utils::{has_abstract_predicate_attr, has_prusti_attr},
    PrustiError,
};
use log::debug;
use prusti_rustc_interface::{
    data_structures::fx::{FxHashMap, FxHashSet},
    errors::MultiSpan,
    hir::{
        self as hir,
        def_id::{DefId, LocalDefId},
        intravisit,
    },
    middle::{hir::map::Map, ty::TyCtxt},
    span::Span,
};
use std::slice::Iter;

/// Checks for illegal usages of specification-only items
/// Checks that built-in specification functions, predicates, resources,
/// and obligations are not used outside of specification code
pub struct IllegalSpecOnlyItemsUsageChecker;

impl<'tcx> SpecCheckerStrategy<'tcx> for IllegalSpecOnlyItemsUsageChecker {
    // This check consists of two passes:
    // First pass: Go over the HIR looking for functions originating from
    // obligation!, resource!, or obligation!; collect them so that
    // we can later also report definition spans if we find illegal usages
    // of them
    // Second pass: Go over all non-spec expressions in HIR looking for
    // built-in specification functions, predicates, resources,
    // and obligations -- also reports errors for items that were not
    // collected in the first pass, just without the definition spans

    #[tracing::instrument(
        name = "IllegalSpecOnlyItemsUsageChecker::check",
        level = "debug",
        skip(self, env)
    )]
    fn check(&self, env: &Environment<'tcx>) -> Vec<PrustiError> {
        let collected_items = self.collect_spec_only_items(env.query);
        debug!("Spec-only items: {:?}", collected_items.spec_only_items);
        debug!(
            "Abstract predicates with bodies: {:?}",
            collected_items.abstract_predicate_with_bodies // NOTE: it seems that we collect these abstract predicates with bodies,
                                                           // but we don't do any checks with them
        );
        let illegal_spec_only_usages =
            self.collect_illegal_spec_only_usages(collected_items.spec_only_items, env.query);
        debug!(
            "Illegal spec-only item usages: {:?}",
            illegal_spec_only_usages
        );

        // TODO: check behavioral subtyping of implemented predicates against default implementation

        let illegal_usage_errors = illegal_spec_only_usages
            .into_iter()
            .map(|usage| match usage {
                IllegalSpecOnlyItemUsage::BuiltinFunction(function_name, usage_span) => {
                    PrustiError::incorrect(
                        format!(
                            "using the built-in `{}` in non-specification code is not allowed",
                            function_name
                        ),
                        MultiSpan::from_span(usage_span),
                    )
                }
                IllegalSpecOnlyItemUsage::ByMacroFunction(item_kind, usage_span, def_span) => {
                    PrustiError::incorrect(
                        format!(
                            "using {} in non-specification code is not allowed",
                            item_kind.name_with_article()
                        ),
                        MultiSpan::from_span(usage_span),
                    )
                    .add_note(
                        format!("this is a specification-only {}", item_kind.name()),
                        def_span,
                    )
                }
            });

        illegal_usage_errors.collect()
    }
}

impl IllegalSpecOnlyItemsUsageChecker {
    /// Returns a map of the `DefID`s to the `Span`s of `predicate!`, `resource!`, and `obligation!`
    /// functions found in the first pass.
    fn collect_spec_only_items<'tcx>(
        &self,
        env_query: EnvQuery<'tcx>,
    ) -> CollectSpecOnlyItemsVisitor<'tcx> {
        let mut collect = CollectSpecOnlyItemsVisitor {
            env_query,
            spec_only_items: FxHashMap::default(),
            abstract_predicate_with_bodies: FxHashSet::default(),
        };
        env_query.hir().walk_toplevel_module(&mut collect);
        env_query.hir().walk_attributes(&mut collect);

        collect
    }

    /// Returns all usages of spec-only items in non-spec code.
    fn collect_illegal_spec_only_usages(
        &self,
        spec_only_items: FxHashMap<DefId, (SpecOnlyItemByMacroKind, Span)>,
        env_query: EnvQuery,
    ) -> Vec<IllegalSpecOnlyItemUsage> {
        let mut visit = CheckSpecOnlyItemsVisitor {
            env_query,
            spec_only_items,
            illegal_usages: Vec::new(),
        }
        .wrap_as_visitor();

        env_query.hir().walk_toplevel_module(&mut visit);
        env_query.hir().walk_attributes(&mut visit);

        visit.wrapped.illegal_usages
    }
}

/// The first visitor: collect all function items that represent
/// predicates, resources, or obligations
struct CollectSpecOnlyItemsVisitor<'tcx> {
    env_query: EnvQuery<'tcx>,
    spec_only_items: FxHashMap<DefId, (SpecOnlyItemByMacroKind, Span)>,
    abstract_predicate_with_bodies: FxHashSet<DefId>,
}

impl<'tcx> intravisit::Visitor<'tcx> for CollectSpecOnlyItemsVisitor<'tcx> {
    type Map = Map<'tcx>;
    type NestedFilter = prusti_rustc_interface::middle::hir::nested_filter::All;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.env_query.hir()
    }

    fn visit_fn(
        &mut self,
        fk: intravisit::FnKind<'tcx>,
        fd: &'tcx hir::FnDecl<'tcx>,
        b: hir::BodyId,
        s: Span,
        local_id: LocalDefId,
    ) {
        // collect this fn's DefId if spec-only function
        let attrs = self.env_query.get_local_attributes(local_id);
        for item_kind in SpecOnlyItemByMacroKind::iter_all() {
            if has_prusti_attr(attrs, item_kind.prusti_attribute()) {
                self.spec_only_items
                    .insert(local_id.to_def_id(), (*item_kind, s));
            }
        }

        intravisit::walk_fn(self, fk, fd, b, local_id);
    }

    fn visit_trait_item(&mut self, ti: &'tcx hir::TraitItem<'tcx>) {
        let def_id = ti.owner_id.def_id.to_def_id();
        let attrs = self.env_query.get_local_attributes(ti.owner_id.def_id);

        if has_abstract_predicate_attr(attrs) {
            let span = self.env_query.get_def_span(def_id);
            self.spec_only_items
                .insert(def_id, (SpecOnlyItemByMacroKind::Predicate, span));
        } else if has_prusti_attr(attrs, "pred_spec_id_ref") {
            if let hir::TraitItemKind::Fn(_, hir::TraitFn::Provided(_)) = &ti.kind {
                self.abstract_predicate_with_bodies.insert(def_id);
            }
        }
        // resource and obligation declarations are not allowed in traits (see check in a
        // neighboring module)

        intravisit::walk_trait_item(self, ti);
    }
}

// 'ByMacro' refers to the fact that this spec-only item kind is one of those declared by a
// designated macro (predicate!, resource!, obligation!) as opposed to built-in functions
#[derive(Clone, Copy, Debug)]
enum SpecOnlyItemByMacroKind {
    Predicate,
    Resource,
    Obligation,
}

impl SpecOnlyItemByMacroKind {
    fn iter_all() -> Iter<'static, Self> {
        static ALL_KINDS: [SpecOnlyItemByMacroKind; 3] = [
            SpecOnlyItemByMacroKind::Predicate,
            SpecOnlyItemByMacroKind::Resource,
            SpecOnlyItemByMacroKind::Obligation,
        ];
        ALL_KINDS.iter()
    }

    fn prusti_attribute(&self) -> &'static str {
        match self {
            SpecOnlyItemByMacroKind::Predicate => "pred_spec_id_ref",
            SpecOnlyItemByMacroKind::Resource => "resource",
            SpecOnlyItemByMacroKind::Obligation => "obligation",
        }
    }

    fn name(&self) -> &'static str {
        match self {
            SpecOnlyItemByMacroKind::Predicate => "predicate",
            SpecOnlyItemByMacroKind::Resource => "resource",
            SpecOnlyItemByMacroKind::Obligation => "obligation",
        }
    }

    fn name_with_article(&self) -> &'static str {
        match self {
            SpecOnlyItemByMacroKind::Predicate => "a predicate",
            SpecOnlyItemByMacroKind::Resource => "a resource",
            SpecOnlyItemByMacroKind::Obligation => "an obligation",
        }
    }
}

/// Usage of a spec-only item in non-spec code. Either of a built-in function
/// or of a spec-only function introduced by a designated macro
#[derive(Debug)]
enum IllegalSpecOnlyItemUsage {
    // arguments: builtin function name, span of usage
    BuiltinFunction(String, Span),
    // arguments: item kind, span of usage, span of definition (if found)
    ByMacroFunction(SpecOnlyItemByMacroKind, Span, Option<Span>),
}

/// The second visitor: collect all uses of spec-only functions in non-spec code
struct CheckSpecOnlyItemsVisitor<'tcx> {
    env_query: EnvQuery<'tcx>,
    spec_only_items: FxHashMap<DefId, (SpecOnlyItemByMacroKind, Span)>,
    illegal_usages: Vec<IllegalSpecOnlyItemUsage>,
}

impl<'v, 'tcx: 'v> NonSpecExprVisitor<'tcx> for CheckSpecOnlyItemsVisitor<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.env_query.tcx()
    }

    fn visit_expr(&mut self, ex: &'tcx hir::Expr<'tcx>) {
        let owner_def_id = ex.hir_id.owner.def_id;

        // all the builtin specification functions in prusti_contracts
        // Needs to be updated when more are added!
        static BUILTIN_SPEC_FUNCS: [&str; 6] = [
            "before_expiry",
            "old",
            "forall",
            "exists",
            "snap",
            "snapshot_equality",
        ];

        // General check: The "path" of a spec-only item doesn't appear anywhere
        // (e.g. as in a function call or an argument when we pass the spec-only item to another function)
        if let hir::ExprKind::Path(ref path) = ex.kind {
            if self.env_query.has_body(owner_def_id) {
                let res = self
                    .env_query
                    .tcx()
                    .typeck(owner_def_id)
                    .qpath_res(path, ex.hir_id);
                if let hir::def::Res::Def(_, def_id) = res {
                    if let Some((item_kind, def_span)) = self.spec_only_items.get(&def_id) {
                        self.illegal_usages
                            .push(IllegalSpecOnlyItemUsage::ByMacroFunction(
                                *item_kind,
                                ex.span,
                                Some(*def_span),
                            ));
                    } else {
                        let attributes = self.env_query.get_attributes(def_id);
                        for item_kind in SpecOnlyItemByMacroKind::iter_all() {
                            if has_prusti_attr(attributes, item_kind.prusti_attribute()) {
                                self.illegal_usages.push(
                                    IllegalSpecOnlyItemUsage::ByMacroFunction(
                                        *item_kind, ex.span, None,
                                    ),
                                );
                            }
                        }

                        for builtin in BUILTIN_SPEC_FUNCS.into_iter() {
                            if self.env_query.tcx().def_path_str(def_id)
                                == format!("prusti_contracts::{}", builtin)
                            {
                                self.illegal_usages.push(
                                    IllegalSpecOnlyItemUsage::BuiltinFunction(
                                        builtin.to_string(),
                                        ex.span,
                                    ),
                                );
                            }
                        }
                    }
                }
            }
        }

        // When we deal with predicates in impls, the above path resolving is not enough,
        // i.e. when Foo::bar is a predicate and we call `foo.bar()` on some `foo: Foo`,
        // we do not observe the called def id `bar` via path resolution.
        if self.env_query.has_body(owner_def_id) {
            let resolved_called_method = self
                .env_query
                .tcx()
                .typeck(owner_def_id)
                .type_dependent_def_id(ex.hir_id);
            if let Some(called_def_id) = resolved_called_method {
                if !self.env_query.tcx().is_constructor(called_def_id) {
                    if let Some((item_kind, def_span)) = self.spec_only_items.get(&called_def_id) {
                        self.illegal_usages
                            .push(IllegalSpecOnlyItemUsage::ByMacroFunction(
                                *item_kind,
                                ex.span,
                                Some(*def_span),
                            ));
                    } else {
                        let attributes = self.env_query.get_attributes(called_def_id);
                        if has_prusti_attr(attributes, "pred_spec_id_ref") {
                            self.illegal_usages
                                .push(IllegalSpecOnlyItemUsage::ByMacroFunction(
                                    SpecOnlyItemByMacroKind::Predicate,
                                    ex.span,
                                    None,
                                ));
                        }
                    }
                }
            }
        }
    }
}
