use super::{
    errors::{SpannedEncodingError, SpannedEncodingResult},
    snapshot::interface::SnapshotEncoderInterface,
    Encoder,
};
use crate::encoder::high::types::HighTypeEncoderInterface;
use prusti_common::vir_local;
use prusti_rustc_interface::span::Span;
use rustc_hash::{FxHashMap, FxHashSet};

use vir_crate::{
    common::identifier::WithIdentifier,
    polymorphic::{
        self as vir, compute_identifier, ExprWalker, FallibleExprWalker, FallibleStmtWalker,
        StmtWalker,
    },
};

/// Determining which of the collected functions should have bodies works as
/// follows:
///
/// 1.  Collect all predicates that are unfolded or folded in the method body.
///     This marks how deeply we need to instantiate function definitions (level
///     n).
/// 2.  Collect all functions that are directly called:
///     1.  in the method;
///     2.  in the preconditions or postconditions of functions directly called
///         in the method or whose preconditions contain an unfolded predicate
///         or whose parameter is a snapshot of an unfolded predicate;
///     3.  in the bodies of functions whose preconditions contain an unfolded
///         predicate or whose parameter is a snapshot of an unfolded predicate.
///
/// We include bodies of all predicates which we observed unfolded at any step
/// of the process.
pub(super) fn collect_definitions(
    error_span: Span,
    encoder: &Encoder,
    name: String,
    methods: Vec<vir::CfgMethod>,
) -> SpannedEncodingResult<vir::Program> {
    let mut unfolded_predicate_collector = UnfoldedPredicateCollector {
        unfolded_predicates: Default::default(),
    };
    vir::utils::walk_methods(&methods, &mut unfolded_predicate_collector);
    let mut collector = Collector {
        error_span,
        encoder,
        method_names: methods.iter().map(|method| method.name()).collect(),
        unfolded_predicates: unfolded_predicate_collector.unfolded_predicates,
        new_unfolded_predicates: Default::default(),
        used_predicates: Default::default(),
        used_fields: Default::default(),
        used_domains: Default::default(),
        used_snap_domain_functions: Default::default(),
        used_functions: Default::default(),
        checked_function_contracts: Default::default(),
        used_mirror_functions: Default::default(),
        unfolded_functions: Default::default(),
        directly_called_functions: Default::default(),
        in_directly_calling_state: true,
    };
    collector.walk_methods(&methods)?;
    collector.into_program(name, methods)
}

struct Collector<'p, 'v: 'p, 'tcx: 'v> {
    error_span: Span,
    encoder: &'p Encoder<'v, 'tcx>,
    /// The list of encoded methods for checking that they do not clash with
    /// functions.
    method_names: FxHashSet<String>,
    /// The set of all predicates that are mentioned in the method.
    used_predicates: FxHashSet<vir::Type>,
    /// The set of predicates whose bodies have to be included because they are
    /// unfolded in the method.
    unfolded_predicates: FxHashSet<vir::Type>,
    new_unfolded_predicates: FxHashSet<vir::Type>,
    used_fields: FxHashSet<vir::Field>,
    used_domains: FxHashSet<String>,
    used_snap_domain_functions: FxHashSet<vir::FunctionIdentifier>,
    /// The set of all functions that are mentioned in the method.
    used_functions: FxHashSet<vir::FunctionIdentifier>,
    /// The set of functions whose contracts were already checked.
    checked_function_contracts: FxHashSet<vir::FunctionIdentifier>,
    /// The set of all mirror functions that are mentioned in the method.
    used_mirror_functions: FxHashSet<vir::FunctionIdentifier>,
    /// The set of functions whose bodies have to be included because predicates
    /// in their preconditions are unfolded.
    unfolded_functions: FxHashSet<vir::FunctionIdentifier>,
    /// Functions that are explicitly called in the program.
    directly_called_functions: FxHashSet<vir::FunctionIdentifier>,
    in_directly_calling_state: bool,
}

impl<'p, 'v: 'p, 'tcx: 'v> Collector<'p, 'v, 'tcx> {
    fn into_program(
        mut self,
        name: String,
        methods: Vec<vir::CfgMethod>,
    ) -> SpannedEncodingResult<vir::Program> {
        let functions = self.get_used_functions()?;
        let viper_predicates = self.get_used_predicates()?;
        let domains = self.get_used_domains();
        let fields = self.get_used_fields();
        Ok(vir::Program {
            name,
            domains,
            fields,
            builtin_methods: self.get_all_methods(),
            methods,
            functions,
            viper_predicates,
        })
    }
    fn walk_methods(&mut self, methods: &[vir::CfgMethod]) -> SpannedEncodingResult<()> {
        let mut predicates = Vec::new();
        for name in &self.unfolded_predicates {
            predicates.push(self.encoder.get_viper_predicate(name)?);
        }
        for predicate in &predicates {
            // make sure we include all the fields
            if let Some(body) = predicate.body().as_ref() {
                self.fallible_walk_expr(body)?;
            }
        }
        vir::utils::fallible_walk_methods(methods, self)?;
        self.used_predicates
            .extend(self.unfolded_predicates.iter().cloned());
        self.used_functions
            .extend(self.unfolded_functions.iter().cloned());
        Ok(())
    }
    fn get_used_fields(&self) -> Vec<vir::Field> {
        // TODO: Remove the deduplication once we switch to the offset-based
        // fields.
        let used_fields: FxHashMap<_, _> = self
            .used_fields
            .iter()
            .map(|field| (&field.name, field))
            .collect();
        let mut used_fields: Vec<_> = used_fields.values().map(|&field| field.clone()).collect();
        used_fields.sort_by_cached_key(|f| f.get_identifier());
        used_fields
    }
    /// The purification optimization that is executed after this assumes that
    /// all bodyless methods are present. That is why we are returning all
    /// methods here.
    fn get_all_methods(&self) -> Vec<vir::BodylessMethod> {
        let mut methods: Vec<_> = self
            .encoder
            .get_builtin_methods()
            .values()
            .cloned()
            .collect();
        methods.sort_by_cached_key(|method| method.name.clone());
        methods
    }
    fn get_used_predicates(&mut self) -> SpannedEncodingResult<Vec<vir::Predicate>> {
        let mut predicates = Vec::new();
        let aux_ref = vir::Type::typed_ref("AuxRef");
        for name in &self.used_predicates {
            if name == &aux_ref {
                // This is not a real type
                continue;
            }
            let predicate = self.encoder.get_viper_predicate(name)?;
            let predicate = if !self.unfolded_predicates.contains(name)
                && !self.new_unfolded_predicates.contains(name)
            {
                // The predicate is never unfolded. Make it abstract.
                match predicate {
                    vir::Predicate::Struct(mut predicate) => {
                        predicate.body = None;
                        vir::Predicate::Struct(predicate)
                    }
                    vir::Predicate::Enum(predicate) => {
                        vir::Predicate::Struct(vir::StructPredicate {
                            typ: predicate.typ,
                            this: predicate.this,
                            body: None,
                        })
                    }
                    predicate => predicate,
                }
            } else {
                predicate
            };
            predicates.push(predicate);
        }
        predicates.push(vir::Predicate::Bodyless(
            vir::Type::typed_ref("DeadBorrowToken$"),
            vir_local! { borrow: Int },
        ));
        predicates.sort_by_key(|f| f.get_identifier());
        Ok(predicates)
    }
    fn get_used_functions(&self) -> SpannedEncodingResult<Vec<vir::Function>> {
        let mut functions = Vec::new();
        for identifier in &self.used_functions {
            let function = self.encoder.get_function(identifier)?;
            let mut function = (*function).clone();
            if !self.unfolded_functions.contains(identifier)
                && !self.directly_called_functions.contains(identifier)
            {
                // The function body is not needed.
                if !function.has_constant_body() {
                    // The function body is non-constant, make the function
                    // abstract. (We leave the constant bodies so that they
                    // could be inlined by one of the optimizations.)
                    function.body = None;
                }
            }
            if self.method_names.contains(&function.name) {
                return Err(SpannedEncodingError::internal(
                    format!(
                        "Rust function {} encoded both as a Viper method and function",
                        function.name
                    ),
                    self.error_span,
                ));
            }
            functions.push(function);
        }
        functions.sort_by_cached_key(|f| f.get_identifier());
        Ok(functions)
    }
    fn get_used_domains(&self) -> Vec<vir::Domain> {
        let mut domains: Vec<_> = self
            .used_domains
            .iter()
            .map(|snapshot_name| {
                let mut domain = self.encoder.get_domain(snapshot_name);
                if let Some(predicate_name) = snapshot_name.strip_prefix("Snap$") {
                    // We have a snapshot for some type
                    if !contains(&self.unfolded_predicates, predicate_name)
                        && !contains(&self.new_unfolded_predicates, predicate_name)
                        && !predicate_name.starts_with("Slice$")
                        && !predicate_name.starts_with("Array$")
                    {
                        // The type is never unfolded, so the snapshot could be
                        // abstract (not always, see #738). An exception is the discriminant
                        // function because it can be called on a folded type.
                        // Another exception is when a snap domain function depends
                        // on an axiom, then we should also retain the axiom.
                        let mut used_snap_domain_function_prefixes = vec![];
                        let mut used_snap_domain_constructor = false;
                        domain.functions.retain(|function| {
                            let function_name = function.get_identifier();
                            let prefix = function_name.split("__").next().map(String::from);
                            let is_constructor = function_name.starts_with("cons");
                            if self
                                .used_snap_domain_functions
                                .contains(&function_name.into())
                            {
                                used_snap_domain_function_prefixes.extend(prefix);
                                used_snap_domain_constructor |= is_constructor;
                                true
                            } else {
                                false
                            }
                        });
                        domain.axioms.retain(|axiom| {
                            let used = used_snap_domain_function_prefixes
                                .iter()
                                .any(|prefix| axiom.name.starts_with(prefix));
                            let retain_type_invariant = axiom.name.ends_with("$valid") && used;
                            let retain_injectivity = used_snap_domain_constructor
                                && axiom.name.ends_with("$injectivity");
                            let retain_field_axiom = used_snap_domain_constructor && used;

                            retain_type_invariant || retain_injectivity || retain_field_axiom
                        });
                    }
                }
                domain
            })
            .collect();
        if let Some(mut mirror_domain) = self.encoder.get_mirror_domain() {
            mirror_domain.functions.retain(|function| {
                self.used_mirror_functions
                    .contains(&function.get_identifier().into())
            });
            if !mirror_domain.functions.is_empty() {
                mirror_domain
                    .functions
                    .sort_by_cached_key(|func| func.get_identifier());
                domains.push(mirror_domain);
            }
        }
        domains.sort_by_cached_key(|domain| domain.name.clone());
        domains
    }
    fn contains_unfolded_predicates(&self, exprs: &[vir::Expr]) -> bool {
        let unfolded_predicate_checker = &mut UnfoldedPredicateChecker {
            unfolded_predicates: &self.unfolded_predicates,
            found: false,
        };
        exprs.iter().any(|expr| {
            ExprWalker::walk(unfolded_predicate_checker, expr);
            unfolded_predicate_checker.found
        })
    }
    fn contains_unfolded_parameters(&self, formal_args: &[vir::LocalVar]) -> bool {
        formal_args.iter().any(|parameter| {
            if let vir::Type::Snapshot(snapshot_type) = &parameter.typ {
                let typ = vir::Type::TypedRef(snapshot_type.clone().into());
                self.unfolded_predicates.contains(&typ)
            } else {
                false
            }
        })
    }
}

fn contains(container: &FxHashSet<vir::Type>, predicate_name: &str) -> bool {
    container.iter().any(|typ| typ.name() == predicate_name)
}

impl<'p, 'v: 'p, 'tcx: 'v> FallibleStmtWalker for Collector<'p, 'v, 'tcx> {
    type Error = SpannedEncodingError;
    fn fallible_walk_expr(&mut self, expr: &vir::Expr) -> SpannedEncodingResult<()> {
        FallibleExprWalker::fallible_walk(self, expr)
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> FallibleExprWalker for Collector<'p, 'v, 'tcx> {
    type Error = SpannedEncodingError;
    fn fallible_walk_variant(
        &mut self,
        vir::Variant {
            base,
            variant_index,
            ..
        }: &vir::Variant,
    ) -> SpannedEncodingResult<()> {
        self.used_fields.insert(variant_index.clone());
        FallibleExprWalker::fallible_walk(self, base)?;
        FallibleExprWalker::fallible_walk_type(self, &variant_index.typ)?;
        Ok(())
    }
    fn fallible_walk_field(
        &mut self,
        vir::FieldExpr { base, field, .. }: &vir::FieldExpr,
    ) -> SpannedEncodingResult<()> {
        self.used_fields.insert(field.clone());
        FallibleExprWalker::fallible_walk(self, base)?;
        FallibleExprWalker::fallible_walk_type(self, &field.typ)?;
        Ok(())
    }
    fn fallible_walk_predicate_access_predicate(
        &mut self,
        vir::PredicateAccessPredicate {
            predicate_type,
            argument,
            ..
        }: &vir::PredicateAccessPredicate,
    ) -> SpannedEncodingResult<()> {
        self.used_predicates.insert(predicate_type.clone());
        FallibleExprWalker::fallible_walk(self, argument)
    }
    fn fallible_walk_unfolding(
        &mut self,
        vir::Unfolding {
            predicate: predicate_type,
            arguments,
            base,
            ..
        }: &vir::Unfolding,
    ) -> SpannedEncodingResult<()> {
        if self.new_unfolded_predicates.insert(predicate_type.clone()) {
            let predicate = self.encoder.get_viper_predicate(predicate_type)?;
            // make sure we include all the fields
            if let Some(body) = predicate.body().as_ref() {
                self.fallible_walk_expr(body)?;
            }
        }
        for arg in arguments {
            FallibleExprWalker::fallible_walk(self, arg)?;
        }
        FallibleExprWalker::fallible_walk(self, base)?;
        Ok(())
    }
    fn fallible_walk_func_app(
        &mut self,
        vir::FuncApp {
            function_name,
            type_arguments,
            arguments,
            formal_arguments,
            return_type,
            ..
        }: &vir::FuncApp,
    ) -> SpannedEncodingResult<()> {
        let identifier: vir::FunctionIdentifier =
            compute_identifier(function_name, type_arguments, formal_arguments, return_type).into();
        let should_visit = !self.used_functions.contains(&identifier);
        let should_visit_in_directly_calling_state =
            self.in_directly_calling_state && !self.directly_called_functions.contains(&identifier);
        if should_visit || should_visit_in_directly_calling_state {
            let function = self.encoder.get_function(&identifier)?;
            self.used_functions.insert(identifier.clone());
            if !self.checked_function_contracts.contains(&identifier)
                || (should_visit_in_directly_calling_state && function.body.is_some())
            {
                self.checked_function_contracts.insert(identifier.clone());
                for expr in function.pres.iter().chain(&function.posts) {
                    self.fallible_walk_expr(expr)?;
                }
            }
            let is_unfoldable = self.contains_unfolded_predicates(&function.pres)
                || self.contains_unfolded_parameters(&function.formal_args);
            // TODO: this post-condition check can be removed once verification of Viper functions is disabled,
            // TODO: this is just a temporary fix for https://github.com/viperproject/prusti-dev/issues/770
            // note that for now this is also true for any pure or predicate
            // function because a mirror postcondition is inserted
            let post_conditions_depend_on_result = function.posts.iter().any(|postcondition| {
                postcondition.find(&vir::Expr::from(
                    vir_local! { __result: { function.return_type.clone() } },
                ))
            });
            if self.in_directly_calling_state || is_unfoldable || post_conditions_depend_on_result {
                self.directly_called_functions.insert(identifier.clone());
                self.unfolded_functions.insert(identifier);
                let old_in_directly_calling_state = self.in_directly_calling_state;
                if !is_unfoldable {
                    // The functions called in the body of this function are
                    // directly callable only if this function is unfoldable.
                    self.in_directly_calling_state = false;
                }
                if let Some(body) = &function.body {
                    self.fallible_walk_expr(body)?;
                }
                self.in_directly_calling_state = old_in_directly_calling_state;
            }
        }
        for arg in arguments {
            FallibleExprWalker::fallible_walk(self, arg)?;
        }
        for arg in formal_arguments {
            FallibleExprWalker::fallible_walk_local_var(self, arg)?;
        }
        FallibleExprWalker::fallible_walk_type(self, return_type)?;
        Ok(())
    }
    fn fallible_walk_domain_func_app(
        &mut self,
        vir::DomainFuncApp {
            domain_function,
            arguments,
            ..
        }: &vir::DomainFuncApp,
    ) -> SpannedEncodingResult<()> {
        if domain_function.domain_name.starts_with("Snap$") {
            self.used_snap_domain_functions
                .insert(domain_function.get_identifier().into());
            self.used_domains
                .insert(domain_function.domain_name.clone());
        } else {
            match domain_function.domain_name.as_str() {
                "MirrorDomain" => {
                    // Always included when encoded, do nothing.
                    self.used_mirror_functions
                        .insert(domain_function.get_identifier().into());
                }
                "UnitDomain" => {
                    self.used_domains
                        .insert(domain_function.domain_name.clone());
                }
                name => {
                    unreachable!("Unexpected domain: {}", name);
                }
            }
        }
        for arg in arguments {
            FallibleExprWalker::fallible_walk(self, arg)?;
        }
        for arg in &domain_function.formal_args {
            FallibleExprWalker::fallible_walk_local_var(self, arg)?;
        }
        Ok(())
    }
    fn fallible_walk_type(&mut self, typ: &vir::Type) -> SpannedEncodingResult<()> {
        match typ {
            vir::Type::Seq(vir::SeqType { box typ }) => {
                self.fallible_walk_type(typ)?;
            }
            vir::Type::TypedRef(..) | vir::Type::TypeVar(..) => {
                self.used_predicates.insert(typ.clone());
            }
            vir::Type::Domain(..) => {
                let name = typ.name();
                if name != "UnitDomain" {
                    unreachable!("Unexpected type that is not snapshot: {}", name);
                }
            }
            vir::Type::Snapshot(..) => {
                self.used_domains.insert(format!("Snap${}", typ.name()));
            }
            _ => {}
        }
        Ok(())
    }
}

/// Collects all predicates that are unfolded.
struct UnfoldedPredicateCollector {
    /// The predicates that are explicitly unfolded in the program.
    unfolded_predicates: FxHashSet<vir::Type>,
}

impl StmtWalker for UnfoldedPredicateCollector {
    fn walk_expr(&mut self, expr: &vir::Expr) {
        ExprWalker::walk(self, expr);
    }

    fn walk_fold(
        &mut self,
        vir::Fold {
            predicate,
            arguments,
            ..
        }: &vir::Fold,
    ) {
        self.unfolded_predicates.insert(predicate.clone());
        for arg in arguments {
            self.walk_expr(arg);
        }
    }

    fn walk_unfold(
        &mut self,
        vir::Unfold {
            predicate,
            arguments,
            ..
        }: &vir::Unfold,
    ) {
        self.unfolded_predicates.insert(predicate.clone());
        for arg in arguments {
            self.walk_expr(arg);
        }
    }
}

impl ExprWalker for UnfoldedPredicateCollector {
    fn walk_unfolding(
        &mut self,
        vir::Unfolding {
            predicate,
            arguments,
            base,
            ..
        }: &vir::Unfolding,
    ) {
        self.unfolded_predicates.insert(predicate.clone());
        for arg in arguments {
            ExprWalker::walk(self, arg);
        }
        ExprWalker::walk(self, base);
    }
}

struct UnfoldedPredicateChecker<'a> {
    unfolded_predicates: &'a FxHashSet<vir::Type>,
    found: bool,
}

impl<'a> ExprWalker for UnfoldedPredicateChecker<'a> {
    fn walk_predicate_access_predicate(
        &mut self,
        vir::PredicateAccessPredicate { predicate_type, .. }: &vir::PredicateAccessPredicate,
    ) {
        if self.unfolded_predicates.contains(predicate_type) {
            self.found = true;
        }
    }
}
