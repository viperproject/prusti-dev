use std::{
    collections::{HashMap, HashSet},
    hash::Hash,
};

use vir_crate::{vir_local, vir_type};
use vir_crate::polymorphic::{self as polymorphic_vir, compute_identifier, ExprWalker, FunctionIdentifier, StmtWalker, WithIdentifier};

use super::Encoder;

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
    encoder: &Encoder,
    name: String,
    methods: Vec<polymorphic_vir::CfgMethod>,
) -> polymorphic_vir::Program {
    let mut unfolded_predicate_collector = UnfoldedPredicateCollector {
        unfolded_predicates: Default::default(),
    };
    polymorphic_vir::utils::walk_methods(&methods, &mut unfolded_predicate_collector);
    let mut collector = Collector {
        encoder,
        method_names: methods.iter().map(|method| method.name()).collect(),
        unfolded_predicates: unfolded_predicate_collector.unfolded_predicates,
        new_unfolded_predicates: Default::default(),
        used_predicates: Default::default(),
        used_fields: Default::default(),
        used_domains: Default::default(),
        used_snap_domain_functions: Default::default(),
        used_functions: Default::default(),
        used_mirror_functions: Default::default(),
        unfolded_functions: Default::default(),
        directly_called_functions: Default::default(),
        in_directly_calling_state: true,
    };
    collector.walk_methods(&methods);
    collector.into_program(name, methods)
}

struct Collector<'p, 'v: 'p, 'tcx: 'v> {
    encoder: &'p Encoder<'v, 'tcx>,
    /// The list of encoded methods for checking that they do not clash with
    /// functions.
    method_names: HashSet<String>,
    /// The set of all predicates that are mentioned in the method.
    used_predicates: HashSet<String>,
    /// The set of predicates whose bodies have to be included because they are
    /// unfolded in the method.
    unfolded_predicates: HashSet<String>,
    new_unfolded_predicates: HashSet<String>,
    used_fields: HashSet<polymorphic_vir::Field>,
    used_domains: HashSet<String>,
    used_snap_domain_functions: HashSet<polymorphic_vir::FunctionIdentifier>,
    /// The set of all functions that are mentioned in the method.
    used_functions: HashSet<polymorphic_vir::FunctionIdentifier>,
    /// The set of all mirror functions that are mentioned in the method.
    used_mirror_functions: HashSet<polymorphic_vir::FunctionIdentifier>,
    /// The set of functions whose bodies have to be included because predicates
    /// in their preconditions are unfolded.
    unfolded_functions: HashSet<polymorphic_vir::FunctionIdentifier>,
    /// Functions that are explicitly called in the program.
    directly_called_functions: HashSet<polymorphic_vir::FunctionIdentifier>,
    in_directly_calling_state: bool,
}

impl<'p, 'v: 'p, 'tcx: 'v> Collector<'p, 'v, 'tcx> {
    fn into_program(mut self, name: String, methods: Vec<polymorphic_vir::CfgMethod>) -> polymorphic_vir::Program {
        let functions = self.get_used_functions();
        let viper_predicates = self.get_used_predicates();
        let domains = self.get_used_domains();
        let fields = self.get_used_fields();
        polymorphic_vir::Program {
            name,
            domains,
            fields,
            builtin_methods: self.get_all_methods(),
            methods,
            functions,
            viper_predicates,
        }
    }
    fn walk_methods(&mut self, methods: &[polymorphic_vir::CfgMethod]) {
        let predicates: Vec<_> = self
            .unfolded_predicates
            .iter()
            .map(|name| self.encoder.get_viper_predicate(name))
            .collect();
        for predicate in &predicates {
            // make sure we include all the fields
            predicate.body().as_ref().map(|body| self.walk_expr(body));
        }
        polymorphic_vir::utils::walk_methods(&methods, self);
        self.used_predicates
            .extend(self.unfolded_predicates.iter().cloned());
        self.used_functions
            .extend(self.unfolded_functions.iter().cloned());
    }
    fn get_used_fields(&self) -> Vec<polymorphic_vir::Field> {
        // TODO: Remove the deduplication once we switch to the offset-based
        // fields.
        let used_fields: HashMap<_, _> = self.used_fields.iter().map(|field| {
            (&field.name, field)
        }).collect();
        used_fields.values().map(|&field| field.clone()).collect()
    }
    /// The purification optimization that is executed after this assumes that
    /// all bodyless methods are present. That is why we are returning all
    /// methods here.
    fn get_all_methods(&self) -> Vec<polymorphic_vir::BodylessMethod> {
        self.encoder
            .get_builtin_methods()
            .values()
            .cloned()
            .collect()
    }
    fn get_used_predicates(&mut self) -> Vec<polymorphic_vir::Predicate> {
        let mut predicates: Vec<_> = self
            .used_predicates
            .iter()
            .filter(|name| {
                *name != "AuxRef" // This is not a real type
            })
            .map(|name| {
                let predicate = self.encoder.get_viper_predicate(name);
                if !self.unfolded_predicates.contains(name)
                    && !self.new_unfolded_predicates.contains(name)
                {
                    // The predicate is never unfolded. Make it abstract.
                    match predicate {
                        polymorphic_vir::Predicate::Struct(mut predicate) => {
                            predicate.body = None;
                            polymorphic_vir::Predicate::Struct(predicate)
                        }
                        polymorphic_vir::Predicate::Enum(predicate) => {
                            polymorphic_vir::Predicate::Struct(polymorphic_vir::StructPredicate {
                                typ: predicate.typ,
                                this: predicate.this,
                                body: None,
                            })
                        }
                        predicate => predicate,
                    }
                } else {
                    predicate
                }
            })
            .chain(Some(polymorphic_vir::Predicate::Bodyless(
                "DeadBorrowToken$".to_string(),
                vir_local! { borrow: Int },
            )))
            .collect();
        predicates.sort_by_key(|f| f.get_identifier());
        predicates
    }
    fn get_used_functions(&self) -> Vec<polymorphic_vir::Function> {
        let mut functions: Vec<_> = self
            .used_functions
            .iter()
            .map(|identifier| {
                let mut function = self.encoder.get_function(identifier).clone();
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
                assert!(
                    !self.method_names.contains(&function.name),
                    "same Rust function encoded as both Viper method and function"
                );
                function
            })
            .collect();
        functions.sort_by_cached_key(|f| f.get_identifier());
        functions
    }
    fn get_used_domains(&self) -> Vec<polymorphic_vir::Domain> {
        let mut domains: Vec<_> = self
            .used_domains
            .iter()
            .map(|snapshot_name| {
                let mut domain = self.encoder.get_domain(snapshot_name);
                if let Some(predicate_name) = snapshot_name.strip_prefix("Snap$") {
                    // We have a snapshot for some type.
                    if !self.unfolded_predicates.contains(predicate_name)
                        && !self.new_unfolded_predicates.contains(predicate_name)
                        && !predicate_name.starts_with("Slice$")
                        && !predicate_name.starts_with("Array$")
                    {
                        // The type is never unfolded, so the snapshot should be
                        // abstract. The only exception is the discriminant function
                        // because it can be called on a folded type.
                        domain.axioms.clear();
                        domain.functions.retain(|function| {
                            self.used_snap_domain_functions
                                .contains(&function.get_identifier().into())
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
            domains.push(mirror_domain);
        }
        domains.sort_by_cached_key(|domain| domain.name.clone());
        domains
    }
    fn contains_unfolded_predicates(&self, exprs: &[polymorphic_vir::Expr]) -> bool {
        let unfolded_predicate_checker = &mut UnfoldedPredicateChecker {
            unfolded_predicates: &self.unfolded_predicates,
            found: false,
        };
        exprs.iter().any(|expr| {
            ExprWalker::walk(unfolded_predicate_checker, expr);
            unfolded_predicate_checker.found
        })
    }
    fn contains_unfolded_parameters(&self, formal_args: &[polymorphic_vir::LocalVar]) -> bool {
        formal_args.iter().any(|parameter| {
            if let polymorphic_vir::Type::Snapshot(..) = &parameter.typ {
                self.unfolded_predicates.contains(&parameter.typ.name())
            } else {
                false
            }
        })
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> StmtWalker for Collector<'p, 'v, 'tcx> {
    fn walk_expr(&mut self, expr: &polymorphic_vir::Expr) {
        ExprWalker::walk(self, expr);
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> ExprWalker for Collector<'p, 'v, 'tcx> {
    fn walk_variant(&mut self, base: &polymorphic_vir::Expr, variant: &polymorphic_vir::Field, _pos: &polymorphic_vir::Position) {
        self.used_fields.insert(variant.clone());
        ExprWalker::walk(self, base);
        ExprWalker::walk_type(self, &variant.typ);
    }
    fn walk_field(&mut self, receiver: &polymorphic_vir::Expr, field: &polymorphic_vir::Field, _pos: &polymorphic_vir::Position) {
        self.used_fields.insert(field.clone());
        ExprWalker::walk(self, receiver);
        ExprWalker::walk_type(self, &field.typ);
    }
    fn walk_predicate_access_predicate(
        &mut self,
        typ: &polymorphic_vir::Type,
        arg: &polymorphic_vir::Expr,
        _perm_amount: polymorphic_vir::PermAmount,
        _pos: &polymorphic_vir::Position,
    ) {
        self.used_predicates.insert(typ.name());
        ExprWalker::walk(self, arg)
    }
    fn walk_unfolding(
        &mut self,
        name: &str,
        args: &Vec<polymorphic_vir::Expr>,
        body: &polymorphic_vir::Expr,
        _perm: polymorphic_vir::PermAmount,
        _variant: &polymorphic_vir::MaybeEnumVariantIndex,
        _pos: &polymorphic_vir::Position,
    ) {
        if self.new_unfolded_predicates.insert(name.to_string()) {
            let predicate = self.encoder.get_viper_predicate(name);
            // make sure we include all the fields
            predicate.body().as_ref().map(|body| self.walk_expr(body));
        }
        for arg in args {
            ExprWalker::walk(self, arg);
        }
        ExprWalker::walk(self, body);
    }
    fn walk_func_app(
        &mut self,
        name: &str,
        args: &Vec<polymorphic_vir::Expr>,
        formal_args: &Vec<polymorphic_vir::LocalVar>,
        return_type: &polymorphic_vir::Type,
        _pos: &polymorphic_vir::Position,
    ) {
        let identifier: polymorphic_vir::FunctionIdentifier =
            compute_identifier(name, formal_args, return_type).into();
        let have_visited = !self.used_functions.contains(&identifier);
        let have_visited_in_directly_calling_state =
            self.in_directly_calling_state && !self.directly_called_functions.contains(&identifier);
        if have_visited || have_visited_in_directly_calling_state {
            let function = self.encoder.get_function(&identifier);
            self.used_functions.insert(identifier.clone());
            for expr in function.pres.iter().chain(&function.posts) {
                self.walk_expr(expr);
            }
            let is_unfoldable = self.contains_unfolded_predicates(&function.pres)
                || self.contains_unfolded_parameters(&function.formal_args);
            if self.in_directly_calling_state || is_unfoldable {
                self.directly_called_functions.insert(identifier.clone());
                self.unfolded_functions.insert(identifier);
                let old_in_directly_calling_state = self.in_directly_calling_state;
                if !is_unfoldable {
                    // The functions called in the body of this function are
                    // directly callable only if this function is unfoldable.
                    self.in_directly_calling_state = false;
                }
                if let Some(body) = &function.body {
                    self.walk_expr(body);
                }
                self.in_directly_calling_state = old_in_directly_calling_state;
            }
        }
        for arg in args {
            ExprWalker::walk(self, arg)
        }
        for arg in formal_args {
            ExprWalker::walk_local_var(self, arg);
        }
        ExprWalker::walk_type(self, return_type);
    }
    fn walk_domain_func_app(
        &mut self,
        func: &polymorphic_vir::DomainFunc,
        args: &Vec<polymorphic_vir::Expr>,
        _pos: &polymorphic_vir::Position,
    ) {
        if func.domain_name.starts_with("Snap$") {
            self.used_snap_domain_functions
                .insert(func.get_identifier().into());
            self.used_domains.insert(func.domain_name.clone());
        } else {
            match func.domain_name.as_str() {
                "MirrorDomain" => {
                    // Always included when encoded, do nothing.
                    self.used_mirror_functions
                        .insert(func.get_identifier().into());
                }
                "UnitDomain" => {
                    self.used_domains.insert(func.domain_name.clone());
                }
                name => {
                    unreachable!("Unexpected domain: {}", name);
                }
            }
        }
        for arg in args {
            ExprWalker::walk(self, arg)
        }
        for arg in &func.formal_args {
            ExprWalker::walk_local_var(self, arg)
        }
    }
    fn walk_type(&mut self, typ: &polymorphic_vir::Type) {
        match typ {
            polymorphic_vir::Type::Seq( polymorphic_vir::SeqType {box typ} ) => {
                self.walk_type(typ);
            }
            polymorphic_vir::Type::TypedRef(..) | polymorphic_vir::Type::TypeVar(..) => {
                self.used_predicates.insert(typ.name());
            }
            polymorphic_vir::Type::Domain(..) => {
                let name = typ.name();
                if name != "UnitDomain" {
                    unreachable!("Unexpected type that is not snapshot: {}", name);
                }
            }
            polymorphic_vir::Type::Snapshot(..) => {
                self.used_domains.insert(format!("Snap${}", typ.name()));
            }
            _ => {}
        }
    }
}

/// Collects all predicates that are unfolded.
struct UnfoldedPredicateCollector {
    /// The predicates that are explicitly unfolded in the program.
    unfolded_predicates: HashSet<String>,
}

impl StmtWalker for UnfoldedPredicateCollector {
    fn walk_expr(&mut self, expr: &polymorphic_vir::Expr) {
        ExprWalker::walk(self, expr);
    }

    fn walk_fold(
        &mut self,
        predicate_name: &str,
        args: &Vec<polymorphic_vir::Expr>,
        _perm: &polymorphic_vir::PermAmount,
        _variant: &polymorphic_vir::MaybeEnumVariantIndex,
        _pos: &polymorphic_vir::Position,
    ) {
        self.unfolded_predicates.insert(predicate_name.to_string());
        for arg in args {
            self.walk_expr(arg);
        }
    }

    fn walk_unfold(
        &mut self,
        predicate_name: &str,
        args: &Vec<polymorphic_vir::Expr>,
        _perm: &polymorphic_vir::PermAmount,
        _variant: &polymorphic_vir::MaybeEnumVariantIndex,
    ) {
        self.unfolded_predicates.insert(predicate_name.to_string());
        for arg in args {
            self.walk_expr(arg);
        }
    }
}

impl ExprWalker for UnfoldedPredicateCollector {
    fn walk_unfolding(
        &mut self,
        name: &str,
        args: &Vec<polymorphic_vir::Expr>,
        body: &polymorphic_vir::Expr,
        _perm: polymorphic_vir::PermAmount,
        _variant: &polymorphic_vir::MaybeEnumVariantIndex,
        _pos: &polymorphic_vir::Position,
    ) {
        self.unfolded_predicates.insert(name.to_string());
        for arg in args {
            ExprWalker::walk(self, arg);
        }
        ExprWalker::walk(self, body);
    }
}

struct UnfoldedPredicateChecker<'a> {
    unfolded_predicates: &'a HashSet<String>,
    found: bool,
}

impl<'a> ExprWalker for UnfoldedPredicateChecker<'a> {
    fn walk_predicate_access_predicate(
        &mut self,
        typ: &polymorphic_vir::Type,
        _arg: &polymorphic_vir::Expr,
        _perm_amount: polymorphic_vir::PermAmount,
        _pos: &polymorphic_vir::Position,
    ) {
        if self.unfolded_predicates.contains(&typ.name()) {
            self.found = true;
        }
    }
}
