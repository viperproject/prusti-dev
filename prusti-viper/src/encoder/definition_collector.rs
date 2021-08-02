use std::{collections::{HashMap, HashSet}, hash::Hash};

use prusti_common::{vir::{self, ExprWalker, FunctionIdentifier, StmtWalker, WithIdentifier, compute_identifier}, vir_local};

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
    methods: Vec<vir::CfgMethod>
) -> vir::Program {

    let mut unfolded_predicate_collector = UnfoldedPredicateCollector {
        encoder,
        unfolded_predicates: Default::default(),
    };
    vir::utils::walk_methods(&methods, &mut unfolded_predicate_collector);
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
    vir::Program {
        name,
        domains: collector.get_used_domains(),
        fields: collector.get_used_fields(),
        builtin_methods: collector.get_all_methods(),
        methods,
        functions: collector.get_used_functions(),
        viper_predicates: collector.get_used_predicates(),
    }
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
    used_fields: HashSet<vir::Field>,
    used_domains: HashSet<String>,
    used_snap_domain_functions: HashSet<vir::FunctionIdentifier>,
    /// The set of all functions that are mentioned in the method.
    used_functions: HashSet<vir::FunctionIdentifier>,
    /// The set of all mirror functions that are mentioned in the method.
    used_mirror_functions: HashSet<vir::FunctionIdentifier>,
    /// The set of functions whose bodies have to be included because predicates
    /// in their preconditions are unfolded.
    unfolded_functions: HashSet<vir::FunctionIdentifier>,
    /// Functions that are explicitly called in the program.
    directly_called_functions: HashSet<vir::FunctionIdentifier>,
    in_directly_calling_state: bool,
}

impl<'p, 'v: 'p, 'tcx: 'v> Collector<'p, 'v, 'tcx> {
    fn walk_methods(&mut self, methods: &[vir::CfgMethod]) {
        vir::utils::walk_methods(&methods, self);
        self.used_predicates.extend(self.unfolded_predicates.iter().cloned());
        self.used_functions.extend(self.unfolded_functions.iter().cloned());
    }
    fn get_used_fields(&self) -> Vec<vir::Field> {
        self.used_fields.iter().cloned().collect()
    }
    /// The purification optimization that is executed after this assumes that
    /// all bodyless methods are present. That is why we are returning all
    /// methods here.
    fn get_all_methods(&self) -> Vec<vir::BodylessMethod> {
        self.encoder.get_builtin_methods().values().cloned().collect()
    }
    fn get_used_predicates(&self) -> Vec<vir::Predicate> {
        let mut predicates: Vec<_> = self.used_predicates.iter().filter(|name| {
            *name != "AuxRef" // This is not a real type
        }).map(|name| {
            let predicate = self.encoder.get_viper_predicate(name);
            if !self.unfolded_predicates.contains(name) && !self.new_unfolded_predicates.contains(name) {
                // The predicate is never unfolded. Make it abstract.
                match self.encoder.get_viper_predicate(name) {
                    vir::Predicate::Struct(mut predicate) => {
                        predicate.body = None;
                        vir::Predicate::Struct(predicate)
                    }
                    vir::Predicate::Enum(predicate) => {
                        vir::Predicate::Struct(vir::StructPredicate {
                            name: predicate.name,
                            this: predicate.this,
                            body: None,
                        })
                    }
                    predicate => predicate,
                }
            } else {
                predicate
            }
        }).chain(Some(vir::Predicate::Bodyless(
            "DeadBorrowToken$".to_string(),
            vir_local!{ borrow: Int },
        ))).collect();
        predicates.sort_by_key(|f| f.get_identifier());
        predicates
    }
    fn get_used_functions(&self) -> Vec<vir::Function> {
        let mut functions: Vec<_> = self.used_functions.iter().map(|identifier| {
            let mut function = self.encoder.get_function(identifier).clone();
            if !self.unfolded_functions.contains(identifier) && !self.directly_called_functions.contains(identifier) {
                // The function body is not needed.
                if !function.has_constant_body() {
                    // The function body is non-constant, make the function
                    // abstract. (We leave the constant bodies so that they
                    // could be inlined by one of the optimizations.)
                    function.body = None;
                }
            }
            assert!(!self.method_names.contains(&function.name), "same Rust function encoded as both Viper method and function");
            function
        }).collect();
        functions.sort_by_cached_key(|f| f.get_identifier());
        functions
    }
    fn get_used_domains(&self) -> Vec<vir::Domain> {
        let mut domains: Vec<_> = self.used_domains.iter().map(|snapshot_name| {
            let mut domain = self.encoder.get_domain(snapshot_name);
            if let Some(predicate_name) = snapshot_name.strip_prefix("Snap$") {
                // We have a snapshot for some type.
                if !self.unfolded_predicates.contains(predicate_name) && !self.new_unfolded_predicates.contains(predicate_name) && !predicate_name.starts_with("Slice$") && !predicate_name.starts_with("Array$") {
                    // The type is never unfolded, so the snapshot should be
                    // abstract. The only exception is the discriminant function
                    // because it can be called on a folded type.
                    domain.axioms.clear();
                    domain.functions.retain(|function|
                        self.used_snap_domain_functions.contains(&function.get_identifier().into())
                    );
                }
            }
            domain
        }).collect();
        if let Some(mut mirror_domain) = self.encoder.get_mirror_domain() {
            mirror_domain.functions.retain(
                |function| self.used_mirror_functions.contains(&function.get_identifier().into())
            );
            domains.push(mirror_domain);
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
        formal_args.iter().any(|parameter|
            if let vir::Type::Snapshot(predicate) = &parameter.typ {
                self.unfolded_predicates.contains(predicate)
            } else {
                false
            }
        )
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> StmtWalker for Collector<'p, 'v, 'tcx> {
    fn walk_expr(&mut self, expr: &vir::Expr) {
        ExprWalker::walk(self, expr);
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> ExprWalker for Collector<'p, 'v, 'tcx> {
    fn walk_variant(&mut self, base: &vir::Expr, variant: &vir::Field, _pos: &vir::Position) {
        self.used_fields.insert(variant.clone());
        ExprWalker::walk(self, base);
        ExprWalker::walk_type(self, &variant.typ);
    }
    fn walk_field(&mut self, receiver: &vir::Expr, field: &vir::Field, _pos: &vir::Position) {
        self.used_fields.insert(field.clone());
        ExprWalker::walk(self, receiver);
        ExprWalker::walk_type(self, &field.typ);
    }
    fn walk_predicate_access_predicate(
        &mut self,
        name: &str,
        arg: &vir::Expr,
        _perm_amount: vir::PermAmount,
        _pos: &vir::Position
    ) {
        self.used_predicates.insert(name.to_string());
        ExprWalker::walk(self, arg)
    }
    fn walk_unfolding(
        &mut self,
        name: &str,
        args: &Vec<vir::Expr>,
        body: &vir::Expr,
        _perm: vir::PermAmount,
        _variant: &vir::MaybeEnumVariantIndex,
        _pos: &vir::Position
    ) {
        self.new_unfolded_predicates.insert(name.to_string());
        for arg in args {
            ExprWalker::walk(self, arg);
        }
        ExprWalker::walk(self, body);
    }
    fn walk_func_app(
        &mut self,
        name: &str,
        args: &Vec<vir::Expr>,
        formal_args: &Vec<vir::LocalVar>,
        return_type: &vir::Type,
        _pos: &vir::Position
    ) {
        let identifier: vir::FunctionIdentifier = compute_identifier(name, formal_args, return_type).into();
        let have_visited = !self.used_functions.contains(&identifier);
        let have_visited_in_directly_calling_state =
            self.in_directly_calling_state && !self.directly_called_functions.contains(&identifier);
        if have_visited || have_visited_in_directly_calling_state {
            let function = self.encoder.get_function(&identifier);
            self.used_functions.insert(identifier.clone());
            for expr in function.pres.iter().chain(&function.posts) {
                self.walk_expr(expr);
            }
            let is_unfoldable =
                self.contains_unfolded_predicates(&function.pres) ||
                self.contains_unfolded_parameters(&function.formal_args);
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
    }
    fn walk_domain_func_app(&mut self, func: &vir::DomainFunc, args: &Vec<vir::Expr>, _pos: &vir::Position) {
        if func.domain_name.starts_with("Snap$") {
            self.used_snap_domain_functions.insert(func.get_identifier().into());
            self.used_domains.insert(func.domain_name.clone());
        } else {
            match func.domain_name.as_str() {
                "MirrorDomain" => {
                    // Always included when encoded, do nothing.
                    self.used_mirror_functions.insert(func.get_identifier().into());
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
    fn walk_type(&mut self, typ: &vir::Type) {
        match typ {
            vir::Type::Seq(typ) => {
                self.walk_type(typ);
            },
            vir::Type::TypedRef(name) => {
                self.used_predicates.insert(name.clone());
            }
            vir::Type::Domain(name) => {
                if name != "UnitDomain" {
                    unreachable!("Unexpected type that is not snapshot: {}", name);
                }
            }
            vir::Type::Snapshot(name) => {
                self.used_domains.insert(format!("Snap${}", name));
            }
            _ => {}
        }
    }
}

// /// Collects all functions that are explicitly called.
// struct ExplicitlyCalledFunctionCollector {
//     /// The functions that are explicitly called in the program.
//     called_functions: HashSet<FunctionIdentifier>,
// }

// impl StmtWalker for ExplicitlyCalledFunctionCollector {
//     fn walk_expr(&mut self, expr: &vir::Expr) {
//         ExprWalker::walk(self, expr);
//     }
// }

// impl ExprWalker for ExplicitlyCalledFunctionCollector {
//     fn walk_func_app(
//         &mut self,
//         name: &str,
//         args: &Vec<vir::Expr>,
//         formal_args: &Vec<vir::LocalVar>,
//         return_type: &vir::Type,
//         _pos: &vir::Position
//     ) {
//         let identifier: vir::FunctionIdentifier = compute_identifier(name, formal_args, return_type).into();
//         self.called_functions.insert(identifier);
//     }
// }

/// Collects all predicates that are unfolded.
struct UnfoldedPredicateCollector<'p, 'v: 'p, 'tcx: 'v> {
    encoder: &'p Encoder<'v, 'tcx>,
    /// The predicates that are explicitly unfolded in the program.
    unfolded_predicates: HashSet<String>,
}

impl<'p, 'v: 'p, 'tcx: 'v> StmtWalker for UnfoldedPredicateCollector<'p, 'v, 'tcx> {
    fn walk_expr(&mut self, expr: &vir::Expr) {
        ExprWalker::walk(self, expr);
    }

    fn walk_fold(
        &mut self,
        predicate_name: &str,
        args: &Vec<vir::Expr>,
        _perm: &vir::PermAmount,
        _variant: &vir::MaybeEnumVariantIndex,
        _pos: &vir::Position
    ) {
        self.unfolded_predicates.insert(predicate_name.to_string());
        for arg in args {
            self.walk_expr(arg);
        }
    }

    fn walk_unfold(
        &mut self,
        predicate_name: &str,
        args: &Vec<vir::Expr>,
        _perm: &vir::PermAmount,
        _variant: &vir::MaybeEnumVariantIndex,
    ) {
        self.unfolded_predicates.insert(predicate_name.to_string());
        for arg in args {
            self.walk_expr(arg);
        }
    }

}

impl<'p, 'v: 'p, 'tcx: 'v> ExprWalker for UnfoldedPredicateCollector<'p, 'v, 'tcx> {
    fn walk_unfolding(
        &mut self,
        name: &str,
        args: &Vec<vir::Expr>,
        body: &vir::Expr,
        _perm: vir::PermAmount,
        _variant: &vir::MaybeEnumVariantIndex,
        _pos: &vir::Position
    ) {
        self.unfolded_predicates.insert(name.to_string());
        for arg in args {
            ExprWalker::walk(self, arg);
        }
        ExprWalker::walk(self, body);
    }
    // fn walk_func_app(
    //     &mut self,
    //     name: &str,
    //     args: &Vec<vir::Expr>,
    //     formal_args: &Vec<vir::LocalVar>,
    //     return_type: &vir::Type,
    //     _pos: &vir::Position
    // ) {
    //     let identifier: vir::FunctionIdentifier = compute_identifier(name, formal_args, return_type).into();
    //     if !self.inside_function_definition && !self.called_functions.contains(&identifier) {
    //         let function = self.encoder.get_function(&identifier);
    //         self.called_functions.insert(identifier);
    //         for expr in function.pres.iter().chain(&function.posts) {
    //             // Since limited functions do not apply to preconditions and
    //             // postconditions, we need to treat all functions called in the
    //             // postconditions as directly called.
    //             self.walk_expr(expr);
    //         }
    //         self.inside_function_definition = true;
    //         if let Some(body) = &function.body {
    //             self.walk_expr(body);
    //         }
    //         self.inside_function_definition = false;
    //     }
    //     for arg in args {
    //         self.walk_expr(arg);
    //     }
    // }
}


struct UnfoldedPredicateChecker<'a> {
    unfolded_predicates: &'a HashSet<String>,
    found: bool,
}

impl<'a> ExprWalker for UnfoldedPredicateChecker<'a> {
    fn walk_predicate_access_predicate(
        &mut self,
        name: &str,
        _arg: &vir::Expr,
        _perm_amount: vir::PermAmount,
        _pos: &vir::Position
    ) {
        if self.unfolded_predicates.contains(name) {
            self.found = true;
        }
    }
}