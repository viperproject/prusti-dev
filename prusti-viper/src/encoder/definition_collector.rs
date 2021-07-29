use std::{collections::HashSet, hash::Hash};

use prusti_common::{vir::{self, ExprWalker, FunctionIdentifier, StmtWalker, WithIdentifier, compute_identifier}, vir_local};

use super::Encoder;

pub(super) fn collect_definitions(
    encoder: &Encoder,
    name: String,
    methods: Vec<vir::CfgMethod>
) -> vir::Program {

    // let mut explictly_called_function_collector = ExplicitlyCalledFunctionCollector {
    //     called_functions: Default::default(),
    // };
    // vir::utils::walk_methods(&methods, &mut explictly_called_function_collector);
    let mut unfolded_predicate_collector = UnfoldedPredicateCollector {
        encoder,
        unfolded_predicates: Default::default(),
        called_functions: Default::default(),
        // explictly_called_function_collector.called_functions,
        inside_function_definition: false,
    };
    vir::utils::walk_methods(&methods, &mut unfolded_predicate_collector);
    let mut collector = Collector {
        encoder,
        unfolded_predicates: unfolded_predicate_collector.unfolded_predicates,
        used_predicates: Default::default(),
        used_fields: Default::default(),
        used_domains: Default::default(),
        used_functions: Default::default(),
        unfolded_functions: Default::default(),
        explicitly_called_functions: unfolded_predicate_collector.called_functions,
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
    /// The set of all predicates that are mentioned in the method.
    used_predicates: HashSet<String>,
    /// The set of predicates whose bodies have to be included because they are
    /// unfolded in the method.
    unfolded_predicates: HashSet<String>,
    used_fields: HashSet<vir::Field>,
    used_domains: HashSet<String>,
    /// The set of all predicates that are mentioned in the method.
    used_functions: HashSet<vir::FunctionIdentifier>,
    /// The set of functions whose bodies have to be included because predicates
    /// in their preconditions are unfolded.
    unfolded_functions: HashSet<vir::FunctionIdentifier>,
    /// Functions that are explicitly called in the program.
    explicitly_called_functions: HashSet<vir::FunctionIdentifier>,
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
            if !self.unfolded_predicates.contains(name) {
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
            if !self.unfolded_functions.contains(identifier) && !self.explicitly_called_functions.contains(identifier) {
                // The function body is not needed, make it abstract.
                function.body = None;
            }
            function
        }).collect();
        functions.sort_by_cached_key(|f| f.get_identifier());
        functions
    }
    fn get_used_domains(&self) -> Vec<vir::Domain> {
        let mut domains: Vec<_> = self.used_domains.iter().map(|domain_name| {
            let mut domain = self.encoder.get_domain(domain_name);
            if let Some(predicate_name) = domain_name.strip_prefix("Snap$") {
                // We have a snapshot for some type.
                if !self.unfolded_predicates.contains(predicate_name) {
                    // The type is never unfolded, so the snapshot should be abstract.
                    domain.axioms.clear();
                    domain.functions.clear();
                }
            }
            domain
        }).collect();
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
    // fn walk_unfolding(
    //     &mut self,
    //     name: &str,
    //     args: &Vec<vir::Expr>,
    //     body: &vir::Expr,
    //     _perm: vir::PermAmount,
    //     _variant: &vir::MaybeEnumVariantIndex,
    //     _pos: &vir::Position
    // ) {
    //     self.used_predicates.insert(name.to_string());
    //     for arg in args {
    //         ExprWalker::walk(self, arg);
    //     }
    //     ExprWalker::walk(self, body);
    // }
    fn walk_func_app(
        &mut self,
        name: &str,
        args: &Vec<vir::Expr>,
        formal_args: &Vec<vir::LocalVar>,
        return_type: &vir::Type,
        _pos: &vir::Position
    ) {
        let identifier: vir::FunctionIdentifier = compute_identifier(name, formal_args, return_type).into();
        if !self.used_functions.contains(&identifier) {
            let function = self.encoder.get_function(&identifier);
            if self.explicitly_called_functions.contains(&identifier) || self.contains_unfolded_predicates(&function.pres) {
                self.used_functions.insert(identifier.clone());
                self.unfolded_functions.insert(identifier);
                for expr in function.pres.iter().chain(&function.posts).chain(&function.body) {
                    self.walk_expr(expr);
                }
            } else {
                self.used_functions.insert(identifier);
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
        self.used_domains.insert(func.domain_name.clone());
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
                self.used_domains.insert(name.clone());
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
    /// The functions that are explicitly called in the program.
    called_functions: HashSet<FunctionIdentifier>,
    inside_function_definition: bool,
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
    fn walk_func_app(
        &mut self,
        name: &str,
        args: &Vec<vir::Expr>,
        formal_args: &Vec<vir::LocalVar>,
        return_type: &vir::Type,
        _pos: &vir::Position
    ) {
        if !self.inside_function_definition {
            self.inside_function_definition = true;
            let identifier: vir::FunctionIdentifier = compute_identifier(name, formal_args, return_type).into();
            let function = self.encoder.get_function(&identifier);
            for expr in function.pres.iter().chain(&function.posts).chain(&function.body) {
                self.walk_expr(expr);
            }
            self.called_functions.insert(identifier);
            self.inside_function_definition = false;
        }
    }
}


struct UnfoldedPredicateChecker<'a> {
    unfolded_predicates: &'a HashSet<String>,
    found: bool,
}

impl<'a> ExprWalker for UnfoldedPredicateChecker<'a> {
    fn walk_predicate_access_predicate(
        &mut self,
        name: &str,
        arg: &vir::Expr,
        _perm_amount: vir::PermAmount,
        _pos: &vir::Position
    ) {
        if self.unfolded_predicates.contains(name) {
            self.found = true;
        }
    }
}