// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! Extracting and type-checking specifications.
//!
//! # Design
//!
//! Prusti uses the Rust annotation mechanism for specifications.
//! Currently, we support procedure preconditions and postconditions and
//! loop invariants. An example specification would look like this:
//!
//! ```rust,ignore
//! #[requires="0 < n && n < 10"]
//! #[ensures="result > 0"]
//! fn fib(mut n: i32) -> i32 {
//!     let mut i = 1;
//!     let mut j = 1;
//!     #[invariant="i > 0 && j > 0"]
//!     while n > 2 {
//!         let tmp = i + j;
//!         j = i;
//!         i = tmp;
//!         n -= 1;
//!     }
//!     i
//! }
//! ```
//!
//! The current version of the tool support the following assertion
//! syntax:
//!
//! ```bnf
//! assertion := assertion && assertion
//!            | expression ==> assertion
//!            | (forall variable_name :: {expression} expression ==> expression)
//! ```
//!
//! Here `expression` is a Rust expression that contains only elements
//! that are considered expressions in Viper, plus `match` expressions.
//! The parsed specification is stored in the structure
//! `specifications::UntypedSpecification` and type-checked
//! specification is stored in the structure
//! `specifications::TypedSpecification`.
//!
//! The general workflow for parsing and type-checking specifications is
//! as follows:
//!
//! 1.  Register callbacks on the `rustc_driver`:
//!
//!     +   `after_parse`
//!     +   `after_analysis`
//!
//!     After `after_analysis` the compilation is stopped (except when
//!     running in the test suite).
//!
//! 2.  When the `after_parse` callback is invoked:
//!
//!     1.  Register attributes `requires`, `ensures`, `invariant`,
//!         `__PRUSTI_SPEC_ONLY`, and `__PRUSTI_SPEC` to avoid the
//!         annoying warning about unknown attributes.
//!     2.  Collect all specification attributes.
//!     3.  Construct `UntypedSpecification` objects by parsing the
//!         specification attributes. First, we split each string into
//!         assertions and expression strings by using a regular
//!         expression. Then, by using the `parse_expr_from_source_str`
//!         procedure we parse each expression into a Rust `Expr` node.
//!         Finally, for each ``Expression`` generate a unique
//!         ``ExpressionId``.
//!     4.  Rewrite the program to add additional function, with “dummy”
//!         closure wrapping the Rust expressions used in
//!         specifications; these are then automatically type checked by
//!         the Rust compiler. This is necessary because it seems that
//!         there is no way to call a type checker on an AST manually.
//!         The example above would be rewritten as follows:
//!
//!         ```rust,ignore
//!         #[requires = "0 < n && n < 10"]
//!         #[ensures = "result > 0"]
//!         #[__PRUSTI_SPEC = r#"102"#]
//!         fn fib(mut n: i32) -> i32 {
//!             let mut i = 1;
//!             let mut j = 1;
//!
//!             #[__PRUSTI_SPEC = r#"101"#]
//!                 while n > 2 {
//!
//!                 #[__PRUSTI_SPEC_ONLY = r#"101"#]
//!                 if false {
//!                     {
//!                         #[__PRUSTI_LOOP_SPEC_ID = r#"101"#]
//!                             || { };
//!                         #[allow(unused_imports)]
//!                         use prusti_contracts::internal::*;
//!
//!                         #[__PRUSTI_EXPR_ID = r#"101"#]
//!                             #[pure]
//!                             || -> bool { i > 0 };
//!
//!                         #[__PRUSTI_EXPR_ID = r#"102"#]
//!                             #[pure]
//!                             || -> bool { j > 0 };
//!                     }
//!                 }
//!                 let tmp = i + j;
//!                 j = i;
//!                 i = tmp;
//!                 n -= 1;
//!             }
//!             i
//!         }
//!
//!         #[__PRUSTI_SPEC_ONLY = r#"102"#]
//!         #[allow(unused_mut)]
//!         #[allow(dead_code)]
//!         #[allow(non_snake_case)]
//!         #[allow(unused_imports)]
//!         #[allow(unused_variables)]
//!         fn fib__spec() -> () {
//!             #[__PRUSTI_SPEC_ONLY = r#"102"#]
//!             fn fib__spec__pre(mut n: i32) -> () {
//!                 #[allow(unused_imports)]
//!                 use prusti_contracts::internal::*;
//!
//!                 #[__PRUSTI_EXPR_ID = r#"103"#]
//!                 #[pure]
//!                 || -> bool { 0 < n };
//!
//!                 #[__PRUSTI_EXPR_ID = r#"104"#]
//!                 #[pure]
//!                 || -> bool { n < 10 };
//!             }
//!             #[__PRUSTI_SPEC_ONLY = r#"102"#]
//!             fn fib__spec__post(mut n: i32, result: i32) -> () {
//!                 #[allow(unused_imports)]
//!                 use prusti_contracts::internal::*;
//!
//!                 #[__PRUSTI_EXPR_ID = r#"105"#]
//!                 #[pure]
//!                 || -> bool { result > 0 };
//!             }
//!         }
//!         ```
//!
//! 3.  When the ``after_analysis`` callback is invoked:
//!
//!     1.  Traverse HIR and create a map from `ExpressionId` (argument of
//!         `__PRUSTI_EXPR_ID` attribute) to HIR `Expr`.
//!     2.  Construct `TypedAssertion` by traversing `UntypedAssertion`
//!         and inserting HIR expressions based on `ExpressionId`.
//!

use ast_builder::MinimalAstBuilder;
use constants::PRUSTI_SPEC_ATTR;
use prusti_common::report::log;
use regex::{self, Regex};
use rustc::session::Session;
use rustc_driver::driver;
use specifications::{
    Assertion, AssertionKind, Expression, ExpressionId, ForAllVars, SpecID, SpecType,
    SpecificationSet, Trigger, TriggerSet, UntypedAssertion, UntypedExpression,
    UntypedSpecification, UntypedSpecificationMap, UntypedSpecificationSet, UntypedTriggerSet,
};
use std::collections::{HashMap, HashSet};
use std::convert::TryFrom;
use std::io::Write;
use std::mem;
use std::sync::{Arc, Mutex};
use syntax::codemap::respan;
use syntax::codemap::Span;
use syntax::ext::build::AstBuilder;
use syntax::feature_gate::AttributeType;
use syntax::fold::{self, Folder};
use syntax::symbol::Symbol;
use syntax::util::small_vector::SmallVector;
use syntax::{self, ast, parse, ptr};
use syntax_pos::DUMMY_SP;
use syntax_pos::{BytePos, FileName, SyntaxContext};

use trait_register::{FunctionRef, TraitRegister};

pub fn register_traits(state: &mut driver::CompileState, register: Arc<Mutex<TraitRegister>>) {
    trace!("[register_traits] enter");
    let krate = state.krate.take().unwrap();
    let source_path = match driver::source_name(state.input) {
        FileName::Real(path) => path,
        _ => unreachable!(),
    };
    let source_filename = source_path.file_name().unwrap().to_str().unwrap();
    let mut parser = TraitParser::new(state.session, &source_filename, register);
    let _krate = parser.fold_crate(krate);
    trace!("[register_traits] exit");
}

/// Rewrite specifications in the expanded AST to get them type-checked
/// by rustc. For more information see the module documentation.
pub fn rewrite_crate(
    state: &mut driver::CompileState,
    register: Arc<Mutex<TraitRegister>>,
) -> UntypedSpecificationMap {
    trace!("[rewrite_crate] enter");
    let krate = state.krate.take().unwrap();
    let source_path = match driver::source_name(state.input) {
        FileName::Real(path) => path,
        _ => unreachable!(),
    };
    let source_filename = source_path.file_name().unwrap().to_str().unwrap();
    let mut parser = SpecParser::new(state.session, &source_filename, register);
    let krate = parser.fold_crate(krate);
    log_crate(&krate, &source_filename);
    state.krate = Some(krate);
    trace!("[rewrite_crate] exit");
    parser.untyped_specifications
}

/// Register attributes in whitelist
pub fn register_attributes(state: &mut driver::CompileState) {
    trace!("[register_attributes] enter");
    let registry = state.registry.as_mut().unwrap();
    registry.register_attribute(String::from("trusted"), AttributeType::Whitelisted);
    registry.register_attribute(String::from("pure"), AttributeType::Whitelisted);
    registry.register_attribute(String::from("invariant"), AttributeType::Whitelisted);
    registry.register_attribute(String::from("requires"), AttributeType::Whitelisted);
    registry.register_attribute(String::from("ensures"), AttributeType::Whitelisted);
    registry.register_attribute(String::from("refine_ensures"), AttributeType::Whitelisted);
    registry.register_attribute(String::from("refine_requires"), AttributeType::Whitelisted);
    registry.register_attribute(PRUSTI_SPEC_ATTR.to_string(), AttributeType::Whitelisted);
    registry.register_attribute(
        String::from("__PRUSTI_SPEC_ONLY"),
        AttributeType::Whitelisted,
    );
    registry.register_attribute(
        String::from("__PRUSTI_LOOP_SPEC_ID"),
        AttributeType::Whitelisted,
    );
    registry.register_attribute(String::from("__PRUSTI_EXPR_ID"), AttributeType::Whitelisted);
    registry.register_attribute(
        String::from("__PRUSTI_FORALL_ID"),
        AttributeType::Whitelisted,
    );
    trace!("[register_attributes] exit");
}

/// Log the rewritten crate for debugging.
fn log_crate(krate: &ast::Crate, source_filename: &str) {
    let mut writer = log::build_writer("rust_crate_before_typechecking", source_filename)
        .ok()
        .unwrap();
    let krate_str = syntax::print::pprust::to_string(|s| s.print_mod(&krate.module, &krate.attrs));
    writer
        .write_all("#![feature(custom_attribute)]\n".as_bytes())
        .unwrap();
    writer.write_all(krate_str.to_string().as_bytes()).unwrap();
    writer.flush().ok().unwrap();
}

pub struct TraitParser<'tcx> {
    register: Arc<Mutex<TraitRegister>>,
    spec_parser: SpecParser<'tcx>,
}

impl<'tcx> TraitParser<'tcx> {
    pub fn new(
        session: &'tcx Session,
        source_filename: &str,
        register: Arc<Mutex<TraitRegister>>,
    ) -> Self {
        Self {
            register: register.clone(),
            spec_parser: SpecParser::new(session, source_filename, register),
        }
    }
}

impl<'tcx> Folder for TraitParser<'tcx> {
    fn fold_item(&mut self, item: ptr::P<ast::Item>) -> SmallVector<ptr::P<ast::Item>> {
        trace!("[fold_item] enter");
        let result = fold::noop_fold_item(item, self)
            .into_iter()
            .map(|item| {
                let item = item.into_inner();
                match item.node.clone() {
                    // Structs
                    ast::ItemKind::Struct(..) => {
                        let mut reg = self.register.lock().unwrap();
                        reg.register_struct(&item);
                    }
                    // Impl block
                    ast::ItemKind::Impl(..) => {
                        let mut reg = self.register.lock().unwrap();
                        reg.register_impl(&item);
                    }
                    // Methods in trait definition
                    ast::ItemKind::Trait(_, _, _, bounds, _) => {
                        let bounds_symbols: HashSet<Symbol> = bounds
                            .iter()
                            .map(|bound| match bound.clone() {
                                ast::GenericBound::Trait(mut t_ref, _) => {
                                    t_ref.trait_ref.path.segments.pop()
                                }
                                _ => None,
                            })
                            .filter(|s| s.is_some())
                            .map(|s_opt| s_opt.unwrap().ident.name)
                            .collect();

                        let mut reg = self.register.lock().unwrap();
                        let specs = self.spec_parser.parse_specs(item.attrs.clone());

                        // check if specs refer to existing super trait
                        specs
                            .iter()
                            .zip(item.attrs.iter())
                            .map(|(s, a)| (s.typ.get_function_ref(), a))
                            .filter(|(r, _)| r.is_some())
                            .map(|(r, a)| (r.unwrap().0, a.span))
                            .for_each(|(r, s)| {
                                if !bounds_symbols.contains(&r) {
                                    self.spec_parser
                                        .report_error(s, "does not refer to super trait");
                                }
                            });

                        reg.register_trait_decl(&item, &specs);
                    }
                    // Any other item
                    _ => (),
                };
                ptr::P(item)
            })
            .collect();
        trace!("[fold_item] exit");
        result
    }

    fn fold_mac(&mut self, mac: ast::Mac) -> ast::Mac {
        mac
    }
}

/// A data structure that extracts preconditions, postconditions,
/// and loop invariants. It also rewrites the AST for type-checking.
/// Each original assertion gets a unique `SpecID` and expression – a
/// unique `ExpressionId` that allows to map them back to their original
/// locations.
pub struct SpecParser<'tcx> {
    session: &'tcx Session,
    register: Arc<Mutex<TraitRegister>>,
    ast_builder: MinimalAstBuilder<'tcx>,
    last_specification_id: SpecID,
    last_expression_id: ExpressionId,
    untyped_specifications: UntypedSpecificationMap,
    rust_program_before_typechecking_writer: Box<Write>,
}

impl<'tcx> SpecParser<'tcx> {
    /// Create new spec parser.
    pub fn new(
        session: &'tcx Session,
        source_filename: &str,
        register: Arc<Mutex<TraitRegister>>,
    ) -> SpecParser<'tcx> {
        SpecParser {
            session: session,
            register: register,
            ast_builder: MinimalAstBuilder::new(&session.parse_sess),
            last_specification_id: SpecID::new(),
            last_expression_id: ExpressionId::new(),
            untyped_specifications: HashMap::new(),
            rust_program_before_typechecking_writer: log::build_writer(
                "rust_program_before_typechecking",
                source_filename,
            )
            .ok()
            .unwrap(),
        }
    }

    fn log_modified_program<S: ToString>(&mut self, data: S) {
        let writer = self.rust_program_before_typechecking_writer.as_mut();
        writer.write_all(data.to_string().as_bytes()).ok().unwrap();
        writer
            .write_all("\n\n".to_string().as_bytes())
            .ok()
            .unwrap();
        writer.flush().ok().unwrap();
    }

    /// Generate a fresh specification ID (guaranteed to be unique).
    fn get_new_specification_id(&mut self) -> SpecID {
        self.last_specification_id.inc()
    }

    /// Generate a fresh expression ID (guaranteed to be unique).
    fn get_new_expression_id(&mut self) -> ExpressionId {
        self.last_expression_id.inc()
    }

    /// Register the raw specification and return the ID under which it
    /// was stored.
    fn register_specification(&mut self, spec: UntypedSpecificationSet) -> SpecID {
        let new_id = self.get_new_specification_id();
        self.untyped_specifications.insert(new_id, spec);
        new_id
    }

    /// Replace the specification set for some ID.
    fn replace_specification(&mut self, id: SpecID, spec: UntypedSpecificationSet) {
        let old_spec_opt = self.untyped_specifications.insert(id, spec);
        if let Some(old_spec) = old_spec_opt {
            if !old_spec.is_empty() {
                warn!("replaced existant non-empty specification");
            }
        } else {
            warn!("replaced non-existant specification");
        }
    }

    fn report_error(&self, span: Span, message: &str) {
        let mut err = self.session.struct_span_err(span, message);
        err.emit();
    }

    fn report_warn(&self, span: Span, message: &str, note: &str) {
        let mut warn = self.session.struct_span_warn(span, message);
        warn.note(note);
        warn.emit();
    }

    /// Construct a lambda function with an attribute that identifies the spec id of the loop
    fn build_loop_mark(&self, spec_id: SpecID) -> ast::Stmt {
        let builder = &self.ast_builder;
        let span = DUMMY_SP;
        let mut lambda_fn = builder
            .lambda_fn_decl(
                span,
                builder.fn_decl(vec![], ast::FunctionRetTy::Default(span)),
                builder.expr_block(builder.block(span, vec![])),
                span,
            )
            .into_inner();
        lambda_fn.attrs = vec![self.ast_builder.attribute_name_value(
            span,
            "__PRUSTI_LOOP_SPEC_ID",
            &spec_id.to_string(),
        )]
        .into();
        builder.stmt_semi(ptr::P(lambda_fn))
    }

    /// Construct a lambda function with given expression to make that expression
    /// to be type-checked by the Rust compiler.
    fn build_typeck_call(
        &self,
        expression: &UntypedExpression,
        expected_ty: Option<ptr::P<ast::Ty>>,
    ) -> ast::Stmt {
        let builder = &self.ast_builder;
        let expr_id = expression.id;
        let rust_expr = expression.expr.clone();
        let span = rust_expr.span;
        let any_ty = self.ast_builder.ty(span, ast::TyKind::Infer);
        let return_ty = expected_ty.unwrap_or(any_ty);
        let mut lambda_fn = builder
            .lambda_fn_decl(
                span,
                builder.fn_decl(vec![], ast::FunctionRetTy::Ty(return_ty)),
                builder.expr_block(builder.block(span, vec![builder.stmt_expr(rust_expr)])),
                span,
            )
            .into_inner();
        lambda_fn.attrs = vec![
            self.ast_builder
                .attribute_name_value(span, "__PRUSTI_EXPR_ID", &expr_id.to_string()),
            self.ast_builder.attribute_word(span, "pure"),
        ]
        .into();
        builder.stmt_semi(ptr::P(lambda_fn))
    }

    fn build_assertion(&self, expression: &UntypedExpression) -> ast::Stmt {
        let bool_path = self
            .ast_builder
            .path_ident(expression.expr.span, self.ast_builder.ident_of("bool"));
        let bool_ty = self.ast_builder.ty_path(bool_path);
        self.build_typeck_call(expression, Some(bool_ty))
    }

    fn convert_trigger_set_to_statements(&self, trigger_set: &UntypedTriggerSet) -> Vec<ast::Stmt> {
        let mut statements = Vec::new();
        for trigger in trigger_set.triggers().iter() {
            for term in trigger.terms().iter() {
                let statement = self.build_typeck_call(term, None);
                statements.push(statement);
            }
        }
        statements
    }

    fn populate_statements(&self, assertion: &UntypedAssertion, statements: &mut Vec<ast::Stmt>) {
        trace!("[populate_statements] enter");
        match *assertion.kind {
            AssertionKind::Expr(ref expression) => {
                let stmt = self.build_assertion(expression);
                statements.push(stmt);
            }
            AssertionKind::And(ref assertions) => {
                for assertion in assertions {
                    self.populate_statements(assertion, statements);
                }
            }
            AssertionKind::Implies(ref lhs_assertion, ref rhs_assertion) => {
                self.populate_statements(lhs_assertion, statements);
                self.populate_statements(rhs_assertion, statements);
            }
            AssertionKind::TypeCond(ref vars, ref assertion) => {
                // TODO deduplicate (see below...)

                let builder = &self.ast_builder;

                // TODO: use a proper span
                let span = DUMMY_SP;

                let mut lambda_fn = builder
                    .lambda_fn_decl(
                        span,
                        builder.fn_decl(vars.vars.clone(), ast::FunctionRetTy::Default(span)),
                        builder.expr_block(builder.block(span, vec![])),
                        span,
                    )
                    .into_inner();

                lambda_fn.attrs = vec![
                    builder.attribute_name_value(span, "__PRUSTI_FORALL_ID", &vars.id.to_string()),
                    builder.attribute_word(span, "pure"),
                ]
                .into();

                let statement = builder.stmt_semi(ptr::P(lambda_fn));
                statements.push(statement);

                // the remainder
                self.populate_statements(assertion, statements);
            }
            // encode generics typecond as forallvargs (hack!)
            AssertionKind::ForAll(ref vars, ref trigger_set, ref body) => {
                let mut stmts = self.convert_trigger_set_to_statements(trigger_set);
                self.populate_statements(body, &mut stmts);
                let builder = &self.ast_builder;

                // TODO: use a proper span
                let span = DUMMY_SP;

                let mut lambda_fn = builder
                    .lambda_fn_decl(
                        span,
                        builder.fn_decl(vars.vars.clone(), ast::FunctionRetTy::Default(span)),
                        builder.expr_block(builder.block(span, stmts)),
                        span,
                    )
                    .into_inner();

                lambda_fn.attrs = vec![
                    builder.attribute_name_value(span, "__PRUSTI_FORALL_ID", &vars.id.to_string()),
                    builder.attribute_word(span, "pure"),
                ]
                .into();

                let statement = builder.stmt_semi(ptr::P(lambda_fn));
                statements.push(statement);
            }
            AssertionKind::Pledge(ref reference, ref lhs, ref rhs) => {
                if let Some(ref reference) = reference {
                    let statement = self.build_typeck_call(reference, None);
                    statements.push(statement);
                }
                self.populate_statements(lhs, statements);
                self.populate_statements(rhs, statements);
            }
        };
        trace!("[populate_statements] exit");
    }

    /// Convert untyped specifications into a sequence of statements for
    /// type-checking.
    fn convert_to_statements(&self, specifications: &[UntypedSpecification]) -> Vec<ast::Stmt> {
        trace!("[convert_to_statements] enter");
        let mut statements = Vec::new();
        for specification in specifications {
            self.populate_statements(&specification.assertion, &mut statements);
        }
        trace!("[convert_to_statements] exit");
        statements
    }

    fn build_prusti_contract_import(&self, span: Span) -> ast::Stmt {
        let builder = &self.ast_builder;
        let mut item = builder
            .item_use_glob(
                span,
                respan(span.shrink_to_lo(), ast::VisibilityKind::Inherited),
                vec![
                    builder.ident_of("prusti_contracts"),
                    builder.ident_of("internal"),
                ],
            )
            .into_inner();
        item.attrs = vec![self
            .ast_builder
            .attribute_allow(item.span, "unused_imports")];
        builder.stmt_item(span, ptr::P(item))
    }

    fn check_for_result_in_params(&mut self, params: &Vec<ast::Arg>) -> bool {
        params.iter().any(|p| match (*p.pat).node {
            ast::PatKind::Ident(_, id, _) => id.name.as_str() == "result",
            _ => false,
        })
    }

    /// Generate a function that contains only the precondition and postcondition
    /// for type-checking.
    fn generate_spec_item(
        &mut self,
        item: &ast::Item,
        spec_id: SpecID,
        preconditions: &[UntypedSpecification],
        postconditions: &[UntypedSpecification],
    ) -> ast::Item {
        let mut name = item.ident.to_string();
        let unit_type = self.ast_builder.ty(item.span, ast::TyKind::Tup(Vec::new()));
        let spec_only_attr = self.ast_builder.attribute_name_value(
            item.span,
            "__PRUSTI_SPEC_ONLY",
            &spec_id.to_string(),
        );

        name.push_str("__spec");

        match item.node {
            ast::ItemKind::Fn(ref decl, ref _header, ref generics, ref _body) => {
                let result_as_param = self.check_for_result_in_params(&decl.inputs);
                if result_as_param {
                    self.report_warn(
                        item.span,
                        "parameter `result` found",
                        "Using parameter `result` in specifications instead of the return value.",
                    );
                }

                let fn_pre = {
                    let mut statements = self.convert_to_statements(preconditions);
                    // Import contracts, if needed
                    if !statements.is_empty() {
                        statements.insert(0, self.build_prusti_contract_import(item.span));
                    }
                    let mut name = name.to_owned();
                    name.push_str("__pre");
                    self.ast_builder.stmt_item(
                        item.span,
                        self.ast_builder.item_fn_attributes(
                            item.span,
                            ast::Ident::from_str(&name),
                            decl.inputs.clone(),
                            unit_type.clone(),
                            generics.clone(),
                            vec![spec_only_attr.clone()],
                            self.ast_builder.block(item.span, statements),
                        ),
                    )
                };

                let fn_post = {
                    let mut statements = self.convert_to_statements(postconditions);
                    // Import contracts, if needed
                    if !statements.is_empty() {
                        statements.insert(0, self.build_prusti_contract_import(item.span));
                    }
                    let mut name = name.to_owned();
                    name.push_str("__post");
                    let return_type = match decl.output.clone() {
                        ast::FunctionRetTy::Ty(ret_ty) => match ret_ty.node {
                            ast::TyKind::Never => unit_type.clone(),
                            _ => ret_ty,
                        },
                        ast::FunctionRetTy::Default(_) => unit_type.clone(),
                    };
                    // Add result to arguments
                    let mut inputs_with_result: Vec<ast::Arg> = decl.inputs.clone();
                    if !result_as_param {
                        inputs_with_result.push(self.ast_builder.arg(
                            item.span,
                            ast::Ident::from_str("result"),
                            return_type.clone(),
                        ));
                    }
                    self.ast_builder.stmt_item(
                        item.span,
                        self.ast_builder.item_fn_attributes(
                            item.span,
                            ast::Ident::from_str(&name),
                            inputs_with_result,
                            unit_type.clone(),
                            generics.clone(),
                            vec![spec_only_attr.clone()],
                            self.ast_builder.block(item.span, statements),
                        ),
                    )
                };
                let statements = vec![fn_pre, fn_post];

                // Attributes for the spec method
                let spec_attr = vec![
                    spec_only_attr,
                    self.ast_builder.attribute_allow(item.span, "unused_mut"),
                    self.ast_builder.attribute_allow(item.span, "dead_code"),
                    self.ast_builder
                        .attribute_allow(item.span, "non_snake_case"),
                    self.ast_builder
                        .attribute_allow(item.span, "unused_imports"),
                    self.ast_builder
                        .attribute_allow(item.span, "unused_variables"),
                ];

                // Glue everything
                self.ast_builder
                    .item_fn_attributes(
                        item.span,
                        ast::Ident::from_str(&name),
                        vec![],
                        unit_type,
                        generics.clone(),
                        spec_attr,
                        self.ast_builder.block(item.span, statements),
                    )
                    .into_inner()
            }
            _ => {
                unreachable!();
            }
        }
    }

    /// Generate a function that contains only an invariant for type-checking.
    fn generate_spec_item_inv(
        &mut self,
        item: &ast::Item,
        spec_id: SpecID,
        invariants: &[UntypedSpecification],
        postfix: Option<&str>,
        base_opt: Option<ast::Item>,
    ) -> ast::Item {
        let mut name = item.ident.to_string();
        match item.node {
            ast::ItemKind::Struct(ref _variantdata, ref generics) => {
                let mut statements = vec![];

                // Add invariants.
                statements.extend(self.convert_to_statements(invariants));

                // Import contracts, if needed
                if !statements.is_empty() {
                    statements.insert(0, self.build_prusti_contract_import(item.span));
                }

                // Add result to arguments
                let unit_type = self.ast_builder.ty(item.span, ast::TyKind::Tup(Vec::new()));

                let mut self_arg: Vec<ast::Arg> = Vec::new();
                self_arg.push(self.ast_builder.arg(
                    item.span,
                    ast::Ident::from_str("self"),
                    // OPEN TODO: using a ref (&mut or &) causes permission troubles
                    //self.ast_builder.ty_rptr(
                    //    item.span,
                    //    self.ast_builder.ty(item.span, ast::TyKind::ImplicitSelf),
                    //    None,
                    //    ast::Mutability::Mutable
                    //)
                    self.ast_builder.ty(item.span, ast::TyKind::ImplicitSelf),
                ));

                // Glue everything.
                if let Some(postfix) = postfix {
                    name.push_str(&format!("__{}__spec", postfix));
                } else {
                    name.push_str("__spec");
                }

                let mut spec_item = self.ast_builder.impl_item_method(
                    item.span,
                    ast::Ident::from_str(&name),
                    Vec::new(),         // attrs,
                    Default::default(), // Generics
                    self_arg,
                    unit_type,
                    self.ast_builder.block(item.span, statements),
                );

                mem::replace(
                    &mut spec_item.attrs,
                    vec![
                        self.ast_builder.attribute_name_value(
                            item.span,
                            "__PRUSTI_SPEC_ONLY",
                            &spec_id.to_string(),
                        ),
                        self.ast_builder.attribute_allow(item.span, "unused_mut"),
                        self.ast_builder.attribute_allow(item.span, "dead_code"),
                        self.ast_builder
                            .attribute_allow(item.span, "non_snake_case"),
                        self.ast_builder
                            .attribute_allow(item.span, "unused_imports"),
                        self.ast_builder
                            .attribute_allow(item.span, "unused_variables"),
                    ],
                );

                let args = generics
                    .params
                    .iter()
                    .map(|x| ast::GenericArg::Type(self.ast_builder.ty_ident(DUMMY_SP, x.ident)))
                    .collect();

                // TODO(@jakob): merge generic requirements
                let mut gen = generics.clone();
                // TODO not dummy ?! (or should it?)
                //self.ast_builder.ty_ident(DUMMY_SP, item.ident), // `item` is the struct
                let mut ty = self.ast_builder.ty_path(self.ast_builder.path_all(
                    DUMMY_SP,
                    false, // global
                    vec![item.ident],
                    args,   // (type parameters)
                    vec![], // bindings
                ));
                if let Some(base) = base_opt {
                    if let ast::ItemKind::Impl(_, _, _, g, _, t, _) = base.node.clone() {
                        gen = g;
                        ty = t;
                    }
                }

                let spec_item_envelope = ast::Item {
                    ident: ast::Ident::from_str(""), // FIXME?
                    attrs: Vec::new(),
                    id: ast::DUMMY_NODE_ID,
                    node: ast::ItemKind::Impl(
                        ast::Unsafety::Normal,
                        ast::ImplPolarity::Positive,
                        ast::Defaultness::Final,
                        gen,
                        None, // TraitRef
                        ty,
                        vec![spec_item], // methods et al.
                    ),
                    vis: self.ast_builder.visinh(), // TODO not dummy!
                    span: DUMMY_SP,                 // TODO not dummy
                    tokens: None,
                };

                spec_item_envelope
            }
            _ => {
                unreachable!();
            }
        }
    }

    /// Generate an impl item that contains only the precondition and postcondition
    /// for type-checking.
    fn generate_spec_impl_item(
        &mut self,
        impl_item: &ast::ImplItem,
        spec_id: SpecID,
        preconditions: &[UntypedSpecification],
        postconditions: &[UntypedSpecification],
    ) -> ast::ImplItem {
        let mut name = impl_item.ident.to_string();
        match impl_item.node {
            ast::ImplItemKind::Method(ref sig, ref _body) => {
                // Import contracts.
                let mut statements = vec![];

                // Add preconditions.
                statements.extend(self.convert_to_statements(preconditions));

                // Add postconditions.
                statements.extend(self.convert_to_statements(postconditions));

                // Import contracts, if needed
                if !statements.is_empty() {
                    statements.insert(0, self.build_prusti_contract_import(impl_item.span));
                }

                // Add result to arguments
                let unit_type = self
                    .ast_builder
                    .ty(impl_item.span, ast::TyKind::Tup(Vec::new()));
                let return_type = match sig.decl.output.clone() {
                    ast::FunctionRetTy::Ty(ret_ty) => match ret_ty.node {
                        ast::TyKind::Never => unit_type.clone(),
                        _ => ret_ty,
                    },
                    ast::FunctionRetTy::Default(_) => unit_type.clone(),
                };
                let mut inputs_with_result: Vec<ast::Arg> = sig.decl.inputs.clone();
                inputs_with_result.push(self.ast_builder.arg(
                    impl_item.span,
                    ast::Ident::from_str("result"),
                    return_type.clone(),
                ));

                let attrs = vec![
                    self.ast_builder.attribute_name_value(
                        impl_item.span,
                        "__PRUSTI_SPEC_ONLY",
                        &spec_id.to_string(),
                    ),
                    self.ast_builder
                        .attribute_allow(impl_item.span, "unused_mut"),
                    self.ast_builder
                        .attribute_allow(impl_item.span, "dead_code"),
                    self.ast_builder
                        .attribute_allow(impl_item.span, "non_snake_case"),
                    self.ast_builder
                        .attribute_allow(impl_item.span, "unused_imports"),
                    self.ast_builder
                        .attribute_allow(impl_item.span, "unused_variables"),
                ];

                // Glue everything.
                name.push_str("__spec");
                self.ast_builder.impl_item_method(
                    impl_item.span,
                    ast::Ident::from_str(&name),
                    attrs,
                    impl_item.generics.clone(),
                    inputs_with_result,
                    unit_type,
                    self.ast_builder.block(impl_item.span, statements),
                )
            }
            _ => {
                unreachable!();
            }
        }
    }

    /// Generate a trait item that contains only the precondition and postcondition
    /// for type-checking.
    fn generate_spec_trait_item(
        &mut self,
        trait_item: &ast::TraitItem,
        spec_id: SpecID,
        preconditions: &[UntypedSpecification],
        postconditions: &[UntypedSpecification],
    ) -> ast::TraitItem {
        let mut name = trait_item.ident.to_string();
        match trait_item.node {
            ast::TraitItemKind::Method(ref sig, ref _body) => {
                // Import contracts.
                let mut statements = vec![];

                // Add preconditions.
                statements.extend(self.convert_to_statements(preconditions));

                // Add postconditions.
                statements.extend(self.convert_to_statements(postconditions));

                // Import contracts, if needed
                if !statements.is_empty() {
                    statements.insert(0, self.build_prusti_contract_import(trait_item.span));
                }

                // Add result to arguments
                let unit_type = self
                    .ast_builder
                    .ty(trait_item.span, ast::TyKind::Tup(Vec::new()));
                let return_type = match sig.decl.output.clone() {
                    ast::FunctionRetTy::Ty(ret_ty) => match ret_ty.node {
                        ast::TyKind::Never => unit_type.clone(),
                        _ => ret_ty,
                    },
                    ast::FunctionRetTy::Default(_) => unit_type.clone(),
                };
                let mut inputs_with_result: Vec<ast::Arg> = sig.decl.inputs.clone();
                inputs_with_result.push(self.ast_builder.arg(
                    trait_item.span,
                    ast::Ident::from_str("result"),
                    return_type.clone(),
                ));

                let attrs = vec![
                    self.ast_builder.attribute_name_value(
                        trait_item.span,
                        "__PRUSTI_SPEC_ONLY",
                        &spec_id.to_string(),
                    ),
                    self.ast_builder
                        .attribute_allow(trait_item.span, "unused_mut"),
                    self.ast_builder
                        .attribute_allow(trait_item.span, "dead_code"),
                    self.ast_builder
                        .attribute_allow(trait_item.span, "non_snake_case"),
                    self.ast_builder
                        .attribute_allow(trait_item.span, "unused_imports"),
                    self.ast_builder
                        .attribute_allow(trait_item.span, "unused_variables"),
                ];

                // Glue everything.
                name.push_str("__spec");
                self.ast_builder.trait_item_method(
                    trait_item.span,
                    ast::Ident::from_str(&name),
                    attrs,
                    trait_item.generics.clone(),
                    inputs_with_result,
                    unit_type,
                    self.ast_builder.block(trait_item.span, statements),
                )
            }
            _ => {
                unreachable!();
            }
        }
    }

    fn rewrite_loop_block(
        &mut self,
        block: ptr::P<ast::Block>,
        spec_id: SpecID,
        invariants: &[UntypedSpecification],
    ) -> ptr::P<ast::Block> {
        trace!("[rewrite_loop_block] enter");
        // Important: fold the content of the loop with `self.fold_block`
        let mut block = self.fold_block(block).into_inner();
        // Early return
        if invariants.is_empty() {
            return ptr::P(block);
        }
        let span = block.span;
        let mut statements = self.convert_to_statements(invariants);
        if !statements.is_empty() {
            statements.insert(0, self.build_prusti_contract_import(span));
        }
        statements.insert(0, self.build_loop_mark(spec_id));
        let builder = &self.ast_builder;
        let expr = builder.expr_if(
            Span::new(BytePos(0), BytePos(0), SyntaxContext::empty()),
            builder.expr_bool(span, false),
            builder.expr_block(builder.block(span, statements)),
            None,
        );
        let mut expr = expr.into_inner();
        expr.attrs = vec![self.ast_builder.attribute_name_value(
            span,
            "__PRUSTI_SPEC_ONLY",
            &spec_id.to_string(),
        )]
        .into();
        block.stmts.insert(0, builder.stmt_expr(ptr::P(expr)));
        trace!("[rewrite_loop_block] exit");
        ptr::P(block)
    }

    fn rewrite_loop(&mut self, expr: ptr::P<ast::Expr>) -> ptr::P<ast::Expr> {
        trace!("[rewrite_loop] enter");
        let mut expr = expr.into_inner();
        let attrs = expr.attrs.to_vec();
        expr.attrs = vec![].into();
        let invariants = self.parse_specs(attrs);
        if !invariants
            .iter()
            .all(|spec| spec.typ == SpecType::Invariant)
        {
            self.report_error(expr.span, "loops can have only invariants");
            return ptr::P(expr);
        }
        let spec_set = SpecificationSet::Loop(invariants.clone());
        let id = self.register_specification(spec_set);
        expr.node = match expr.node {
            ast::ExprKind::While(condition, block, ident) => {
                let block = self.rewrite_loop_block(block, id, &invariants);
                let condition = self.fold_expr(condition);
                ast::ExprKind::While(condition, block, ident)
            }
            ast::ExprKind::WhileLet(pattern, expr, block, label) => {
                let block = self.rewrite_loop_block(block, id, &invariants);
                ast::ExprKind::WhileLet(pattern, expr, block, label)
            }
            ast::ExprKind::ForLoop(pattern, expr, block, label) => {
                let block = self.rewrite_loop_block(block, id, &invariants);
                ast::ExprKind::ForLoop(pattern, expr, block, label)
            }
            ast::ExprKind::Loop(block, label) => {
                let block = self.rewrite_loop_block(block, id, &invariants);
                ast::ExprKind::Loop(block, label)
            }
            _ => unreachable!(),
        };
        let mut new_attrs: Vec<_> = expr
            .attrs
            .iter()
            .cloned()
            .filter(|attr| {
                !attr.check_name("trusted")
                    && !attr.check_name("pure")
                    && !attr.check_name("invariant")
                    && !attr.check_name("requires")
                    && !attr.check_name("ensures")
            })
            .collect();
        new_attrs.push(self.ast_builder.attribute_name_value(
            expr.span,
            PRUSTI_SPEC_ATTR,
            &id.to_string(),
        ));
        expr.attrs = new_attrs.into();

        trace!("[rewrite_loop] exit");
        ptr::P(expr)
    }

    fn rewrite_fn_item(&mut self, item: ptr::P<ast::Item>) -> SmallVector<ptr::P<ast::Item>> {
        trace!("[rewrite_fn_item] enter");
        let mut item = item.into_inner();

        // Parse specification
        let specs = self.parse_specs(item.attrs.clone());
        if specs.iter().any(|spec| spec.typ == SpecType::Invariant) {
            self.report_error(item.span, "invariant not allowed for procedure");
            return SmallVector::one(ptr::P(item));
        }
        let preconditions: Vec<_> = specs
            .clone()
            .into_iter()
            .filter(|spec| spec.typ == SpecType::Precondition)
            .collect();
        let postconditions: Vec<_> = specs
            .into_iter()
            .filter(|spec| spec.typ == SpecType::Postcondition)
            .collect();
        let spec_set = SpecificationSet::Procedure(preconditions.clone(), postconditions.clone());

        // Register specification
        let id = self.register_specification(spec_set.clone());
        item.attrs.push(self.ast_builder.attribute_name_value(
            item.span,
            PRUSTI_SPEC_ATTR,
            &id.to_string(),
        ));

        // Early returns
        if spec_set.is_empty() {
            trace!("[rewrite_fn_item] exit");
            return SmallVector::one(ptr::P(item));
        }
        if let ast::ItemKind::Fn(_, fn_header, ..) = item.node {
            if is_unsafe(fn_header) {
                trace!("[rewrite_fn_item] exit");
                return SmallVector::one(ptr::P(item));
            }
        }

        // Dump modified item
        let new_item_str = syntax::print::pprust::item_to_string(&item);
        debug!("new_item:\n{}", new_item_str);
        self.log_modified_program(new_item_str);

        // Create spec item
        let mut spec_item = self.generate_spec_item(&item, id, &preconditions, &postconditions);
        spec_item
            .attrs
            .extend(item.attrs.iter().cloned().filter(|attr| {
                !attr.check_name("trusted")
                    && !attr.check_name("pure")
                    && !attr.check_name("invariant")
                    && !attr.check_name("requires")
                    && !attr.check_name("ensures")
                    && !attr.check_name(PRUSTI_SPEC_ATTR)
            }));

        // Dump spec item
        let spec_item_str = syntax::print::pprust::item_to_string(&spec_item);
        debug!("spec_item:\n{}", spec_item_str);
        self.log_modified_program(spec_item_str);

        // Return small vector
        trace!("[rewrite_fn_item] exit");
        let mut result = SmallVector::new();
        result.push(ptr::P(item));
        result.push(ptr::P(spec_item));
        result
    }

    fn rewrite_impl_item_method(
        &mut self,
        mut impl_item: ast::ImplItem,
    ) -> (SmallVector<ast::ImplItem>, SmallVector<ast::ImplItem>) {
        trace!("[rewrite_impl_item_method] enter");

        // Parse specification
        let specs = self.parse_specs(impl_item.attrs.clone());
        if specs.iter().any(|spec| spec.typ == SpecType::Invariant) {
            self.report_error(impl_item.span, "invariant not allowed for procedure");
            return (SmallVector::one(impl_item), SmallVector::new());
        }
        let preconditions: Vec<_> = specs
            .clone()
            .into_iter()
            .filter(|spec| spec.typ == SpecType::Precondition)
            .collect();
        let postconditions: Vec<_> = specs
            .into_iter()
            .filter(|spec| spec.typ == SpecType::Postcondition)
            .collect();
        let spec_set = SpecificationSet::Procedure(preconditions.clone(), postconditions.clone());

        // Register specification
        let id = self.register_specification(spec_set.clone());
        impl_item.attrs.push(self.ast_builder.attribute_name_value(
            impl_item.span,
            PRUSTI_SPEC_ATTR,
            &id.to_string(),
        ));

        // Early returns
        if spec_set.is_empty() {
            trace!("[rewrite_impl_item_method] exit");
            return (SmallVector::one(impl_item), SmallVector::new());
        }
        if let ast::ImplItemKind::Method(ast::MethodSig { header, .. }, ..) = impl_item.node {
            if is_unsafe(header) {
                trace!("[rewrite_impl_item_method] exit");
                return (SmallVector::one(impl_item), SmallVector::new());
            }
        }

        // Dump modified item
        let new_item_str = syntax::print::pprust::impl_item_to_string(&impl_item);
        debug!("new_item:\n{}", new_item_str);
        self.log_modified_program(new_item_str);

        // Create spec item
        let mut spec_item =
            self.generate_spec_impl_item(&impl_item, id, &preconditions, &postconditions);
        spec_item
            .attrs
            .extend(impl_item.attrs.iter().cloned().filter(|attr| {
                !attr.check_name("trusted")
                    && !attr.check_name("pure")
                    && !attr.check_name("invariant")
                    && !attr.check_name("requires")
                    && !attr.check_name("ensures")
                    && !attr.check_name(PRUSTI_SPEC_ATTR)
            }));

        // Dump spec item
        let spec_item_str = syntax::print::pprust::impl_item_to_string(&spec_item);
        debug!("spec_item:\n{}", spec_item_str);
        self.log_modified_program(spec_item_str);

        // Return small vector
        trace!("[rewrite_impl_item_method] exit");
        (SmallVector::one(impl_item), SmallVector::one(spec_item))
    }

    fn rewrite_struct_item(&mut self, item: ptr::P<ast::Item>) -> SmallVector<ptr::P<ast::Item>> {
        trace!("[rewrite_struct_item] enter");
        let mut item = item.into_inner();

        let mut result = SmallVector::new();

        // Parse specification for struct
        let struct_specs = self.parse_specs(item.attrs.clone());
        if struct_specs
            .iter()
            .any(|spec| spec.typ != SpecType::Invariant)
        {
            self.report_error(item.span, "only invariant allowed for struct");
        } else {
            let struct_invariants: Vec<_> = struct_specs
                .clone()
                .into_iter()
                .filter(|spec| spec.typ == SpecType::Invariant)
                .collect();
            let struct_spec_set = SpecificationSet::Struct(struct_invariants.clone());

            // Register specification
            let struct_spec_id = self.register_specification(struct_spec_set.clone());

            if !struct_spec_set.is_empty() {
                // Dump modified item
                let new_item_str = syntax::print::pprust::item_to_string(&item);
                debug!("new_item:\n{}", new_item_str);
                self.log_modified_program(new_item_str);

                // Create spec item
                let mut struct_spec_item = self.generate_spec_item_inv(
                    &item,
                    struct_spec_id,
                    &struct_invariants,
                    None,
                    None,
                );

                struct_spec_item
                    .attrs
                    .extend(item.attrs.iter().cloned().filter(|attr| {
                        !attr.check_name("trusted")
                            && !attr.check_name("pure")
                            && !attr.check_name("invariant")
                            && !attr.check_name("requires")
                            && !attr.check_name("ensures")
                            && !attr.check_name(PRUSTI_SPEC_ATTR)
                    }));

                // Dump spec item
                let spec_item_str = syntax::print::pprust::item_to_string(&struct_spec_item);
                debug!("spec_item:\n{}", spec_item_str);
                self.log_modified_program(spec_item_str);
                item.attrs.push(self.ast_builder.attribute_name_value(
                    item.span,
                    PRUSTI_SPEC_ATTR,
                    &struct_spec_id.to_string(),
                ));
                result.push(ptr::P(struct_spec_item));
            }
        }

        let register = self.register.clone();
        {
            let mut reg = register.lock().unwrap();
            for (reg_id, id_opt, impl_item, tr_attrs) in reg.get_relevant_traits(&item).clone() {
                let specs = self.parse_specs(tr_attrs);
                if specs
                    .iter()
                    .any(|spec| spec.typ != SpecType::Invariant && !spec.typ.is_refines())
                {
                    let span = reg.get_trait_span(&reg_id).unwrap_or(item.span.clone());
                    self.report_error(
                        span,
                        "only invariants or contract refinement allowed for traits",
                    );
                    continue;
                }
                let invariants: Vec<_> = specs
                    .clone()
                    .into_iter()
                    .filter(|spec| spec.typ == SpecType::Invariant)
                    .collect();
                let spec_set = SpecificationSet::Struct(invariants.clone());
                if !spec_set.is_empty() {
                    let id = if let Some(id) = id_opt {
                        self.replace_specification(id, spec_set.clone());
                        id
                    } else {
                        let id = self.register_specification(spec_set.clone());
                        reg.register_specid(reg_id.clone(), id.clone());
                        id
                    };

                    let trait_name = reg_id.to_string();
                    let trait_spec_item = self.generate_spec_item_inv(
                        &item,
                        id,
                        &invariants,
                        Some(&trait_name),
                        Some(impl_item),
                    );

                    result.push(ptr::P(trait_spec_item));
                }
            }
        }

        trace!("[rewrite_struct_item] exit");
        result.push(ptr::P(item));
        result
    }

    fn rewrite_trait_item_method(
        &mut self,
        mut trait_item: ast::TraitItem,
        mut inherited_specs: Vec<UntypedSpecification>,
    ) -> SmallVector<ast::TraitItem> {
        trace!("[rewrite_trait_item_method] enter");

        // Parse specification
        let mut specs = self.parse_specs(trait_item.attrs.clone());
        specs.append(&mut inherited_specs);

        if specs.iter().any(|spec| spec.typ == SpecType::Invariant) {
            self.report_error(trait_item.span, "invariant not allowed for procedure");
            return SmallVector::one(trait_item);
        }
        // TODO(@jakob): register all specs
        let preconditions: Vec<_> = specs
            .clone()
            .into_iter()
            .filter(|spec| spec.typ.is_precondition())
            .collect();
        let postconditions: Vec<_> = specs
            .into_iter()
            .filter(|spec| spec.typ.is_postcondition())
            .collect();
        let spec_set = SpecificationSet::Procedure(preconditions.clone(), postconditions.clone());

        // Register specification
        let id = self.register_specification(spec_set.clone());
        match trait_item.node {
            ast::TraitItemKind::Method(_, Some(_)) => {
                trait_item.attrs.push(self.ast_builder.attribute_name_value(
                    trait_item.span,
                    PRUSTI_SPEC_ATTR,
                    &id.to_string(),
                ));
            }
            // TODO: correct?
            ast::TraitItemKind::Method(_, None) => {
                trait_item.attrs.push(self.ast_builder.attribute_name_value(
                    trait_item.span,
                    PRUSTI_SPEC_ATTR,
                    &id.to_string(),
                ));
            }
            _ => unreachable!(),
        }

        // Early returns
        if spec_set.is_empty() {
            trace!("[rewrite_trait_item_method] exit");
            return SmallVector::one(trait_item);
        }
        if let ast::TraitItemKind::Method(ast::MethodSig { header, .. }, ..) = trait_item.node {
            if is_unsafe(header) {
                trace!("[rewrite_trait_item_method] exit");
                return SmallVector::one(trait_item);
            }
        }

        // Dump modified item
        let new_item_str = syntax::print::pprust::trait_item_to_string(&trait_item);
        debug!("new_item:\n{}", new_item_str);
        self.log_modified_program(new_item_str);

        // Create spec item
        let mut spec_item =
            self.generate_spec_trait_item(&trait_item, id, &preconditions, &postconditions);
        spec_item
            .attrs
            .extend(trait_item.attrs.iter().cloned().filter(|attr| {
                !attr.check_name("trusted")
                    && !attr.check_name("pure")
                    && !attr.check_name("invariant")
                    && !attr.check_name("requires")
                    && !attr.check_name("ensures")
                    && !attr.check_name(PRUSTI_SPEC_ATTR)
            }));

        // Dump spec item
        let spec_item_str = syntax::print::pprust::trait_item_to_string(&spec_item);
        debug!("spec_item:\n{}", spec_item_str);
        self.log_modified_program(spec_item_str);

        // Return small vector
        trace!("[rewrite_trait_item_method] exit");
        let mut result = SmallVector::new();
        result.push(trait_item);
        result.push(spec_item);
        result
    }

    /// Extracts specification string from the attribute with the
    /// correct base span.
    fn extract_spec_string(
        &self,
        attribute: &ast::Attribute,
    ) -> Option<(String, Span, Option<FunctionRef>)> {
        use syntax::parse::token;
        use syntax::tokenstream::{Delimited, TokenStream, TokenTree};

        let trees: Vec<TokenTree> = attribute.tokens.trees().collect();
        let tree_len = trees.len();

        if tree_len == 0 {
            self.report_error(
                attribute.span,
                "malformed specification (no arguments provided)",
            );
            return None;
        }

        let mut function_ref = None;
        let spec_tree = match trees[0] {
            TokenTree::Token(_, ref token) => {
                if *token != token::Token::Eq {
                    self.report_error(
                        attribute.span,
                        "malformed specification (expected equality)",
                    );
                    return None;
                }
                trees[1].clone()
            }
            TokenTree::Delimited(
                _,
                Delimited {
                    delim: token::DelimToken::Paren,
                    ref tts,
                },
            ) => {
                let token_stream: TokenStream = tts.clone().into();
                let spec_trees: Vec<TokenTree> = token_stream.trees().collect();
                if spec_trees.len() == 1 {
                    spec_trees[0].clone()
                } else if spec_trees.len() == 5 && attribute.path.to_string().starts_with("refine_")
                {
                    // len 5 because 5 inner tokens in #[refine_...(Trait::method="contract")]
                    //                                              111112233333345555555555
                    let trait_symbol =
                        if let TokenTree::Token(_, token::Token::Ident(ref ident, _)) =
                            spec_trees[0]
                        {
                            ident.name.clone()
                        } else {
                            self.report_error(
                                attribute.span,
                                "malformed specification (expected trait identifier)",
                            );
                            return None;
                        };
                    if let TokenTree::Token(_, token::Token::ModSep) = spec_trees[1] {
                    } else {
                        self.report_error(
                            attribute.span,
                            "malformed specification (expected separator)",
                        );
                        return None;
                    }
                    let func_symbol =
                        if let TokenTree::Token(_, token::Token::Ident(ref ident, _)) =
                            spec_trees[2]
                        {
                            ident.name.clone()
                        } else {
                            self.report_error(
                                attribute.span,
                                "malformed specification (expected function identifier)",
                            );
                            return None;
                        };
                    if let TokenTree::Token(_, token::Token::Eq) = spec_trees[3] {
                    } else {
                        self.report_error(
                            attribute.span,
                            "malformed specification (expected equality)",
                        );
                        return None;
                    }
                    function_ref = Some((trait_symbol, func_symbol));
                    spec_trees[4].clone()
                } else {
                    self.report_error(
                        attribute.span,
                        "malformed specification (expected single argument)",
                    );
                    return None;
                }
            }
            _ => {
                self.report_error(attribute.span, "malformed specification (expected token)");
                return None;
            }
        };
        let spec_string_with_span = match spec_tree {
            TokenTree::Token(span, ref token) => match *token {
                token::Token::Literal(ref lit, None) => match *lit {
                    token::Lit::Str_(ref name) => {
                        let name: &str = &name.as_str();
                        let spec = String::from(name);
                        Some((spec, span, function_ref))
                    }
                    token::Lit::StrRaw(ref name, delimiter_size) => {
                        let name: &str = &name.as_str();
                        let spec = String::from(name);
                        Some((
                            spec,
                            shift_span(span, (delimiter_size + 1) as u32),
                            function_ref,
                        ))
                    }
                    _ => None,
                },
                _ => None,
            },
            _ => None,
        };
        if spec_string_with_span.is_none() {
            self.report_error(
                attribute.span,
                "malformed specification (failed to parse specification string)",
            );
        }
        spec_string_with_span
    }

    fn parse_typaram_condition(
        &mut self,
        span: &mut Span,
        spec_string: &mut &str,
    ) -> Option<ForAllVars<ast::Arg>> {
        // FIXME... the uglier the better
        if let Some(pos) = spec_string.find("~~>") {
            let foo = &spec_string[..pos];
            let (ty1, ty2) = self.parse_type(*span, foo.to_string()).unwrap(); // FIXME span
            let arg1 = self.ast_builder.arg(
                *span,
                self.ast_builder.ident_of("t1"),
                ty1, // FIXME
            );
            let arg2 = self.ast_builder.arg(
                *span,
                self.ast_builder.ident_of("t2"),
                ty2, // FIXME
            );
            let forallvars = ForAllVars {
                // is actually a "FORALL_ID"
                id: self.get_new_expression_id(),
                vars: vec![arg1, arg2],
            };
            *spec_string = &spec_string[pos + 3..];
            *span = shift_span(*span, (pos + 3) as u32);
            Some(forallvars)
        } else {
            None
        }
    }

    fn parse_assertion_wrap(&mut self, span: Span, spec_string: &str) -> Option<UntypedAssertion> {
        match self.parse_assertion(span, spec_string) {
            Ok(assertion) => Some(assertion),
            Err(AssertionParsingError::NotMatchingParenthesis) => {
                self.report_error(span, "not matching parenthesis");
                None
            }
            Err(AssertionParsingError::ParsingRustExpressionFailed)
            | Err(AssertionParsingError::FailedForallMatch)
            | Err(AssertionParsingError::FailedAfterExpiryMatch) => None,
        }
    }

    /// Parses attribute into specification.
    /// TODO: Rewrite to use the [syn](https://crates.io/crates/syn) crate.
    fn parse_specs(&mut self, attributes: Vec<ast::Attribute>) -> Vec<UntypedSpecification> {
        trace!("[parse_specs] enter attributes.len={}", attributes.len());

        let specifications: Vec<_> = attributes
            .into_iter()
            .map(|attribute| {
                if let Ok(spec_type) = SpecType::try_from(&attribute.path.to_string() as &str) {
                    if let Some((spec_string, mut span, function_ref)) =
                        self.extract_spec_string(&attribute)
                    {
                        // FIXME ugly code
                        let mut spec_string: &str = &spec_string;
                        let foo = self.parse_typaram_condition(&mut span, &mut spec_string);
                        if let Some(assertion) = self.parse_assertion_wrap(span, &spec_string) {
                            let assertion = match foo {
                                Some(x) => Assertion {
                                    kind: box AssertionKind::TypeCond(x, assertion),
                                },
                                None => assertion,
                            };
                            debug!("assertion={:?}", assertion);
                            let mut new_spec_type = spec_type;
                            if function_ref.is_some() {
                                new_spec_type = match spec_type {
                                    SpecType::RefinePrecondition(_) => {
                                        SpecType::RefinePrecondition(function_ref)
                                    }
                                    SpecType::RefinePostcondition(_) => {
                                        SpecType::RefinePostcondition(function_ref)
                                    }
                                    _ => {
                                        self.report_error(
                                            attribute.span,
                                            "malformed specification",
                                        );
                                        return None;
                                    }
                                }
                            }
                            Some(UntypedSpecification {
                                typ: new_spec_type,
                                assertion: assertion,
                            })
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                } else {
                    // TODO: Report error only on attributes with  the "prusti" namespace
                    //self.report_error(attribute.span, "unsupported attribute");
                    None
                }
            })
            .filter(|spec| spec.is_some())
            .map(|spec| spec.unwrap())
            .collect();

        trace!("[parse_specs] exit");
        specifications
    }

    /// Parse Rust expression.
    fn parse_expression(
        &mut self,
        base_span: Span,
        spec_string: String,
    ) -> Result<ptr::P<ast::Expr>, AssertionParsingError> {
        trace!(
            "[parse_expression] enter spec_string={:?} span={:?}",
            spec_string,
            base_span
        );
        let mut whitespace_count = 0;
        for char in spec_string.chars() {
            if !char.is_whitespace() {
                break;
            }
            whitespace_count += 1;
        }
        let expr = parse::new_parser_from_source_str(
            &self.session.parse_sess,
            FileName::QuoteExpansion,
            spec_string,
        )
        .parse_expr();
        debug!("Parsed expr: {:?}", expr);
        let result = match expr {
            Ok(expr) => {
                let mut rewriter = SpanRewriter::new(whitespace_count, expr.span, base_span);
                let expr = rewriter.fold_expr(expr);
                Ok(expr)
            }
            Err(mut err) => {
                err.emit();
                Err(AssertionParsingError::ParsingRustExpressionFailed)
            }
        };
        trace!("[parse_expression] exit");
        result
    }

    /// Parse Rust type. (copied from parse_expression)
    fn parse_type(
        &mut self,
        base_span: Span,
        spec_string: String,
    ) -> Result<(ptr::P<ast::Ty>, ptr::P<ast::Ty>), AssertionParsingError> {
        trace!(
            "[parse_ty] enter spec_string={:?} span={:?}",
            spec_string,
            base_span
        );
        //let mut whitespace_count = 0;
        //for char in spec_string.chars() {
        //    if !char.is_whitespace() {
        //        break;
        //    }
        //    whitespace_count += 1;
        //}
        let mut parser = parse::new_parser_from_source_str(
            &self.session.parse_sess,
            FileName::QuoteExpansion,
            spec_string,
        );
        let expr = parser.parse_ty();
        //parser.expected_tokens.clear();
        match parser.expect(&parse::token::Token::EqEq) {
            Ok(_) => {}
            Err(mut err) => {
                err.emit();
                return Err(AssertionParsingError::ParsingRustExpressionFailed);
            }
        }
        let expr2 = parser.parse_ty();
        // TODO expect "eof" after parsing!
        debug!("Parsed ty: {:?}", expr);
        return Ok((expr.unwrap(), expr2.unwrap()));
        //let result = match expr {
        //    Ok(expr) => {
        //        let mut rewriter = SpanRewriter::new(whitespace_count, expr.span, base_span);
        //        let expr = rewriter.fold_ty(expr);
        //        Ok(expr)
        //    }
        //    Err(mut err) => {
        //        err.emit();
        //        Err(AssertionParsingError::ParsingRustExpressionFailed)
        //    }
        //};
        //trace!("[parse_ty] exit");
        //result
    }

    fn parse_vars(
        &mut self,
        span: Span,
        var_match: regex::Match,
    ) -> Result<Vec<ast::Arg>, AssertionParsingError> {
        let span = shift_resize_span(
            span,
            var_match.start() as u32,
            var_match.as_str().len() as u32,
        );
        let vars_string = var_match.as_str();
        let mut vars = Vec::new();
        lazy_static! {
            static ref RE: Regex =
                Regex::new(r"^\s*([a-z][a-z0-9]*)\s*:\s*([a-z][a-z0-9]*)\s*$").unwrap();
        }
        let builder = &self.ast_builder;
        for var_string in vars_string.split(',') {
            if let Some(caps) = RE.captures(var_string) {
                let name = &caps[1];
                let typ = &caps[2];
                let var = builder.arg(
                    span,
                    builder.ident_of(name),
                    builder.ty_ident(span, builder.ident_of(typ)),
                );
                vars.push(var);
            } else {
                self.report_error(span, "failed to parse forall bounded variable list");
                return Err(AssertionParsingError::FailedForallMatch);
            };
        }
        Ok(vars)
    }

    fn parse_triggers(
        &mut self,
        span: Span,
        trigger_match: regex::Match,
    ) -> Result<UntypedTriggerSet, AssertionParsingError> {
        let span = shift_resize_span(
            span,
            trigger_match.start() as u32,
            trigger_match.as_str().len() as u32,
        );
        let trigger_set_string = trigger_match.as_str();
        let mut triggers = Vec::new();
        for trigger_string in trigger_set_string.split(';') {
            let mut terms = Vec::new();
            for term in trigger_string.split(',') {
                let term = self.parse_expression(span, String::from(term))?;
                let expr = Expression {
                    id: self.get_new_expression_id(),
                    expr: term,
                };
                terms.push(expr);
            }
            triggers.push(Trigger::new(terms));
        }
        Ok(TriggerSet::new(triggers))
    }

    fn parse_forall_expr(
        &mut self,
        span: Span,
        expr_match: regex::Match,
    ) -> Result<ptr::P<ast::Expr>, AssertionParsingError> {
        let expr_string = String::from(expr_match.as_str());
        if expr_string.contains("==>") {
            self.report_error(span, "forall can have only one implication");
            return Err(AssertionParsingError::FailedForallMatch);
        }
        let span = shift_resize_span(
            span,
            expr_match.start() as u32,
            expr_match.as_str().len() as u32,
        );
        self.parse_expression(span, expr_string)
    }

    // TODO: name; now also parses "assert_on_expiry"
    fn parse_after_expiry(
        &mut self,
        span: Span,
        spec_string: &str,
    ) -> Result<UntypedAssertion, AssertionParsingError> {
        let is_postcondition = true;
        lazy_static! {
            static ref POSTCONDITION_RE: Regex = Regex::new(
                r"(?sx)
                ^(?P<whitespace1>\s*(?P<construct>(after|assert_on)_expiry)\s*(<result>)?\s*\()
                (?P<body>.*)
                (?P<whitespace2>\)\s*)$
            "
            )
            .unwrap();
        }
        lazy_static! {
            static ref NON_POSTCONDITION_RE: Regex = Regex::new(
                r"(?sx)
                ^\s*after_expiry\s*
                (<(?P<reference>[a-zA-Z0-9_]+)>)?
                \s*\((?P<body>.*)\)\s*$
            "
            )
            .unwrap();
        }
        let captures_result = if is_postcondition {
            POSTCONDITION_RE.captures(spec_string)
        } else {
            NON_POSTCONDITION_RE.captures(spec_string)
        };
        if let Some(caps) = captures_result {
            let reference = if !is_postcondition {
                let reference_match = match caps.name("reference") {
                    Some(m) => self.parse_forall_expr(span, m)?,
                    None => self.parse_expression(span, String::from("result"))?,
                };
                let reference_use = self.ast_builder.expr_addr_of(span, reference_match);
                let reference_expr = Expression {
                    id: self.get_new_expression_id(),
                    expr: reference_use,
                };
                Some(reference_expr)
            } else {
                None
            };
            let body_str = caps.name("body").unwrap().as_str();
            let (lhs_str, rhs_str) = match caps.name("construct").unwrap().as_str() {
                "after_expiry" => {
                    // after_expiry(rhs) // lhs == true
                    ("true", body_str)
                }
                "assert_on_expiry" => {
                    // assert_on_expiry(lhs[, rhs]) // default: rhs == true
                    let mut iter = body_str.rsplitn(2, ',');
                    let one = iter.next();
                    let two = iter.next();
                    if two.is_none() {
                        (one.unwrap(), "true")
                    } else {
                        (two.unwrap(), one.unwrap())
                    }
                }
                _ => unreachable!(),
            };
            let new_span = {
                let whitespace1_len = caps.name("whitespace1").unwrap().as_str().len();
                shift_resize_span(span, whitespace1_len as u32, body_str.len() as u32)
            };
            let lhs = self.parse_assertion(new_span, lhs_str)?;
            let rhs = self.parse_assertion(new_span, rhs_str)?;
            debug!(
                "after_expiry: reference={:?} lhs={:?} rhs={:?}",
                reference, lhs, rhs
            );
            let assertion = UntypedAssertion {
                kind: box AssertionKind::Pledge(reference, lhs, rhs),
            };
            Ok(assertion)
        } else {
            self.report_error(span, "failed to parse after_expiry expression");
            Err(AssertionParsingError::FailedAfterExpiryMatch)
        }
    }

    fn parse_forall(
        &mut self,
        span: Span,
        spec_string: &str,
    ) -> Result<UntypedAssertion, AssertionParsingError> {
        trace!("[enter] parse_forall spec_string={}", spec_string);
        let spec_string_without_parenthesis = {
            // Remove parenthesis.
            lazy_static! {
                static ref RE: Regex = Regex::new(
                    r"(?sx)
                    ^\s*\(\s*(?P<forall>.*)\s*\)\s*$
                ",
                )
                .unwrap();
            }
            if let Some(caps) = RE.captures(spec_string) {
                caps.name("forall").unwrap().as_str().to_string()
            } else {
                spec_string.to_string()
            }
        };
        debug!(
            "parse_forall spec_string_without_parenthesis={}",
            spec_string_without_parenthesis
        );
        lazy_static! {
            static ref RE: Regex = Regex::new(
                r"(?sx)
                ^\s*forall\s*
                (?P<vars>.*)\s*::\s*(\{(?P<triggers>.*)\})?\s*
                (?P<filter>.*)\s*==>\s*(?P<body>.*)\s*$
            ",
            )
            .unwrap();
        }
        if let Some(caps) = RE.captures(&spec_string_without_parenthesis) {
            let vars = self.parse_vars(span, caps.name("vars").unwrap())?;
            let triggers = match caps.name("triggers") {
                Some(triggers) => self.parse_triggers(span, triggers)?,
                None => TriggerSet::new(vec![]),
            };
            let filter = self.parse_forall_expr(span, caps.name("filter").unwrap())?;
            let body = self.parse_forall_expr(span, caps.name("body").unwrap())?;
            debug!(
                "forall: vars={:?} triggers={:?} filter={:?} body={:?}",
                vars, triggers, filter, body
            );
            let assertion = UntypedAssertion {
                kind: box AssertionKind::ForAll(
                    ForAllVars {
                        id: self.get_new_expression_id(),
                        vars: vars,
                    },
                    triggers,
                    UntypedAssertion {
                        kind: box AssertionKind::Implies(
                            UntypedAssertion {
                                kind: box AssertionKind::Expr(Expression {
                                    id: self.get_new_expression_id(),
                                    expr: filter,
                                }),
                            },
                            UntypedAssertion {
                                kind: box AssertionKind::Expr(Expression {
                                    id: self.get_new_expression_id(),
                                    expr: body,
                                }),
                            },
                        ),
                    },
                ),
            };
            Ok(assertion)
        } else {
            self.report_error(span, "failed to parse forall expression");
            Err(AssertionParsingError::FailedForallMatch)
        }
    }

    /// Parse an assertion string into an assertion object.
    /// The assertion string can only contain an implication, forall, or a
    /// Rust expression.
    fn parse_assertion_simple(
        &mut self,
        span: Span,
        spec_string: String,
    ) -> Result<UntypedAssertion, AssertionParsingError> {
        trace!(
            "[parse_assertion_simple] enter spec_string={:?}",
            spec_string
        );

        // Drop surrounding parenthesis.
        {
            lazy_static! {
                static ref RE: Regex = Regex::new(r"^(\s*\()(.*)\)\s*$").unwrap();
            }
            if let Some(caps) = RE.captures(&spec_string) {
                let new_span = shift_span(span, caps[1].len() as u32);
                return self.parse_assertion_simple(new_span, String::from(&caps[2]));
            }
        }

        // Parse after_expiry or assert_on_expiry.
        if spec_string.contains("after_expiry") || spec_string.contains("assert_on_expiry") {
            return self.parse_after_expiry(span, &spec_string);
        }

        // Parse forall.
        if spec_string.contains("forall")
            && (!spec_string.contains("==>")
                || spec_string.find("forall").unwrap() < spec_string.find("==>").unwrap())
        {
            return self.parse_forall(span, &spec_string);
        }

        // Parse the implication.
        {
            let mut parenthesis_depth = 0;
            let iter = spec_string.char_indices().peekable();
            let mut last2 = None;
            let mut last1 = None;
            for (position, char) in iter {
                if char == '(' {
                    parenthesis_depth += 1;
                    last1 = None;
                    continue;
                }
                if char == ')' {
                    parenthesis_depth -= 1;
                    if parenthesis_depth < 0 {
                        return Err(AssertionParsingError::NotMatchingParenthesis);
                    }
                    last1 = None;
                    continue;
                }
                if parenthesis_depth == 0 && last2 == Some('=') && last1 == Some('=') && char == '>'
                {
                    let expr = substring(&spec_string, 0, position - 2);
                    let expr = self.parse_expression(span, expr)?;
                    let assertion = substring(&spec_string, position + 1, spec_string.len());
                    let new_span = shift_span(span, (position + 1) as u32);
                    let assertion = self.parse_assertion(new_span, &assertion)?;
                    let precondition = Expression {
                        id: self.get_new_expression_id(),
                        expr: expr,
                    };
                    // TODO: Report the bug that the following line
                    // gives a compiler error.
                    //let kind = UntypedAssertionKind::Implies(precondition, assertion);
                    return Ok(UntypedAssertion {
                        kind: box AssertionKind::Implies(
                            Assertion {
                                kind: box AssertionKind::Expr(precondition),
                            },
                            assertion,
                        ),
                    });
                }
                last2 = last1;
                last1 = Some(char);
            }
            if parenthesis_depth != 0 {
                return Err(AssertionParsingError::NotMatchingParenthesis);
            }
        }

        // We have a simple Rust expression.
        let expr = self.parse_expression(span, spec_string)?;
        let assertion = UntypedAssertion {
            kind: box AssertionKind::Expr(Expression {
                id: self.get_new_expression_id(),
                expr: expr,
            }),
        };
        trace!("[parse_assertion_simple] exit");
        Ok(assertion)
    }

    /// Parse a specification string into an assertion object.
    ///
    /// This method works by splitting assertion on `&&` and recursively
    /// parsing each conjunct.
    fn parse_assertion(
        &mut self,
        span: Span,
        spec_string: &str,
    ) -> Result<UntypedAssertion, AssertionParsingError> {
        trace!("[parse_assertion] enter spec_string={:?}", spec_string);
        let mut iter = spec_string.char_indices().peekable();
        let mut block_start = 0;
        let mut assertions: Vec<UntypedAssertion> = Vec::new();
        let mut parenthesis_depth = 0;
        while let Some((position, char)) = iter.next() {
            if char == '(' {
                parenthesis_depth += 1;
                continue;
            }
            if char == ')' {
                parenthesis_depth -= 1;
                if parenthesis_depth < 0 {
                    return Err(AssertionParsingError::NotMatchingParenthesis);
                }
                continue;
            }
            if parenthesis_depth == 0 && char == '&' {
                if let Some(&(_, '&')) = iter.peek() {
                    iter.next();
                    let block = substring(spec_string, block_start, position);
                    let new_span = shift_span(span, block_start as u32);
                    let assertion = self.parse_assertion(new_span, &block)?;
                    assertions.push(assertion);
                    block_start = position + 2;
                }
            }
        }
        if parenthesis_depth != 0 {
            return Err(AssertionParsingError::NotMatchingParenthesis);
        }
        let block = substring(spec_string, block_start, spec_string.len());
        let new_span = shift_span(span, block_start as u32);
        let last_assertion = self.parse_assertion_simple(new_span, block)?;
        let assertion = if assertions.is_empty() {
            last_assertion
        } else {
            assertions.push(last_assertion);
            Assertion {
                kind: box AssertionKind::And(assertions),
            }
        };

        trace!("[parse_assertion] exit");
        Ok(assertion)
    }
}

impl<'tcx> Folder for SpecParser<'tcx> {
    fn fold_crate(&mut self, c: ast::Crate) -> ast::Crate {
        let mut krate = fold::noop_fold_crate(c, self);
        // Avoid compiler error "unstable feature"
        krate.attrs.push(
            self.ast_builder
                .attribute_allow(krate.span, "unstable_features"),
        );
        // Avoid compiler error "attributes on expressions are experimental. (see issue #15701)"
        krate.attrs.push(
            self.ast_builder
                .attribute_feature(krate.span, "stmt_expr_attributes"),
        );
        /*
        // Automatically add "extern crate prusti_constracts"
        krate.module.items.push(
            self.ast_builder.item_extern_crate(
                krate.span,
                self.ast_builder.ident_of("prusti_contracts")
            )
        );
        */
        krate
    }

    fn fold_item(&mut self, item: ptr::P<ast::Item>) -> SmallVector<ptr::P<ast::Item>> {
        trace!("[fold_item] enter");
        let result = fold::noop_fold_item(item, self)
            .into_iter()
            .flat_map(|item| match item.node.clone() {
                // Top-level functions
                ast::ItemKind::Fn(..) => self.rewrite_fn_item(item),

                // Structs
                ast::ItemKind::Struct(..) => self.rewrite_struct_item(item),

                // Impl methods
                ast::ItemKind::Impl(
                    unsafety,
                    polarity,
                    defaultness,
                    generics,
                    ifce,
                    ty,
                    impl_items,
                ) => {
                    let mut new_code_items = vec![];
                    let mut new_spec_items = vec![];

                    for impl_item in impl_items.into_iter() {
                        match impl_item.node {
                            ast::ImplItemKind::Method(..) => {
                                let (code_items, spec_items) =
                                    self.rewrite_impl_item_method(impl_item);
                                new_code_items.extend(code_items);
                                new_spec_items.extend(spec_items);
                            }
                            _ => new_code_items.push(impl_item),
                        }
                    }

                    let mut new_items = SmallVector::new();
                    if !new_spec_items.is_empty() {
                        new_items.push(ptr::P(ast::Item {
                            node: ast::ItemKind::Impl(
                                ast::Unsafety::Normal,
                                polarity,
                                defaultness,
                                generics.clone(),
                                None,
                                ty.clone(),
                                new_spec_items,
                            ),
                            ..item.clone().into_inner()
                        }))
                    }
                    new_items.push(ptr::P(ast::Item {
                        node: ast::ItemKind::Impl(
                            unsafety,
                            polarity,
                            defaultness,
                            generics,
                            ifce,
                            ty,
                            new_code_items,
                        ),
                        ..item.into_inner()
                    }));
                    new_items
                }

                // Methods in trait definition
                ast::ItemKind::Trait(is_auto, unsafety, generics, bounds, trait_items) => {
                    let mut item = item.into_inner();

                    let trait_symbol = item.ident.name.clone();
                    let (trait_id, is_registered, funcs_symbols) = {
                        let reg = self.register.lock().unwrap();
                        (
                            reg.get_id(&item),
                            reg.is_trait_specid_registered(&item),
                            reg.get_funcs_for_trait(&trait_symbol),
                        )
                    };
                    if !is_registered {
                        let empty_spec = SpecificationSet::Struct(Vec::new());
                        let specid = self.register_specification(empty_spec);
                        {
                            let mut reg = self.register.lock().unwrap();
                            reg.register_specid(trait_id, specid.clone());
                        }
                        item.attrs.push(self.ast_builder.attribute_name_value(
                            item.span,
                            PRUSTI_SPEC_ATTR,
                            &specid.to_string(),
                        ));
                    }

                    let trait_symbols: HashSet<Symbol> = trait_items
                        .clone()
                        .into_iter()
                        .map(|item| item.ident.name)
                        .collect();

                    for symbol in funcs_symbols {
                        if !trait_symbols.contains(&symbol) {
                            self.report_error(
                                item.span,
                                &format!("no method '{}' in super trait", symbol),
                            );
                        }
                    }

                    let mut new_trait_items = vec![];
                    for trait_item in trait_items.into_iter() {
                        match trait_item.node {
                            ast::TraitItemKind::Method(..) => {
                                let method_symbol = trait_item.ident.name.clone();
                                let func_ref = (trait_symbol.clone(), method_symbol);
                                let func_attrs = {
                                    let reg = self.register.lock().unwrap();
                                    reg.get_attrs_refine(&func_ref)
                                };
                                let func_specs = self.parse_specs(func_attrs);
                                new_trait_items
                                    .extend(self.rewrite_trait_item_method(trait_item, func_specs));
                            }
                            _ => new_trait_items.push(trait_item),
                        }
                    }

                    SmallVector::one(ptr::P(ast::Item {
                        node: ast::ItemKind::Trait(
                            is_auto,
                            unsafety,
                            generics,
                            bounds,
                            new_trait_items,
                        ),
                        ..item
                    }))
                }

                // Any other item
                _ => SmallVector::one(item),
            })
            .collect();
        trace!("[fold_item] exit");
        result
    }

    fn fold_expr(&mut self, expr: ptr::P<ast::Expr>) -> ptr::P<ast::Expr> {
        match expr.node {
            ast::ExprKind::While(..)
            | ast::ExprKind::WhileLet(..)
            | ast::ExprKind::ForLoop(..)
            | ast::ExprKind::Loop(..) => self.rewrite_loop(expr),
            _ => expr.map(|e| syntax::fold::noop_fold_expr(e, self)),
        }
    }

    fn fold_mac(&mut self, mac: ast::Mac) -> ast::Mac {
        mac
    }
}

#[derive(Debug)]
/// An error reported when parsing of assertion fails.
pub enum AssertionParsingError {
    /// Reported when parenthesis do not match.
    NotMatchingParenthesis,
    /// Reported when Rust assertion parsing fails.
    ParsingRustExpressionFailed,
    /// Reported when matching forall expression fails.
    FailedForallMatch,
    /// Reported when matching after_expiry expression fails.
    FailedAfterExpiryMatch,
}

fn substring(string: &str, start: usize, end: usize) -> String {
    string
        .chars()
        .skip(start)
        .take(end - start)
        .collect::<String>()
}

#[derive(Debug)]
struct SpanRewriter {
    old_base_pos: syntax::codemap::BytePos,
    new_base_pos: syntax::codemap::BytePos,
}

impl SpanRewriter {
    pub fn new(whitespace_count: u32, old_base_span: Span, new_base_span: Span) -> SpanRewriter {
        let x = SpanRewriter {
            old_base_pos: old_base_span.lo(),
            new_base_pos: new_base_span.lo() + syntax::codemap::BytePos(whitespace_count),
        };
        x
    }
}

impl Folder for SpanRewriter {
    fn new_span(&mut self, sp: Span) -> Span {
        let one = syntax::codemap::BytePos(1);
        let lo = sp.lo() + self.new_base_pos - self.old_base_pos + one;
        let hi = sp.hi() + self.new_base_pos - self.old_base_pos + one;
        Span::new(lo, hi, sp.ctxt())
    }
}

fn shift_span(span: Span, offset: u32) -> Span {
    let offset = syntax::codemap::BytePos(offset);
    Span::new(span.lo() + offset, span.hi() + offset, span.ctxt())
}

fn shift_resize_span(span: Span, offset: u32, length: u32) -> Span {
    let lo = span.lo() + syntax::codemap::BytePos(offset);
    let hi = lo + syntax::codemap::BytePos(length);
    Span::new(lo, hi, span.ctxt())
}

fn is_unsafe(fn_header: ast::FnHeader) -> bool {
    match fn_header.unsafety {
        ast::Unsafety::Unsafe => true,
        ast::Unsafety::Normal => false,
    }
}
