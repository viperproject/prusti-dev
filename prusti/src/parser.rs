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
//! ```
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
//!     assertion := assertion && assertion
//!                | expression ==> assertion
//!                | (forall variable_name :: {expression} expression ==> expression)
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
//!         assertions wrapping the Rust expressions used in
//!         specifications; these are then automatically type checked by
//!         the Rust compiler. This is necessary because it seems that
//!         there is no way to call a type checker on an AST manually.
//!         The example above would be rewritten as follows:
//!
//!         ```
//!         #[__PRUSTI_SPEC = "101"]
//!         fn fib(mut n: i32) -> i32 {
//!             let mut i = 1;
//!             let mut j = 1;
//!
//!             #[__PRUSTI_SPEC = "102"]
//!             while n > 2 {
//!                 #[__PRUSTI_SPEC_ONLY = "103"]
//!                 {
//!                     if false {
//!                         use prusti_contracts::internal::* ;
//!                         __assertion(104, i > 0);
//!                         __assertion(105, j > 0);
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
//!         #[allow(unused_mut)]
//!         #[allow(dead_code)]
//!         #[allow(non_snake_case)]
//!         #[__PRUSTI_SPEC_ONLY = "106"]
//!         fn fib__spec(mut n: i32) -> i32 {
//!             use prusti_contracts::internal::* ;
//!             __assertion(107, 0 < n);
//!             __assertion(108, n < 10);
//!             let result = fib(n);
//!             __assertion(109, result > 0);
//!             result
//!         }
//!         ```
//!
//!         The first argument to `__assertion` is an `ExpressionId` of
//!         the corresponding expression.
//!
//! 3.  When the ``after_analysis`` callback is invoked:
//!
//!     1.  Traverse HIR and create a map from `ExpressionId` (first
//!         argument of `__assertion`) to HIR `Expr` (second argument of
//!         `__assertion`).
//!     2.  Construct `TypedAssertion` by traversing `UntypedAssertion`
//!         and inserting HIR expressions based on `ExpressionId`.
//!
//! Note: AST/HIR nodes are linked to assertions by specification
//! identifier that is stored as a ``__PRUSTI_SPEC`` attribute.

use ast_builder::MinimalAstBuilder;
use regex::{self, Regex};
use rustc::session::Session;
use rustc_driver::driver;
use syntax::{self, ast, parse, ptr};
use syntax::codemap::Span;
use syntax::ext::build::AstBuilder;
use syntax::fold::{self, Folder};
use syntax::util::small_vector::SmallVector;
use syntax::attr;
use syntax_pos::FileName;
use prusti_interface::specifications::{Assertion, AssertionKind, Expression, ExpressionId, ForAllVars, SpecID,
                     SpecType, SpecificationSet, Trigger, TriggerSet, UntypedAssertion,
                     UntypedExpression, UntypedSpecification, UntypedSpecificationMap,
                     UntypedSpecificationSet, UntypedTriggerSet};
use std::collections::HashMap;
use std::convert::TryFrom;
use std::mem;
use syntax::codemap::respan;
use prusti_interface::constants::PRUSTI_SPEC_ATTR;
use syntax_pos::DUMMY_SP;
use prusti_interface::report::Log;
use std::io::Write;

/// Rewrite specifications in the expanded AST to get them type-checked
/// by rustc. For more information see the module documentation.
pub fn rewrite_crate(state: &mut driver::CompileState) -> UntypedSpecificationMap {
    trace!("[rewrite_crate] enter");
    let krate = state.krate.take().unwrap();
    let source_path = match driver::source_name(state.input) {
        FileName::Real(path) => path,
        _ => unreachable!(),
    };
    let source_filename = source_path.file_name().unwrap().to_str().unwrap();
    let mut parser = SpecParser::new(state.session, &source_filename);
    state.krate = Some(parser.fold_crate(krate));
    trace!("[rewrite_crate] exit");
    parser.untyped_specifications
}

/// A data structure that extracts preconditions, postconditions,
/// and loop invariants. It also rewrites the AST for type-checking.
/// Each original assertion gets a unique `SpecID` and expression – a
/// unique `ExpressionId` that allows to map them back to their original
/// locations.
pub struct SpecParser<'tcx> {
    session: &'tcx Session,
    ast_builder: MinimalAstBuilder<'tcx>,
    last_specification_id: SpecID,
    last_expression_id: ExpressionId,
    untyped_specifications: UntypedSpecificationMap,
    rust_program_before_typechecking_writer: Box<Write>
}

impl<'tcx> SpecParser<'tcx> {
    /// Create new spec parser.
    pub fn new(session: &'tcx Session, source_filename: &str) -> SpecParser<'tcx> {
        SpecParser {
            session: session,
            ast_builder: MinimalAstBuilder::new(&session.parse_sess),
            last_specification_id: SpecID::new(),
            last_expression_id: ExpressionId::new(),
            untyped_specifications: HashMap::new(),
            rust_program_before_typechecking_writer: Log::writer("rust_program_before_typechecking", source_filename).ok().unwrap()
        }
    }

    fn log_modified_program<S: ToString>(&mut self, data: S) {
        let writer = self.rust_program_before_typechecking_writer.as_mut();
        writer.write_all(data.to_string().as_bytes()).ok().unwrap();
        writer.write_all("\n\n".to_string().as_bytes()).ok().unwrap();
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

    fn report_error(&self, span: Span, message: &str) {
        let mut err = self.session.struct_span_err(span, message);
        err.emit();
    }

    /// Construct a lambda function with given expression to make that expression
    /// to be type-checked by the Rust compiler.
    fn build_typeck_call(&self, expression: &UntypedExpression, expected_ty: Option<ptr::P<ast::Ty>>) -> ast::Stmt {
        let builder = &self.ast_builder;
        let expr_id = expression.id;
        let rust_expr = expression.expr.clone();
        let span = rust_expr.span;
        let any_ty = self.ast_builder.ty(span, ast::TyKind::Infer);
        let return_ty = expected_ty.unwrap_or(any_ty);
        let mut lambda_fn = builder.lambda_fn_decl(
            span,
            builder.fn_decl(
                vec![],
                ast::FunctionRetTy::Ty(return_ty)
            ),
            builder.expr_block(builder.block(span, vec![builder.stmt_expr(rust_expr)])),
            span
        ).into_inner();
        lambda_fn.attrs = vec![
            self.ast_builder
                .attribute_name_value(span, "__PRUSTI_SPEC_EXPR_ID", &expr_id.to_string()),
            self.ast_builder.attribute_word(span, "pure"),
        ].into();
        builder.stmt_semi(ptr::P(lambda_fn))
    }

    fn build_assertion(&self, expression: &UntypedExpression) -> ast::Stmt {
        let bool_path = self.ast_builder.path_ident(
            expression.expr.span,
            self.ast_builder.ident_of("bool")
        );
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
            AssertionKind::And(ref assertions) => for assertion in assertions {
                self.populate_statements(assertion, statements);
            },
            AssertionKind::Implies(ref expression, ref assertion) => {
                let stmt = self.build_assertion(expression);
                statements.push(stmt);
                self.populate_statements(assertion, statements);
            }
            AssertionKind::ForAll(ref vars, ref trigger_set, ref body) => {
                let mut stmts = self.convert_trigger_set_to_statements(trigger_set);
                self.populate_statements(body, &mut stmts);
                let builder = &self.ast_builder;

                // TODO: use a proper span
                let span = DUMMY_SP;

                let mut lambda_fn = builder.lambda_fn_decl(
                    span,
                    builder.fn_decl(
                        vars.vars.clone(),
                        ast::FunctionRetTy::Default(span)
                    ),
                    builder.expr_block(builder.block(span, stmts)),
                    span
                ).into_inner();

                lambda_fn.attrs = vec![
                    builder.attribute_name_value(span, "__PRUSTI_SPEC_FORALL_VARS_ID", &vars.id.to_string()),
                    builder.attribute_word(span, "pure"),
                ].into();

                let statement = builder.stmt_semi(ptr::P(lambda_fn));
                statements.push(statement);
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
        builder.stmt_item(
            span,
            builder.item_use_glob(
                span,
                respan(span.shrink_to_lo(), ast::VisibilityKind::Inherited),
                vec![
                    builder.ident_of("prusti_contracts"),
                    builder.ident_of("internal"),
                ],
            ),
        )
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
        match item.node {
            ast::ItemKind::Fn(ref decl, ref _header, ref generics, ref _body) => {
                // Import contracts.
                let mut statements = vec![self.build_prusti_contract_import(item.span)];

                // Add preconditions.
                statements.extend(self.convert_to_statements(preconditions));

                // Add postconditions.
                statements.extend(self.convert_to_statements(postconditions));

                // Add result to arguments
                let unit_type = self.ast_builder.ty(
                    item.span,
                    ast::TyKind::Tup(Vec::new())
                );
                let return_type = match decl.output.clone() {
                    ast::FunctionRetTy::Ty(return_type) => return_type,
                    ast::FunctionRetTy::Default(_) => unit_type.clone()
                };
                let mut inputs_with_result: Vec<ast::Arg> = decl.inputs.clone();
                inputs_with_result.push(
                    self.ast_builder.arg(
                        item.span,
                        ast::Ident::from_str("result"),
                        return_type.clone()
                    )
                );

                // Glue everything.
                name.push_str("__spec");
                let mut spec_item = self.ast_builder.item_fn_poly(
                    item.span,
                    ast::Ident::from_str(&name),
                    inputs_with_result,
                    unit_type,
                    generics.clone(),
                    self.ast_builder.block(item.span, statements),
                )
                    .into_inner();
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
                        self.ast_builder.attribute_allow(item.span, "non_snake_case"),
                        self.ast_builder.attribute_allow(item.span, "unused_imports"),
                        self.ast_builder.attribute_allow(item.span, "unused_variables"),
                    ],
                );
                spec_item
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
                let mut statements = vec![self.build_prusti_contract_import(impl_item.span)];

                // Add preconditions.
                statements.extend(self.convert_to_statements(preconditions));

                // Add postconditions.
                statements.extend(self.convert_to_statements(postconditions));

                // Add result to arguments
                let unit_type = self.ast_builder.ty(
                    impl_item.span,
                    ast::TyKind::Tup(Vec::new())
                );
                let return_type = match sig.decl.output.clone() {
                    ast::FunctionRetTy::Ty(return_type) => return_type,
                    ast::FunctionRetTy::Default(_) => unit_type.clone()
                };
                let mut inputs_with_result: Vec<ast::Arg> = sig.decl.inputs.clone();
                inputs_with_result.push(
                    self.ast_builder.arg(
                        impl_item.span,
                        ast::Ident::from_str("result"),
                        return_type.clone()
                    )
                );

                let attrs = vec![
                    self.ast_builder.attribute_name_value(
                        impl_item.span,
                        "__PRUSTI_SPEC_ONLY",
                        &spec_id.to_string(),
                    ),
                    self.ast_builder.attribute_allow(impl_item.span, "unused_mut"),
                    self.ast_builder.attribute_allow(impl_item.span, "dead_code"),
                    self.ast_builder.attribute_allow(impl_item.span, "non_snake_case"),
                    self.ast_builder.attribute_allow(impl_item.span, "unused_imports"),
                    self.ast_builder.attribute_allow(impl_item.span, "unused_variables"),
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
                let mut statements = vec![self.build_prusti_contract_import(trait_item.span)];

                // Add preconditions.
                statements.extend(self.convert_to_statements(preconditions));

                // Add postconditions.
                statements.extend(self.convert_to_statements(postconditions));

                // Add result to arguments
                let unit_type = self.ast_builder.ty(
                    trait_item.span,
                    ast::TyKind::Tup(Vec::new())
                );
                let return_type = match sig.decl.output.clone() {
                    ast::FunctionRetTy::Ty(return_type) => return_type,
                    ast::FunctionRetTy::Default(_) => unit_type.clone()
                };
                let mut inputs_with_result: Vec<ast::Arg> = sig.decl.inputs.clone();
                inputs_with_result.push(
                    self.ast_builder.arg(
                        trait_item.span,
                        ast::Ident::from_str("result"),
                        return_type.clone()
                    )
                );

                let attrs = vec![
                    self.ast_builder.attribute_name_value(
                        trait_item.span,
                        "__PRUSTI_SPEC_ONLY",
                        &spec_id.to_string(),
                    ),
                    self.ast_builder.attribute_allow(trait_item.span, "unused_mut"),
                    self.ast_builder.attribute_allow(trait_item.span, "dead_code"),
                    self.ast_builder.attribute_allow(trait_item.span, "non_snake_case"),
                    self.ast_builder.attribute_allow(trait_item.span, "unused_imports"),
                    self.ast_builder.attribute_allow(trait_item.span, "unused_variables"),
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
        let mut block = block.into_inner();
        if invariants.is_empty() {
            return ptr::P(block);
        }
        let span = block.span;
        let mut statements = self.convert_to_statements(invariants);
        statements.insert(0, self.build_prusti_contract_import(span));
        let builder = &self.ast_builder;
        let expr = builder.expr_if(
            span,
            builder.expr_bool(span, false),
            builder.expr_block(builder.block(span, statements)),
            None,
        );
        let mut expr = expr.into_inner();
        expr.attrs = vec![
            self.ast_builder
                .attribute_name_value(span, "__PRUSTI_SPEC_ONLY", &spec_id.to_string()),
        ].into();
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
        expr.attrs = vec![
            self.ast_builder
                .attribute_name_value(expr.span, PRUSTI_SPEC_ATTR, &id.to_string()),
        ].into();

        trace!("[rewrite_loop] exit");
        ptr::P(expr)
    }

    fn rewrite_fn_item(&mut self, item: ptr::P<ast::Item>) -> SmallVector<ptr::P<ast::Item>> {
        trace!("[rewrite_fn_item] enter");
        let mut item = item.into_inner();
        let attrs = item.attrs;
        item.attrs = vec![];
        let is_pure_function = attr::contains_name(&attrs, "pure");
        let is_trusted = attr::contains_name(&attrs, "trusted");
        let specs = self.parse_specs(attrs);
        if specs.iter().any(|spec| spec.typ == SpecType::Invariant) {
            self.report_error(item.span, "invariant not allowed for procedure");
            return SmallVector::new();
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
        let id = self.register_specification(spec_set);
        let spec_item = self.generate_spec_item(&item, id, &preconditions, &postconditions);
        let node = item.node;
        item.node = self.fold_item_kind(node);
        item.attrs = vec![
            self.ast_builder
                .attribute_name_value(item.span, PRUSTI_SPEC_ATTR, &id.to_string()),
        ];
        if is_pure_function {
            item.attrs.push(
                self.ast_builder.attribute_word(item.span, "pure")
            );
        }
        if is_trusted {
            item.attrs.push(
                self.ast_builder.attribute_word(item.span, "trusted")
            );
        }

        let new_item_str = syntax::print::pprust::item_to_string(&item);
        let spec_item_str = syntax::print::pprust::item_to_string(&spec_item);
        debug!("new_item:\n{}", new_item_str);
        self.log_modified_program(new_item_str);
        debug!("spec_item:\n{}", spec_item_str);
        self.log_modified_program(spec_item_str);

        trace!("[rewrite_fn_item] exit");
        let mut result = SmallVector::new();
        result.push(ptr::P(item));
        result.push(ptr::P(spec_item));
        result
    }

    fn rewrite_impl_item_method(&mut self, mut impl_item: ast::ImplItem) -> SmallVector<ast::ImplItem> {
        trace!("[rewrite_impl_item_method] enter");
        let attrs = impl_item.attrs;
        impl_item.attrs = vec![];
        let is_pure_function = attr::contains_name(&attrs, "pure");
        let is_trusted = attr::contains_name(&attrs, "trusted");
        let specs = self.parse_specs(attrs);
        if specs.iter().any(|spec| spec.typ == SpecType::Invariant) {
            self.report_error(impl_item.span, "invariant not allowed for procedure");
            return SmallVector::new();
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
        let id = self.register_specification(spec_set);
        let spec_item = self.generate_spec_impl_item(&impl_item, id, &preconditions, &postconditions);
        impl_item.attrs = vec![
            self.ast_builder
                .attribute_name_value(impl_item.span, PRUSTI_SPEC_ATTR, &id.to_string()),
        ];
        if is_pure_function {
            impl_item.attrs.push(
                self.ast_builder.attribute_word(impl_item.span, "pure")
            );
        }
        if is_trusted {
            impl_item.attrs.push(
                self.ast_builder.attribute_word(impl_item.span, "trusted")
            );
        }

        let new_item_str = syntax::print::pprust::impl_item_to_string(&impl_item);
        let spec_item_str = syntax::print::pprust::impl_item_to_string(&spec_item);
        debug!("new_item:\n{}", new_item_str);
        self.log_modified_program(new_item_str);
        debug!("spec_item:\n{}", spec_item_str);
        self.log_modified_program(spec_item_str);

        trace!("[rewrite_impl_item_method] exit");
        let mut result = SmallVector::new();
        result.push(impl_item);
        result.push(spec_item);
        result
    }

    fn rewrite_trait_item_method(&mut self, mut trait_item: ast::TraitItem) -> SmallVector<ast::TraitItem> {
        trace!("[rewrite_trait_item_method] enter");
        let attrs = trait_item.attrs;
        trait_item.attrs = vec![];
        let is_pure_function = attr::contains_name(&attrs, "pure");
        let is_trusted = attr::contains_name(&attrs, "trusted");
        let specs = self.parse_specs(attrs);
        if specs.iter().any(|spec| spec.typ == SpecType::Invariant) {
            self.report_error(trait_item.span, "invariant not allowed for procedure");
            return SmallVector::new();
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
        let id = self.register_specification(spec_set);
        let spec_item = self.generate_spec_trait_item(&trait_item, id, &preconditions, &postconditions);
        trait_item.attrs = vec![];

        // Skip body-less trait methods
        match trait_item.node {
            ast::TraitItemKind::Method(_, Some(_)) => {
                trait_item.attrs.push(
                    self.ast_builder
                        .attribute_name_value(trait_item.span, PRUSTI_SPEC_ATTR, &id.to_string()),
                );
            }

            ast::TraitItemKind::Method(_, None) => {} // OK

            _ => unreachable!(),
        }

        if is_pure_function {
            trait_item.attrs.push(
                self.ast_builder.attribute_word(trait_item.span, "pure")
            );
        }
        if is_trusted {
            trait_item.attrs.push(
                self.ast_builder.attribute_word(trait_item.span, "trusted")
            );
        }

        let new_item_str = syntax::print::pprust::trait_item_to_string(&trait_item);
        let spec_item_str = syntax::print::pprust::trait_item_to_string(&spec_item);
        debug!("new_item:\n{}", new_item_str);
        self.log_modified_program(new_item_str);
        debug!("spec_item:\n{}", spec_item_str);
        self.log_modified_program(spec_item_str);

        trace!("[rewrite_trait_item_method] exit");
        let mut result = SmallVector::new();
        result.push(trait_item);
        result.push(spec_item);
        result
    }

    /// Extracts specification string from the attribute with the
    /// correct base span.
    fn extract_spec_string(&self, attribute: &ast::Attribute) -> Option<(String, Span)> {
        use syntax::tokenstream::TokenTree;
        use syntax::parse::token;

        let trees: Vec<TokenTree> = attribute.tokens.trees().collect();
        if trees.len() != 2 {
            self.report_error(
                attribute.span,
                "malformed specification (incorrect number of token trees)",
            );
            return None;
        }
        match trees[0] {
            TokenTree::Token(_, ref token) => {
                if *token != token::Token::Eq {
                    self.report_error(
                        attribute.span,
                        "malformed specification (expected equality)",
                    );
                    return None;
                }
            }
            _ => {
                self.report_error(attribute.span, "malformed specification (expected token)");
                return None;
            }
        };
        let spec_string_with_span = match trees[1] {
            TokenTree::Token(span, ref token) => match *token {
                token::Token::Literal(ref lit, None) => match *lit {
                    token::Lit::Str_(ref name) => {
                        let name: &str = &name.as_str();
                        let spec = String::from(name);
                        Some((spec, span))
                    }
                    token::Lit::StrRaw(ref name, delimiter_size) => {
                        let name: &str = &name.as_str();
                        let spec = String::from(name);
                        Some((spec, shift_span(span, (delimiter_size + 1) as u32)))
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

    fn parse_assertion_wrap(&mut self, span: Span, spec_string: &str) -> Option<UntypedAssertion> {
        match self.parse_assertion(span, spec_string) {
            Ok(assertion) => Some(assertion),
            Err(AssertionParsingError::NotMatchingParenthesis) => {
                self.report_error(span, "not matching parenthesis");
                None
            }
            Err(AssertionParsingError::ParsingRustExpressionFailed)
            | Err(AssertionParsingError::FailedForallMatch) => None,
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
                    if let Some((spec_string, span)) = self.extract_spec_string(&attribute) {
                        debug!("spec={:?} spec_type={:?}", spec_string, spec_type);
                        if let Some(assertion) = self.parse_assertion_wrap(span, &spec_string) {
                            debug!("assertion={:?}", assertion);
                            Some(UntypedSpecification {
                                typ: spec_type,
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
        ).parse_expr();
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
        let re = Regex::new(r"^\s*([a-z][a-z0-9]*)\s*:\s*([a-z][a-z0-9]*)\s*$").unwrap();
        let builder = &self.ast_builder;
        for var_string in vars_string.split(',') {
            if let Some(caps) = re.captures(var_string) {
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

    fn parse_forall(
        &mut self,
        span: Span,
        spec_string: &str,
    ) -> Result<UntypedAssertion, AssertionParsingError> {
        let re = Regex::new(
            r"(?x)
            ^\s*forall\s*
            (?P<vars>.*)\s*::\s*(\{(?P<triggers>.*)\})?\s*
            (?P<filter>.*)\s*==>\s*(?P<body>.*)\s*$
        ",
        ).unwrap();
        if let Some(caps) = re.captures(spec_string) {
            let vars = self.parse_vars(span, caps.name("vars").unwrap())?;
            let triggers = match caps.name("triggers") {
                Some(triggers) => self.parse_triggers(span, triggers)?,
                None => TriggerSet::new(vec![])
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
                            Expression {
                                id: self.get_new_expression_id(),
                                expr: filter,
                            },
                            UntypedAssertion {
                                kind: box AssertionKind::Expr(
                                    Expression {
                                        id: self.get_new_expression_id(),
                                        expr: body,
                                    },
                                )
                            }
                        )
                    }
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
            let re = Regex::new(r"^(\s*\()(.*)\)\s*$").unwrap();
            if let Some(caps) = re.captures(&spec_string) {
                let new_span = shift_span(span, caps[1].len() as u32);
                return self.parse_assertion_simple(new_span, String::from(&caps[2]));
            }
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
                            kind: box AssertionKind::Implies(precondition, assertion),
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
    fn fold_item(&mut self, item: ptr::P<ast::Item>) -> SmallVector<ptr::P<ast::Item>> {
        trace!("[fold_item] enter");
        let result = match item.node {
            ast::ItemKind::Fn(..) => self.rewrite_fn_item(item),
            _ => fold::noop_fold_item(item, self),
        };
        trace!("[fold_item] exit");
        result
    }

    fn fold_impl_item(&mut self, impl_item: ast::ImplItem) -> SmallVector<ast::ImplItem> {
        trace!("[fold_impl_item] enter");
        let result = match impl_item.node {
            ast::ImplItemKind::Method(..) => self.rewrite_impl_item_method(impl_item),
            _ => fold::noop_fold_impl_item(impl_item, self),
        };
        trace!("[fold_item] exit");
        result
    }

    fn fold_trait_item(&mut self, trait_item: ast::TraitItem) -> SmallVector<ast::TraitItem> {
        trace!("[fold_trait_item] enter");
        let result = match trait_item.node {
            ast::TraitItemKind::Method(..) => self.rewrite_trait_item_method(trait_item),
            _ => fold::noop_fold_trait_item(trait_item, self),
        };
        trace!("[fold_trait_item] exit");
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
}

fn substring(string: &str, start: usize, end: usize) -> String {
    string
        .chars()
        .skip(start)
        .take(end - start)
        .collect::<String>()
}

struct SpanRewriter {
    old_base_pos: syntax::codemap::BytePos,
    new_base_pos: syntax::codemap::BytePos,
}

impl SpanRewriter {
    pub fn new(whitespace_count: u32, old_base_span: Span, new_base_span: Span) -> SpanRewriter {
        SpanRewriter {
            old_base_pos: old_base_span.lo(),
            new_base_pos: new_base_span.lo() + syntax::codemap::BytePos(whitespace_count),
        }
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
