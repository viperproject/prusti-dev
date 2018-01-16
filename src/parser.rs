//! Code for extracting specifications.
//!
//! TODO: Copy documentation from my status report.


use ast_builder::MinimalAstBuilder;
use regex::Regex;
use rustc::session::Session;
use rustc_driver::driver;
use syntax::{self, ast, ptr, parse};
use syntax::codemap::Span;
use syntax::ext::build::AstBuilder;
use syntax::fold::Folder;
use syntax::util::small_vector::SmallVector;
use syntax_pos::FileName;
use specifications::{
    AssertionKind, Assertion, SpecID, SpecType, Expression, ExpressionId,
    SpecificationSet, UntypedSpecification, UntypedSpecificationSet,
    UntypedAssertion, UntypedSpecificationMap};
use std::collections::HashMap;
use std::convert::TryFrom;
use std::mem;



/// Rewrite specifications in the expanded AST to get them type-checked
/// by rustc. For more information see the module documentation.
pub fn rewrite_crate(state: &mut driver::CompileState
                     ) -> UntypedSpecificationMap {
    trace!("[rewrite_crate] enter");
    let krate = state.krate.take().unwrap();
    let mut parser = SpecParser::new(state.session);
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
}

impl<'tcx> SpecParser<'tcx> {

    /// Create new spec parser.
    pub fn new(session: &'tcx Session) -> SpecParser<'tcx> {
        SpecParser {
            session: session,
            ast_builder: MinimalAstBuilder::new(&session.parse_sess),
            last_specification_id: SpecID::new(),
            last_expression_id: ExpressionId::new(),
            untyped_specifications: HashMap::new(),
        }
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

    fn populate_statements(&self, assertion: &UntypedAssertion,
                           statements: &mut Vec<ast::Stmt>) {
        trace!("[populate_statements] enter");
        let builder = &self.ast_builder;
        match *assertion.kind {
            AssertionKind::Expr(ref expression) => {
                let id = expression.id;
                let rust_expr = expression.expr.clone();
                let span = rust_expr.span;
                let stmt = builder.stmt_expr(
                    builder.expr_call(
                        span,
                        builder.expr_ident(
                            span,
                            builder.ident_of("__assertion"),
                        ),
                        vec![
                            builder.expr_usize(span, id.into()),
                            rust_expr,
                        ],
                    )
                );
                statements.push(stmt);
            },
            AssertionKind::And(ref assertions) => {
                for assertion in assertions {
                    self.populate_statements(assertion, statements);
                }
            },
            _ => {
                unimplemented!();
            }
        };
        trace!("[populate_statements] exit");
    }

    /// Convert untyped specifications into a sequence of statements for
    /// type-checking.
    fn convert_to_statements(&self, specifications: &Vec<UntypedSpecification>
                             ) -> Vec<ast::Stmt> {
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
                ast::Visibility::Inherited,
                vec![
                    builder.ident_of("prusti_contracts"),
                    builder.ident_of("internal"),
                ]
            )
        )
    }

    /// Generate a function that contains only the precondition and postcondition
    /// for type-checking.
    fn generate_spec_item(&mut self, item: &ast::Item,
                          spec_id: SpecID,
                          preconditions: &Vec<UntypedSpecification>,
                          postconditions: &Vec<UntypedSpecification>) -> ast::Item {
        let mut name = item.ident.to_string();
        let builder = &self.ast_builder;
        let span = item.span;
        match &item.node {
            &ast::ItemKind::Fn(ref decl, _unsafety, _constness, _abi,
                               ref _generics, ref _body) => {

                // Import contracts.
                let mut statements = vec![
                    self.build_prusti_contract_import(span),
                ];

                // Add preconditions.
                statements.extend(self.convert_to_statements(preconditions));

                // Add result.
                let args: Vec<_> = decl.inputs.clone().into_iter().map(|arg| {
                    if let ast::PatKind::Ident(_, ident, _) = arg.pat.node {
                        builder.expr_ident(ident.span, ident.node)
                    }
                    else {
                        unreachable!();
                    }
                }).collect();
                statements.push(
                    builder.stmt_let(
                        item.span,
                        false,
                        ast::Ident::from_str("result"),
                        builder.expr_call_ident(item.span, item.ident, args),
                    )
                );

                // Add postconditions.
                statements.extend(self.convert_to_statements(postconditions));

                // Return result.
                statements.push(
                    builder.stmt_expr(
                        builder.expr_ident(
                            item.span,
                            builder.ident_of("result")
                        )
                    )
                );

                // Glue everything.
                let return_type = match decl.output.clone() {
                    ast::FunctionRetTy::Ty(return_type) => {Some(return_type)},
                    ast::FunctionRetTy::Default(_) => {None},
                };
                name.push_str("__spec");
                let mut spec_item = builder.item_fn_optional_result(
                    item.span,
                    ast::Ident::from_str(&name),
                    decl.inputs.clone(),
                    return_type,
                    builder.block(
                        item.span,
                        statements,
                        ),
                    ).into_inner();
                mem::replace(&mut spec_item.attrs, vec![
                    builder.attribute_name_value(
                        item.span, "__PRUSTI_SPEC_ONLY", &spec_id.to_string()),
                    builder.attribute_allow(item.span, "unused_mut"),
                    builder.attribute_allow(item.span, "dead_code"),
                    builder.attribute_allow(item.span, "non_snake_case"),
                    builder.attribute_allow(item.span, "unused_imports"),
                ]);
                spec_item
            },
            _ => {
                unreachable!();
            }
        }
    }

    fn rewrite_loop_block(&mut self, block: ptr::P<ast::Block>,
                          spec_id: SpecID,
                          invariants: &Vec<UntypedSpecification>
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
            builder.expr_block(
                builder.block(
                    span,
                    statements
                )
            ),
            None,
        );
        let mut expr = expr.into_inner();
        expr.attrs = vec![
            self.ast_builder.attribute_name_value(
                span, "__PRUSTI_SPEC_ONLY", &spec_id.to_string()),
        ].into();
        block.stmts.insert(0, builder.stmt_expr(ptr::P(expr)));
        trace!("[rewrite_loop_block] exit");
        ptr::P(block)
    }

    fn rewrite_loop(&mut self, expr: ptr::P<ast::Expr>) -> ptr::P<ast::Expr> {
        // TODO: Recursively rewrite nested loops.
        trace!("[rewrite_loop] enter");
        let mut expr = expr.into_inner();
        let attrs = expr.attrs.to_vec();
        expr.attrs = vec![].into();
        let invariants = self.parse_specs(attrs);
        if !invariants.iter().all(|spec| spec.typ == SpecType::Invariant) {
            self.report_error(expr.span, "loops can have only invariants");
            return ptr::P(expr);
        }
        let spec_set = SpecificationSet::Loop(invariants.clone());
        let id = self.register_specification(spec_set);
        expr.node = match expr.node {
            ast::ExprKind::While(condition, block, ident) => {
                let block = self.rewrite_loop_block(block, id, &invariants);
                ast::ExprKind::While(condition, block, ident)
            },
            ast::ExprKind::WhileLet(pattern, expr, block, label) => {
                let block = self.rewrite_loop_block(block, id, &invariants);
                ast::ExprKind::WhileLet(pattern, expr, block, label)
            },
            ast::ExprKind::ForLoop(pattern, expr, block, label) => {
                let block = self.rewrite_loop_block(block, id, &invariants);
                ast::ExprKind::ForLoop(pattern, expr, block, label)
            },
            ast::ExprKind::Loop(block, label) => {
                let block = self.rewrite_loop_block(block, id, &invariants);
                ast::ExprKind::Loop(block, label)
            },
            _ => {unreachable!()},
        };
        expr.attrs = vec![
            self.ast_builder.attribute_name_value(
                expr.span, "__PRUSTI_SPEC", &id.to_string()),
        ].into();
        trace!("[rewrite_loop] exit");
        ptr::P(expr)
    }

    fn rewrite_fn_item(&mut self,
                        item: ptr::P<ast::Item>) -> SmallVector<ptr::P<ast::Item>> {
        trace!("[rewrite_function] enter");
        let mut item = item.into_inner();
        let attrs = item.attrs;
        item.attrs = vec![];
        let specs = self.parse_specs(attrs);
        if specs.iter().any(|spec| spec.typ == SpecType::Invariant) {
            self.report_error(item.span, "invariant not allowed for procedure");
            return SmallVector::new();
        }
        let preconditions: Vec<_> = specs
            .clone().into_iter()
            .filter(|spec| spec.typ == SpecType::Precondition).collect();
        let postconditions: Vec<_> = specs
            .into_iter()
            .filter(|spec| spec.typ == SpecType::Postcondition).collect();
        let spec_set = SpecificationSet::Procedure(
            preconditions.clone(), postconditions.clone());
        let id = self.register_specification(spec_set);
        let spec_item = self.generate_spec_item(&item, id, &preconditions, &postconditions);
        let node = item.node;
        item.node = self.fold_item_kind(node);
        item.attrs = vec![
            self.ast_builder.attribute_name_value(
                item.span, "__PRUSTI_SPEC", &id.to_string()),
        ];
        debug!("new_item:\n{}", syntax::print::pprust::item_to_string(&item));
        debug!("spec_item:\n{}", syntax::print::pprust::item_to_string(&spec_item));
        trace!("[rewrite_function] exit");
        let mut result = SmallVector::new();
        result.push(ptr::P(item));
        result.push(ptr::P(spec_item));
        result
    }

    fn extract_spec_string(&self, attribute: &ast::Attribute) -> Option<String> {
        use syntax::tokenstream::TokenTree;
        use syntax::parse::token;

        let trees: Vec<TokenTree> = attribute.tokens.trees().collect();
        if trees.len() != 2 {
            self.report_error(attribute.span, "malformed specification");
            return None;
        }
        match &trees[0] {
            &TokenTree::Token(_, ref token) => {
                if *token != token::Token::Eq {
                    self.report_error(attribute.span, "malformed specification");
                    return None;
                }
            },
            _ => {
                self.report_error(attribute.span, "malformed specification");
                return None;
            },
        };
        let spec_string = match &trees[1] {
            &TokenTree::Token(_, ref token) => {
                match token {
                    &token::Token::Literal(ref lit, None) => {
                        match lit {
                            &token::Lit::Str_(ref name) => {
                                let name: &str = &name.as_str();
                                let spec = String::from(name);
                                Some(spec)
                            },
                            _ => {
                                None
                            },
                        }
                    },
                    _ => {
                        None
                    },
                }
            },
            _ => {
                None
            },
        };
        if spec_string.is_none() {
            self.report_error(attribute.span, "malformed specification");
        }
        spec_string
    }

    fn parse_assertion_wrap(&mut self, span: Span,
                            spec_string: String) -> Option<UntypedAssertion> {
        match self.parse_assertion(span, spec_string) {
            Ok(assertion) => {
                Some(assertion)
            },
            Err(AssertionParsingError::NotMatchingParenthesis) => {
                self.report_error(span, "not matching parenthesis");
                None
            },
            Err(AssertionParsingError::ParsingRustExpressionFailed) => {
                None
            },
        }
    }

    /// Parses attribute into specification.
    /// TODO: Rewrite to use the [syn](https://crates.io/crates/syn) crate.
    fn parse_specs(&mut self,
                   attributes: Vec<ast::Attribute>) -> Vec<UntypedSpecification> {
        trace!("[parse_specs] enter attributes.len={}", attributes.len());

        let specifications: Vec<_> = attributes.into_iter().map(|attribute| {
            if let Ok(spec_type) = SpecType::try_from(
                &attribute.path.to_string() as &str) {
                if let Some(spec_string) = self.extract_spec_string(&attribute) {
                    debug!("spec={:?} spec_type={:?}", spec_string, spec_type);
                    if let Some(assertion) = self.parse_assertion_wrap(
                        attribute.span, spec_string) {
                        debug!("assertion={:?}", assertion);
                        Some(UntypedSpecification {
                            typ: spec_type,
                            assertion: assertion,
                        })
                    }
                    else {
                        None
                    }
                }
                else {
                    None
                }
            } else {
                self.report_error(attribute.span, "unsupported attribute");
                None
            }
        }).filter(|spec| spec.is_some()).map(|spec| spec.unwrap()).collect();

        trace!("[parse_specs] exit");
        specifications
    }

    /// Parse Rust expression.
    fn parse_expression(&mut self, _span: Span, spec_string: String)
            -> Result<ptr::P<ast::Expr>, AssertionParsingError> {
        trace!("[parse_expression] enter spec_string={:?}", spec_string);
        let expr = parse::parse_expr_from_source_str(
            FileName::QuoteExpansion, spec_string, &self.session.parse_sess);
        let result = match expr {
            Ok(expr) => Ok(expr),
            Err(mut err) => {
                err.emit();
                Err(AssertionParsingError::ParsingRustExpressionFailed)
            },
        };
        trace!("[parse_expression] exit");
        result
    }

    /// Parse an assertion string into an assertion object.
    /// The assertion string can only contain an implication, forall, or a
    /// Rust expression.
    fn parse_assertion_simple(&mut self, span: Span, spec_string: String)
            -> Result<UntypedAssertion, AssertionParsingError> {
        trace!("[parse_assertion_simple] enter spec_string={:?}", spec_string);

        // Drop surrounding parenthesis.
        {
            let re = Regex::new(r"^\s*\((.*)\)\s*$").unwrap();
            if let Some(caps) = re.captures(&spec_string) {
                return self.parse_assertion_simple(span, String::from(&caps[1]));
            }
        }

        // Parse forall.
        {
            let re = Regex::new(r"(?x)
                ^\s*
                forall
                \s*
                (?P<vars>[a-z][a-z0-9]*(,\s*[a-z][a-z0-9]*))
                \s*
                ::
                \s*
                \{(?P<triggers>.*)\}
                \s*
                (?P<filter>.*)
                \s*
                ==>
                \s*
                (?P<body>.*)
                \s*
            ").unwrap();
            if let Some(_caps) = re.captures(&spec_string) {
                unimplemented!();
            }
        }

        // Parse the implication.
        {
            let mut parenthesis_depth = 0;
            let mut iter = spec_string.char_indices().peekable();
            let mut last2 = None;
            let mut last1 = None;
            while let Some((position, char)) = iter.next() {
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
                if parenthesis_depth == 0 {
                    if last2 == Some('=') && last1 == Some('=') && char == '>' {
                        let expr = substring(&spec_string, 0, position - 2);
                        let expr = self.parse_expression(span, expr)?;
                        let assertion = substring(&spec_string, position+1,
                                                  spec_string.len());
                        let assertion = self.parse_assertion(span, assertion)?;
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
                }
                last1 = Some(char);
                last2 = last1;
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
    /// TODO: Write a unit test for this.
    fn parse_assertion(&mut self, span: Span, spec_string: String)
            -> Result<UntypedAssertion, AssertionParsingError> {
        trace!("[parse_assertion] enter spec_string={:?}", spec_string);
        // Get pairs of matching braces.
        let mut start_positions: Vec<usize> = Vec::new();
        // Map from position of an open parenthesis to the position
        // of the matching close parenthesis.
        let mut end_positions: HashMap<usize, usize> = HashMap::new();
        for (position, char) in spec_string.chars().enumerate() {
            if char == '(' {
                start_positions.push(position);
            }
            else if char == ')' {
                if let Some(start_position) = start_positions.pop() {
                    end_positions.insert(start_position, position);
                } else {
                    return Err(AssertionParsingError::NotMatchingParenthesis);
                }
            }
        }
        if !start_positions.is_empty() {
            return Err(AssertionParsingError::NotMatchingParenthesis);
        }
        // Split assertion and process it recursively.
        let mut iter = spec_string.char_indices().peekable();
        let mut block_start = 0;
        let mut assertions: Vec<UntypedAssertion> = Vec::new();
        while let Some((position, char)) = iter.next() {
            if char == '(' {
                match iter.nth(end_positions[&position] - position) {
                    Some((_, ')')) => {},
                    _ => {bug!()},
                }
            }
            if char == '&' {
                if let Some(&(_, '&')) = iter.peek() {
                    iter.next();
                    let block = substring(&spec_string, block_start, position);
                    let assertion = self.parse_assertion(span, block)?;
                    assertions.push(assertion);
                    block_start = position + 2;
                }
            }
        }
        let block = substring(&spec_string, block_start, spec_string.len());
        let last_assertion = self.parse_assertion_simple(span, block)?;
        let assertion = if assertions.is_empty() {
            last_assertion
        }
        else {
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
            ast::ItemKind::Fn(_, _, _, _, _, _) => {
                self.rewrite_fn_item(item)
            },
            _ => {
                SmallVector::one(item.map(|item| self.fold_item_simple(item)))
            },
        };
        trace!("[fold_item] exit");
        result
    }

    fn fold_expr(&mut self, expr: ptr::P<ast::Expr>) -> ptr::P<ast::Expr> {
        let result = match expr.node {
            ast::ExprKind::While(_, _, _) |
            ast::ExprKind::WhileLet(_, _, _, _) |
            ast::ExprKind::ForLoop(_, _, _, _) |
            ast::ExprKind::Loop(_, _) => {
                self.rewrite_loop(expr)
            },
            _ => {
                expr.map(|e| syntax::fold::noop_fold_expr(e, self))
            },
        };
        result
    }

}


#[derive(Debug)]
/// An error reported when parsing of assertion fails.
pub enum AssertionParsingError {
    /// Reported when parenthesis do not match.
    NotMatchingParenthesis,
    /// Reported when Rust assertion parsing fails.
    ParsingRustExpressionFailed,
}

fn substring(string: &str, start: usize, end: usize) -> String {
    string
        .chars()
        .skip(start)
        .take(end-start)
        .collect::<String>()
}
