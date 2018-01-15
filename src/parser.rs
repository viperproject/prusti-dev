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
    UntypedSpecification, UntypedSpecificationSet, UntypedAssertion};
use std::collections::HashMap;
use std::convert::TryFrom;



/// Rewrite specifications in the expanded AST to get them type-checked
/// by rustc. For more information see the module documentation.
pub fn rewrite_crate(state: &mut driver::CompileState) {
    trace!("[rewrite_crate] enter");
    let krate = state.krate.take().unwrap();
    let mut parser = SpecParser::new(state.session);
    state.krate = Some(parser.fold_crate(krate));
    trace!("[rewrite_crate] exit");
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
    untyped_specifications: HashMap<SpecID, UntypedSpecificationSet>,
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

    fn rewrite_fn_item(&mut self,
                        item: ptr::P<ast::Item>) -> SmallVector<ptr::P<ast::Item>> {
        trace!("[rewrite_function] enter");
        let mut item = item.into_inner();
        let attrs = item.attrs;
        let specs = self.parse_specs(attrs);
        if specs.iter().any(|spec| spec.typ == SpecType::Invariant) {
            self.report_error(item.span, "invariant not allowed for procedure");
            return SmallVector::new();
        }
        let id = self.register_specification(specs);
        let node = item.node;
        item.node = self.fold_item_kind(node);
        let builder = &self.ast_builder;
        item.attrs = vec![
            builder.attribute(
                item.span,
                builder.meta_name_value(
                    item.span,
                    builder.name_of("__PRUSTI_SPEC"),
                    ast::LitKind::Str(
                        builder.name_of(&id.to_string()),
                        ast::StrStyle::Cooked),
                )
            )
        ];
        debug!("new_item:\n{}", syntax::print::pprust::item_to_string(&item));
        trace!("[rewrite_function] exit");
        SmallVector::one(ptr::P(item))
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
