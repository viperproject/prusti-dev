//! Code for extracting specifications.


use std::mem;
use std::convert::TryFrom;
use std::collections::HashMap;

use syntax::{self, ast, ptr, fold};
use syntax::codemap::Span;
use syntax::fold::Folder;
use syntax::ext::base::{ExtCtxt, Annotatable};
use syntax::ext::build::AstBuilder;
use syntax::ext::quote::rt::ExtParseUtils;

use specifications::{SpecType, SpecID, RawSpec};


pub struct SpecParser {
    last_id: SpecID,
    raw_specs: HashMap<SpecID, RawSpec>,
}

impl RawSpec {

    fn from_meta_item(cx: &mut ExtCtxt, attr: &ast::MetaItem) -> Self {
        let spec_type = SpecType::try_from(attr.name.as_str().as_ref()).unwrap();
        let spec_expr = match &attr.node {
            &ast::MetaItemKind::NameValue(ref lit) => {
                match lit.node {
                    ast::LitKind::Str(ref lit, _) => {
                        cx.parse_expr(lit.to_string().clone())
                    },
                    _ => {panic!("Unrecognized attribute literal: {:?}", lit.node)},
                }
            },
            _ => {panic!("Unrecognized attribute: {:?}", attr.node)},
        };
        RawSpec {
            spec_type: spec_type,
            expr: spec_expr,
            span: attr.span,
        }
    }

    fn from_attribute(cx: &mut ExtCtxt, attr: &ast::Attribute) -> Self {
        use syntax::tokenstream::TokenTree;
        use syntax::parse::token;

        let spec_type = SpecType::try_from(&attr.path.to_string() as &str).unwrap();

        let trees: Vec<TokenTree> = attr.tokens.trees().collect();
        assert!(trees.len() == 2);
        match &trees[0] {
            &TokenTree::Token(_, ref token) => {
                assert!(*token == token::Token::Eq);
            },
            _ => {
                unreachable!();
            },
        };
        let spec_expr = match &trees[1] {
            &TokenTree::Token(_, ref token) => {
                match token {
                    &token::Token::Literal(ref lit, None) => {
                        match lit {
                            &token::Lit::Str_(ref name) => {
                                let name: &str = &name.as_str();
                                let spec = String::from(name);
                                cx.parse_expr(spec.clone())
                            },
                            _ => {
                                unreachable!();
                            },
                        }
                    },
                    _ => {
                        unreachable!();
                    },
                }
            },
            _ => {
                unreachable!();
            },
        };
        RawSpec {
            spec_type: spec_type,
            expr: spec_expr,
            span: attr.span,
        }
    }
}

impl SpecParser {

    pub fn new() -> SpecParser {
        SpecParser {
            last_id: SpecID::new(),
            raw_specs: HashMap::new(),
        }
    }

    pub fn get_new_id(&mut self) -> SpecID {
        self.last_id.inc()
    }

    pub fn register_spec(&mut self, spec: RawSpec) -> SpecID {
        let new_id = self.get_new_id();
        self.raw_specs.insert(new_id, spec);
        new_id
    }

    /// Generate a function that contains only the precondition and postcondition
    /// for type-checking.
    fn generate_spec_item(&mut self, cx: &mut ExtCtxt,
                          item: &ast::Item, proc_specs: &[RawSpec]) -> ast::Item {
        let mut name = item.ident.to_string();
        match &item.node {
            &ast::ItemKind::Fn(ref decl, _unsafety, _constness, _abi, ref _generics, ref _body) => {
                let return_type = match decl.output.clone() {
                    ast::FunctionRetTy::Ty(return_type) => {return_type},
                    _ => {unreachable!()},
                };
                name.push_str("__spec");
                let mut statements = vec![
                    quote_stmt!(cx, use prusti_contracts::internal::*;).unwrap()
                ];
                let assertions: Vec<_> = proc_specs.into_iter().map(|spec| {
                    let assertion_id = self.register_spec(spec.clone());
                    let assertion_id_number = assertion_id.to_number();
                    let spec_expr = &spec.expr;
                    let stmt = quote_stmt!(cx, __assertion($assertion_id_number, $spec_expr)).unwrap();
                    (spec.spec_type, stmt)
                }).collect();
                // Add preconditions.
                let preconditions = assertions
                    .iter()
                    .filter(|&&(ref spec_type, _)| *spec_type == SpecType::Precondition)
                    .map(|&(_, ref stmt)| stmt.clone());
                statements.extend(preconditions);
                // Add result.
                let args: Vec<_> = decl.inputs.clone().into_iter().map(|arg| {
                    if let ast::PatKind::Ident(_, ident, _) = arg.pat.node {
                        cx.expr_ident(ident.span, ident.node)
                    }
                    else {
                        unreachable!();
                    }
                }).collect();
                statements.push(
                    cx.stmt_let(
                        item.span,
                        false,
                        ast::Ident::from_str("result"),
                        cx.expr_call_ident(item.span, item.ident, args),
                    )
                );
                // Add postconditions.
                let postconditions = assertions
                    .iter()
                    .filter(|&&(ref spec_type, _)| *spec_type == SpecType::Postcondition)
                    .map(|&(_, ref stmt)| stmt.clone());
                statements.extend(postconditions);
                // Return result.
                statements.push(quote_stmt!(cx, result).unwrap());
                // Glue everything.
                let mut spec_item = cx.item_fn(
                    item.span,
                    ast::Ident::from_str(&name),
                    decl.inputs.clone(),
                    return_type,
                    cx.block(
                        item.span,
                        statements,
                        ),
                    ).unwrap();
                let spec_item_id = self.get_new_id();
                let spec_item_id_string = spec_item_id.to_string();
                mem::replace(&mut spec_item.attrs, vec![
                    quote_attr!(cx, #[allow(unused_mut)]),
                    quote_attr!(cx, #[allow(dead_code)]),
                    quote_attr!(cx, #[allow(non_snake_case)]),
                    quote_attr!(cx, #[__PRUSTI_SPEC=$spec_item_id_string]),
                ]);
                spec_item
            },
            _ => {
                unreachable!();
            }
        }
    }

    /// Rewrite all loop invariants.
    fn rewrite_item(&mut self, cx: &mut ExtCtxt, item: ast::Item) -> ast::Item {
        let mut rewriter = LoopInvariantRewriter::new(self, cx);
        rewriter.rewrite_item(item)
    }

    fn expand_item_specifications(&mut self,
                                  cx: &mut ExtCtxt,
                                  attr: &ast::MetaItem,
                                  mut item: ast::Item) -> Vec<ast::Item> {
        trace!("[expand_item_specifications] enter");
        let item_id = self.get_new_id();
        let item_id_string = item_id.to_string();
        let new_attrs = vec![
            quote_attr!(cx, #[__PRUSTI_SPEC=$item_id_string]),
        ];
        let old_attrs = mem::replace(&mut item.attrs, new_attrs);
        let mut proc_specs = vec![RawSpec::from_meta_item(cx, attr)];
        proc_specs.extend(old_attrs.into_iter().map(
            |attr| RawSpec::from_attribute(cx, &attr)
        ));
        assert!(
            !proc_specs.iter().any(|spec| spec.spec_type == SpecType::Invariant),
            "Loop invariant in an unexpected position."
        );
        let spec_item = self.generate_spec_item(cx, &item, &proc_specs);
        debug!("spec_item:\n{}", syntax::print::pprust::item_to_string(&spec_item));
        item = self.rewrite_item(cx, item);
        debug!("item:\n{}", syntax::print::pprust::item_to_string(&item));
        trace!("[expand_item_specifications] exit");
        vec![item, spec_item]
    }

    /// Rewrite a procedure with specifications so that its specs are
    /// type-checked.
    pub fn expand_specifications(&mut self,
                                 cx: &mut ExtCtxt,
                                 _span: Span,
                                 attr: &ast::MetaItem,
                                 item: Annotatable) -> Vec<Annotatable> {
        trace!("[expand_specifications] enter");
        let annotatables = if let Annotatable::Item(item) = item {
            let mut item = item.unwrap();
            let items = self.expand_item_specifications(cx, attr, item);
            items.into_iter().map(|item| Annotatable::Item(ptr::P(item))).collect()
        } else {
            bug!("This should not be reached.")
        };
        trace!("[expand_specifications] exit");
        annotatables
    }

    /// Currently, this method only checks that all attributes were converted.
    pub fn check_ast(&self) {
        unimplemented!()
    }
}

struct LoopInvariantRewriter<'a, 'cx: 'a> {
    parser: &'a mut SpecParser,
    cx: &'a mut ExtCtxt<'cx>,
}

impl<'a, 'cx: 'a> LoopInvariantRewriter<'a, 'cx> {
    pub fn new(parser: &'a mut SpecParser,
               cx: &'a mut ExtCtxt<'cx>) -> LoopInvariantRewriter<'a, 'cx> {
        LoopInvariantRewriter {
            parser: parser,
            cx: cx,
        }
    }
    pub fn rewrite_item(&mut self, item: ast::Item) -> ast::Item {
        self.fold_item_simple(item)
    }
    fn rewrite_block(&mut self, block: ptr::P<ast::Block>,
                     invariants: Vec<RawSpec>) -> ptr::P<ast::Block> {
        debug!("invariants: {:?}", invariants);
        let mut block = block.unwrap();
        if !invariants.is_empty() {
            let assertions: Vec<ast::Stmt> = invariants.into_iter().map(|spec| {
                let assertion_id = self.parser.register_spec(spec.clone()).to_number();
                let spec_expr = &spec.expr;
                quote_stmt!(self.cx, __assertion($assertion_id, $spec_expr)).unwrap()
            }).collect();
            let mut expr = quote_expr!(self.cx,
                {
                    if false {
                        use prusti_contracts::internal::*;
                        $assertions
                    }
                }
            ).unwrap();
            let loop_id = self.parser.get_new_id();
            let loop_id_string = format!(" = \"{}\"", loop_id.to_number());
            let mut builder = syntax::tokenstream::TokenStreamBuilder::new();
            for stream in self.cx.parse_tts(loop_id_string) {
                builder.push(stream);
            }
            expr.attrs = vec![
                ast::Attribute {
                    style: ast::AttrStyle::Outer,
                    path: ast::Path::from_ident(block.span, ast::Ident::from_str("__PRUSTI_SPEC")),
                    tokens: builder.build(),
                    id: syntax::attr::mk_attr_id(),
                    is_sugared_doc: false,
                    span: block.span,
                }
            ].into();
            let stmt = self.cx.stmt_expr(ptr::P(expr));
            block.stmts.insert(0, stmt);
        }
        ptr::P(block)
    }
}

impl<'a, 'cx: 'a> fold::Folder for LoopInvariantRewriter<'a, 'cx> {

    fn fold_expr(&mut self, expr: ptr::P<ast::Expr>) -> ptr::P<ast::Expr> {
        debug!("expr: {}", syntax::print::pprust::expr_to_string(&expr));
        let expr = expr.unwrap();
        let expr = {
            if let ast::ExprKind::While(condition, block, ident) = expr.node {
                let invariants: Vec<_> = expr.attrs.into_iter().map(
                    |attr| RawSpec::from_attribute(self.cx, &attr)
                ).collect();
                let block = self.rewrite_block(block, invariants);
                let loop_id = self.parser.get_new_id();
                let loop_id_string = format!(" = \"{}\"", loop_id.to_number());
                let mut builder = syntax::tokenstream::TokenStreamBuilder::new();
                for stream in self.cx.parse_tts(loop_id_string) {
                    builder.push(stream);
                }
                let mut new_attrs = vec![
                    ast::Attribute {
                        style: ast::AttrStyle::Outer,
                        path: ast::Path::from_ident(expr.span, ast::Ident::from_str("__PRUSTI_SPEC")),
                        tokens: builder.build(),
                        id: syntax::attr::mk_attr_id(),
                        is_sugared_doc: false,
                        span: expr.span,
                    }
                ];
                debug!("attrs: {:?}", new_attrs);
                ast::Expr {
                    id: expr.id,
                    node: ast::ExprKind::While(condition, block, ident),
                    span: expr.span,
                    attrs: new_attrs.into(),
                }
            }
            else if let ast::ExprKind::WhileLet(_pattern, _condition, _block, _ident) = expr.node {
                unimplemented!();
            }
            else if let ast::ExprKind::ForLoop(_pattern, _condition, _block, _ident) = expr.node {
                unimplemented!();
            }
            else if let ast::ExprKind::Loop(_block, _ident) = expr.node {
                unimplemented!();
            } else {
                expr
            }
        };
        ptr::P(expr)
    }

}
