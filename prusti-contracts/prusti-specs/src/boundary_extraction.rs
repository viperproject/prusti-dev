use quote::ToTokens;
use rustc_hash::FxHashSet;
use syn::{self, visit::Visit, BinOp};

pub struct BoundExtractor {
    // the set of bound variables within that expression
    pub name_set: FxHashSet<String>,
}

impl BoundExtractor {
    pub fn extract_bounds_top(expr: syn::Expr, name: &String, name_set: &FxHashSet<String>) -> Vec<Boundary> {
        // first make sure the expression has the form A ==> B (or equivalent)
        // and then extract a bound from A
        let mut extractor = BoundExtractor {
            name_set: name_set.clone(),
        };
        let simplified = simplify_expression(&expr);
        match simplified {
            syn::Expr::Binary(syn::ExprBinary {
                left: box e1,
                op: syn::BinOp::Or(_),
                ..
            }) => {
                // there are only a few kind of ways to express boundaries on the
                // input values: the ones we allow / recognize so far are:
                //   - !(bound_cond) || property
                if let syn::Expr::Unary(syn::ExprUnary {
                    op: syn::UnOp::Not(_),
                    expr: box bound_expr,
                    ..
                }) = e1
                {
                    // in this case, the contents of the quantifier have the form
                    // !(potential boundary condition) || (check)
                    extractor.extract_bounds_recursive(bound_expr, name)
                } else {
                    vec![]
                }
            }
            _ => vec![],
        }
    }


    pub fn extract_bounds_recursive(&mut self, expr: syn::Expr, name: &String) -> Vec<Boundary> {
        let simplified = simplify_expression(&expr);
        match simplified {
            syn::Expr::Binary(syn::ExprBinary {
                box left,
                box right,
                op,
                ..
            }) => {
                match op {
                    // combining results:
                    syn::BinOp::And(_) => {
                        let mut left_bound = self.extract_bounds_recursive(left, name);
                        let mut right_bound = self.extract_bounds_recursive(right, name);
                        left_bound.append(&mut right_bound);
                        left_bound
                    }
                    BinOp::Lt(_) | BinOp::Le(_) | BinOp::Gt(_) | BinOp::Ge(_) => {
                        // one of the two operators have to include "name" if this is
                        // is a boundary:
                        let variables = self.find_identifiers(&expr);
                        if variables.contains(name) {
                            // might be a bound for our current variable
                            // transform it such that left is exactly x,
                            // and right is the upper or lower boundary
                            let bound_opt = self.derive_boundary(name, &left, &right, &op);
                            if let Some(bound) = bound_opt {
                                vec![bound]
                            } else {
                                vec![]
                            }
                        } else {
                            // definitely not a boundary for our variable
                            vec![]
                        }
                    }

                    _ => vec![],
                }
            }
            syn::Expr::Unary(syn::ExprUnary {
                op: syn::UnOp::Not(_),
                expr: box sub_expr,
                ..
            }) => {
                let sub_bounds = self.extract_bounds_recursive(sub_expr, name);
                // invert all the boundaries of the sub_expression
                sub_bounds
                    .iter()
                    .map(|bound| bound.clone().invert())
                    .collect()
            }
            _ => vec![],
        }
    }

    pub fn derive_boundary(
        &self,
        name: &String,
        left: &syn::Expr,
        right: &syn::Expr,
        op: &syn::BinOp,
    ) -> Option<Boundary> {
        let left_simp = simplify_expression(left);
        let right_simp = simplify_expression(right);
        let mut new_op = *op;
        let mut bound_expr = None;

        // for now do it simple: One of the two expressions has to be
        // exactly "name"
        let left_name_opt = expression_name(&left_simp);
        let right_name_opt = expression_name(&right_simp);
        if let Some(left_name) = left_name_opt {
            if &left_name == name {
                bound_expr = Some(right.clone());
            }
        }
        if let Some(right_name) = right_name_opt {
            if &right_name == name {
                // in case they both are just "name", this is not a boundary
                assert!(bound_expr.is_none());
                // turn the condition around!
                new_op = match op {
                    BinOp::Lt(_) => BinOp::Gt(syn::token::Gt::default()),
                    BinOp::Gt(_) => BinOp::Lt(syn::token::Lt::default()),
                    BinOp::Le(_) => BinOp::Ge(syn::token::Ge::default()),
                    BinOp::Ge(_) => BinOp::Le(syn::token::Le::default()),
                    _ => panic!(),
                };
                bound_expr = Some(left.clone());
            }
        }
        // now we can be sure (if bound_expr is some) that our comparison has the
        // form `name op bound_expr`

        // now create boundary:
        if let Some(bound) = bound_expr {
            let (included, kind) = match new_op {
                BinOp::Lt(_) => (false, BoundaryKind::Upper),
                BinOp::Gt(_) => (false, BoundaryKind::Lower),
                BinOp::Le(_) => (true, BoundaryKind::Upper),
                BinOp::Ge(_) => (true, BoundaryKind::Lower),
                // this is actually checked before calling this function
                _ => unreachable!(),
            };
            let dependent_vars = self.find_identifiers(&bound);
            Some(Boundary {
                bound,
                included,
                kind,
                dependent_vars,
            })
        } else {
            None
        }
    }

    fn find_identifiers(&self, expr: &syn::Expr) -> FxHashSet<String> {
        let mut finder = IdentifierFinder {
            bound_vars: FxHashSet::default(),
        };
        finder.visit_expr(expr);
        finder
            .bound_vars
            .into_iter()
            .filter(|x| self.name_set.contains(x))
            .collect()
    }
}

// The following two functions should go into some syn-helper file or similar

/// syn expressions can be part of a block, put into braces etc, all of which make
/// it harder to analyze them.
/// This function should help us simplify
pub fn simplify_expression(expr: &syn::Expr) -> syn::Expr {
    match expr {
        syn::Expr::Block(syn::ExprBlock { block, .. }) => {
            if block.stmts.len() == 1 {
                let res = block.stmts.get(0).unwrap().clone();
                if let syn::Stmt::Expr(sub_expr) = res {
                    let res = simplify_expression(&sub_expr);
                    return res;
                }
            }
        }
        syn::Expr::Paren(syn::ExprParen {
            expr: box sub_expr, ..
        }) => {
            let res = simplify_expression(sub_expr);
            return res;
        }
        syn::Expr::Type(syn::ExprType { expr: sub_expr, .. }) => {
            let res = simplify_expression(sub_expr);
            return res;
        }
        _ => {}
    }
    expr.clone()
}

// if expression is a identifier, get the name:
pub fn expression_name(expr: &syn::Expr) -> Option<String> {
    if let syn::Expr::Path(syn::ExprPath { path, .. }) = expr {
        return Some(path.to_token_stream().to_string());
    }
    None
}

#[derive(Clone)]
pub struct Boundary {
    pub bound: syn::Expr,
    /// Whether or not that value is still in the range
    pub included: bool,
    /// upper or lower bound?
    pub kind: BoundaryKind,
    /// other variables that are part of the current quantifier, that this
    /// boundary relies on (i.e. must have been defined before)
    pub dependent_vars: FxHashSet<String>,
}

#[derive(Clone, Debug, Copy, PartialEq)]
pub enum BoundaryKind {
    Upper,
    Lower,
}

impl Boundary {
    pub fn invert(self) -> Self {
        let kind = match self.kind {
            BoundaryKind::Upper => BoundaryKind::Lower,
            BoundaryKind::Lower => BoundaryKind::Upper,
        };
        Self {
            bound: self.bound,
            included: !self.included,
            kind,
            dependent_vars: self.dependent_vars,
        }
    }

}

// a Visitor to extract identifiers that occurr in an expression
pub struct IdentifierFinder {
    pub bound_vars: FxHashSet<String>,
}

impl<'ast> syn::visit::Visit<'ast> for IdentifierFinder {
    fn visit_expr_path(&mut self, expr_path: &'ast syn::ExprPath) {
        if expr_path.path.segments.len() == 1 {
            // it is an identifier
            let name = expr_path.to_token_stream().to_string();
            self.bound_vars.insert(name);
        }
        // keep visiting :)
        syn::visit::visit_expr_path(self, expr_path);
    }
}
