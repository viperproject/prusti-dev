use crate::runtime_checks::utils;
use quote::ToTokens;
use rustc_hash::FxHashSet;
use syn::{self, parse_quote, parse_quote_spanned, spanned::Spanned, visit::Visit, BinOp};

type LoopBoundaries = ((String, syn::Type), syn::ExprRange);

pub(crate) struct BoundExtractor {
    // the set of bound variables within that expression
    pub name_set: FxHashSet<String>,
}

/// Try to find manually annotated boundaries with the #[runtime_quantifier_bounds]
/// attribute. Returns None if there is no such attribute, Some(error)
/// if there is one, but the contained ranges are false, and the tokens
/// of the ranges otherwise.
pub(crate) fn manual_bounds(
    expr: syn::ExprClosure,
    bound_vars: Vec<(String, syn::Type)>,
) -> Option<syn::Result<Vec<LoopBoundaries>>> {
    let manual_bounds = utils::get_attribute_contents(
        "prusti :: runtime_quantifier_bounds".to_string(),
        &expr.attrs,
    )?;
    let bounds_expr: syn::Expr = simplify_expression(&syn::parse2(manual_bounds).ok()?);
    // there is either one or multiple
    let bounds_vec = match bounds_expr {
        syn::Expr::Tuple(expr_tuple) => {
            let mut ranges: Vec<syn::ExprRange> = Vec::new();
            for range in expr_tuple.elems.iter() {
                let range = simplify_expression(range);
                if let syn::Expr::Range(expr_range) = range {
                    ranges.push(expr_range);
                } else {
                    return Some(Err(syn::Error::new(
                        range.span(),
                        "Runtime checks: quantifier boundaries must be provided as ranges",
                    )));
                }
            }
            ranges
        }
        syn::Expr::Range(range_expr) => vec![range_expr],
        _ => {
            return Some(Err(syn::Error::new(
                bounds_expr.span(),
                "Runtime checks: quantifier boundaries must be provided as ranges",
            )));
        }
    };
    if bounds_vec.len() != bound_vars.len() {
        return Some(Err(syn::Error::new(
                    expr.span(),
                    "Runtime checks: the provided number of ranges does not match the number of closure arguments.")));
    }
    assert!(bounds_vec.len() == bound_vars.len());
    Some(Ok(bound_vars.into_iter().zip(bounds_vec).collect()))
}

/// If no ranges were manually annotated, this function tries to derive them by looking at
/// the contained expression. This only works for a very limited set of cases.
pub(crate) fn derive_ranges(
    body: syn::Expr,
    args: Vec<(String, syn::Type)>,
) -> syn::Result<Vec<LoopBoundaries>> {
    if args.len() > 1 {
        return Err(syn::Error::new(
            body.span(),
            "Runtime checks: multiple args without manually defined boundaries are not allowed",
        ));
    }
    let name_set: FxHashSet<String> = args.iter().map(|el| el.0.clone()).collect();
    let mut boundaries: Vec<((String, syn::Type), syn::ExprRange)> = Vec::new();
    let bounds_expr = split_implication_lhs(&body).unwrap_or(parse_quote! {()});
    let boundary_extractor = BoundExtractor { name_set };
    for (name, ty) in args.iter() {
        let range_expr: syn::ExprRange = if utils::is_primitive_number(ty) {
            let bounds = boundary_extractor.extract_bounds_recursive(&bounds_expr, name);
            let mut upper_bound_opt = None;
            let mut lower_bound_opt = None;

            // if there are multiple variables, potentially with dependencies
            // the loops need to be in a specific order
            assert!(bounds.len() <= 2);
            let mut include_upper = true; // if we have the MAX upper limit,
            for Boundary {
                kind,
                bound,
                included,
                ..
            } in bounds.iter()
            {
                // include it
                match *kind {
                    BoundaryKind::Upper => {
                        // first idea was to add one here if inclusive, but
                        // this can lead to overflows! Need to use ..=x syntax
                        if upper_bound_opt.is_some() {
                            return Err(syn::Error::new(
                                body.span(),
                                format!(
                                    "Runtime checks: multiple upper bounds defined for {}",
                                    name
                                ),
                            ));
                        }
                        upper_bound_opt = Some(bound.clone());
                        include_upper = *included;
                    }
                    BoundaryKind::Lower => {
                        if lower_bound_opt.is_some() {
                            return Err(syn::Error::new(
                                body.span(),
                                format!(
                                    "Runtime checks: multiple lower bounds defined for {}",
                                    name
                                ),
                            ));
                        };
                        lower_bound_opt = if *included {
                            // lower bound works the other way around
                            Some(bound.clone())
                        } else {
                            Some(parse_quote! {
                                #bound + 1
                            })
                        }
                    }
                }
            }
            let upper_bound = if let Some(upper_bound) = upper_bound_opt {
                upper_bound
            } else {
                // upper bounds are required unless the type is very small
                if utils::ty_small_enough(ty) {
                    parse_quote_spanned! {body.span() =>
                        #ty::MAX
                    }
                } else {
                    return Err(syn::Error::new(
                        body.span(),
                        format!(
                            "Runtime checks: a quantifier over type {} requires an upper bound",
                            ty.to_token_stream()
                        ),
                    ));
                }
            };
            let lower_bound = if let Some(lower_bound) = lower_bound_opt {
                lower_bound
            } else {
                // lower bounds are required unless the type is very small or unsigned
                if utils::ty_small_enough(ty) || utils::ty_unsigned(ty) {
                    parse_quote_spanned! {body.span() =>
                        #ty::MIN
                    }
                } else {
                    return Err(syn::Error::new(
                        body.span(),
                        format!(
                            "Runtime checks: a quantifier over type {} requires a lower bound",
                            ty.to_token_stream()
                        ),
                    ));
                }
            };

            if include_upper {
                parse_quote_spanned! {body.span() =>
                    (#lower_bound)..=(#upper_bound)
                }
            } else {
                parse_quote_spanned! {body.span() =>
                    (#lower_bound)..(#upper_bound)
                }
            }
        } else {
            return Err(syn::Error::new(
                body.span(),
                format!(
                    "Runtime checks: quantifier over type {} is not supported",
                    ty.to_token_stream()
                ),
            ));
        };
        boundaries.push(((name.clone(), ty.clone()), range_expr));
    }
    Ok(boundaries)
}

/// Given the body of a quantifier, if it contains an implication get its lefthandside
pub fn split_implication_lhs(expr: &syn::Expr) -> Option<syn::Expr> {
    // first make sure the expression has the form A ==> B (or equivalent)
    let simplified = simplify_expression(expr);
    if let syn::Expr::Binary(syn::ExprBinary {
        left:
            box syn::Expr::Unary(syn::ExprUnary {
                op: syn::UnOp::Not(_),
                expr: box bound_expr,
                ..
            }),
        op: syn::BinOp::Or(_),
        ..
    }) = simplified
    {
        // in this case, the contents of the quantifier have the form
        // !(potential boundary condition) || (check)
        Some(bound_expr.clone())
    } else {
        None
    }
}
impl BoundExtractor {
    fn extract_bounds_recursive(&self, expr: &syn::Expr, name: &String) -> Vec<Boundary> {
        let simplified = simplify_expression(expr);
        match simplified {
            syn::Expr::Binary(syn::ExprBinary {
                box left,
                box right,
                op,
                ..
            }) => {
                match op {
                    // combining results of and:
                    syn::BinOp::And(_) => {
                        let mut left_bound = self.extract_bounds_recursive(&left, name);
                        let mut right_bound = self.extract_bounds_recursive(&right, name);
                        left_bound.append(&mut right_bound);
                        left_bound
                    }
                    // generate boundaries from comparisons if one of the sides
                    // is the name we are currently looking for
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
                let sub_bounds = self.extract_bounds_recursive(&sub_expr, name);
                // invert all the boundaries derived of the sub_expression
                sub_bounds
                    .iter()
                    .map(|bound| bound.clone().invert())
                    .collect()
            }
            _ => vec![],
        }
    }

    /// Given a comparison, derive the corresponding boundary for the variable
    /// we are currently dealing with
    fn derive_boundary(
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
        let left_name_opt = utils::expression_name(&left_simp);
        let right_name_opt = utils::expression_name(&right_simp);
        if let Some(left_name) = left_name_opt {
            if &left_name == name {
                bound_expr = Some(right.clone());
            }
        }
        if let Some(right_name) = right_name_opt {
            if &right_name == name {
                // in case they both are just "name", this cannot be used as a
                // boundary
                if bound_expr.is_some() {
                    return None;
                }
                // turn the condition around because implication is of the form
                // not cond || expression
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
        // a Visitor to extract identifiers that occurr in an expression
        struct IdentifierFinder {
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

/// syn expressions can be part of a block, put into braces etc, all of which make
/// it harder to analyze them. This function removes these.
fn simplify_expression(expr: &syn::Expr) -> syn::Expr {
    match expr {
        syn::Expr::Block(syn::ExprBlock { block, .. }) => {
            if block.stmts.len() == 1 {
                let res = block.stmts.get(0).unwrap().clone();
                if let syn::Stmt::Expr(sub_expr) = res {
                    simplify_expression(&sub_expr)
                } else {
                    expr.clone()
                }
            } else {
                expr.clone()
            }
        }
        syn::Expr::Paren(syn::ExprParen {
            expr: box sub_expr, ..
        }) => simplify_expression(sub_expr),
        syn::Expr::Type(syn::ExprType { expr: sub_expr, .. }) => simplify_expression(sub_expr),
        _ => expr.clone(),
    }
}

#[derive(Clone)]
pub(crate) struct Boundary {
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
pub(crate) enum BoundaryKind {
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
