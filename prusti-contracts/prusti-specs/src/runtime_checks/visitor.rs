use crate::runtime_checks::{
    associated_function_info::AssociatedFunctionInfo,
    boundary_extraction,
    check_type::CheckItemType,
    quantifiers::{translate_quantifier_expression, QuantifierKind},
};
use proc_macro2::TokenStream;
use quote::{quote, ToTokens};
use syn::{parse_quote_spanned, spanned::Spanned, visit_mut::VisitMut, Expr};

pub(crate) struct CheckVisitor {
    pub function_info: AssociatedFunctionInfo,
    pub within_old: bool,
    pub within_before_expiry: bool,
    pub check_type: CheckItemType,
    /// Whether the current expression is part of the outermost
    /// expression. If yes, and we encounter a conjunction or
    /// forall quantifier, we can extend the reported error with
    /// more precise information
    is_outer: bool,
    contains_conjunction: bool,
}

impl CheckVisitor {
    pub(crate) fn new(function_info: AssociatedFunctionInfo, check_type: CheckItemType) -> Self {
        Self {
            function_info,
            within_old: false,
            within_before_expiry: false,
            check_type,
            is_outer: true,
            contains_conjunction: false,
        }
    }
}

impl VisitMut for CheckVisitor {
    fn visit_expr_mut(&mut self, expr: &mut Expr) {
        let was_outer = self.is_outer;
        match expr {
            Expr::Path(expr_path) => {
                // collect arguments that occurr within old expression
                // these are the ones we wanna clone
                if let Some(ident) = expr_path.path.get_ident() {
                    let name = ident.to_token_stream().to_string();
                    if let Some(arg) = self.function_info.get_mut_arg(&name) {
                        // argument used within an old expression?
                        // not already marked as used in old?
                        if self.check_type.gets_old_args() && (self.within_old || (!arg.is_ref && arg.is_mutable)) {
                            // if it was not already marked to be stored
                            // needs to be checked for indeces to be correct
                            arg.used_in_old = true;
                            // replace the identifier with the correct field access
                            let index_token: TokenStream =
                                arg.index.to_string().parse().unwrap();
                            let new_path: syn::Expr = parse_quote_spanned! { expr.span() => (old_values.#index_token)};
                            *expr = new_path;
                        }
                    } else if self.within_before_expiry && name == *"result" {
                        let new_path: syn::Expr = parse_quote_spanned! { expr.span() =>
                            result_before_expiry.0
                        };
                        *expr = new_path;
                    }
                }
            }
            Expr::Call(call)
                // func: box Expr::Path(syn::ExprPath { path, .. }),
                // ..
            => {
                self.is_outer = false;
                let path_expr = (*call.func).clone();
                // move this function, has nothing to do with boundary extraction
                let name = if let Some(name) = boundary_extraction::expression_name(&path_expr) {
                    name
                } else {
                    // still visit recursively
                    syn::visit_mut::visit_expr_mut(self, expr);
                    return;
                };
                match name.as_str() {
                    ":: prusti_contracts :: old" | "prusti_contracts :: old" | "old" => {
                        // for this function we can savely try to get
                        // more precise errors about the contents
                        self.is_outer = true;
                        // for prusti_assert etc we can not resolve old here
                        if self.check_type.is_inlined() {
                            syn::visit_mut::visit_expr_call_mut(self, call);
                            // just leave it as it is.. resolve it on mir level
                        } else {
                            let sub_expr = call.args.pop();
                            // remove old-call and replace with content expression
                            *expr = sub_expr.unwrap().value().clone();
                            self.within_old = true;
                            self.visit_expr_mut(expr);
                            // will cause all variables below to be replaced by old_value.some_field
                            self.within_old = false;
                        }
                    }
                    ":: prusti_contracts :: before_expiry" | "prusti_contracts :: before_expiry" | "before_expiry" => {
                        let sub_expr = call.args.pop();
                        *expr = sub_expr.unwrap().value().clone();
                        self.within_before_expiry = true;
                        self.visit_expr_mut(expr);
                        // will cause all variables below to be replaced by old_value.some_field
                        self.within_before_expiry = false;
                    },
                    ":: prusti_contracts :: forall" => {
                        // arguments are triggers and then the closure:
                        let quant_closure_expr: syn::Expr = call.args.last().unwrap().clone();
                        if let syn::Expr::Closure(mut expr_closure) = quant_closure_expr {
                            // since this is a conjunction, we can get
                            // more information about subexpressions failing
                            self.is_outer = was_outer;
                            self.visit_expr_mut(&mut expr_closure.body);
                            // we are throwing away any triggers
                            // extract all the relevant information, construct a
                            // new expression
                            let check_expr = translate_quantifier_expression(
                                &expr_closure,
                                QuantifierKind::Forall,
                                was_outer,
                            );
                            *expr = check_expr;
                        }                    }
                    ":: prusti_contracts :: exists" => {
                        // here we don't want every failing iteration
                        // to give us additional info
                        syn::visit_mut::visit_expr_call_mut(self, call);
                        // extend self.surround_quantifiers correctly!
                        let closure_expression: syn::Expr = call.args.last().unwrap().clone();
                        if let syn::Expr::Closure(expr_closure) = closure_expression {
                            let check_expr = translate_quantifier_expression(
                                &expr_closure,
                                QuantifierKind::Exists,
                                false,
                            );
                            *expr = check_expr
                        }
                    },
                    _ => syn::visit_mut::visit_expr_mut(self, expr),
                }
            },
            Expr::Binary(syn::ExprBinary {
                left: box left,
                op: syn::BinOp::And(_),
                right: box right, ..
            }) => {
                if was_outer {
                    syn::visit_mut::visit_expr_mut(self, left);
                    let left_contains_conjunction = self.contains_conjunction;
                    self.contains_conjunction = false;
                    syn::visit_mut::visit_expr_mut(self, right);
                    let right_contains_conjunction = self.contains_conjunction;
                    // call check function on both sides:
                    let left_str = left.span().source_text().unwrap_or_else(|| quote!(left).to_string());
                    let left_error_str = format!("\n\t> expression {} was violated.", left_str);
                    let right_str = right.span().source_text().unwrap_or_else(|| quote!(right).to_string());
                    let right_error_str = format!("\n\t> expression {} was violated.", right_str);

                    // the expression will be split up even further
                    if !left_contains_conjunction {
                        let new_left = parse_quote_spanned!{left.span() =>
                            ::prusti_contracts::runtime_check_internals::check_expr(#left, #left_error_str, &mut prusti_rtc_info_buffer, &mut prusti_rtc_info_len)
                        };
                        *left = new_left;
                    }
                    if !right_contains_conjunction {
                        let new_right = parse_quote_spanned! {right.span() =>
                            ::prusti_contracts::runtime_check_internals::check_expr(#right, #right_error_str, &mut prusti_rtc_info_buffer, &mut prusti_rtc_info_len)
                        };
                        *right = new_right;
                    }
                    // signal to parent that it doesnt need to wrap this expression
                    // into a separate check function, since it will be further split up
                    self.contains_conjunction = true;
                }
            },
            Expr::Block(_) | Expr::Paren(_) => {
                syn::visit_mut::visit_expr_mut(self, expr);
            }
            _ => {
                self.is_outer = false;
                syn::visit_mut::visit_expr_mut(self, expr);
            }
        }
        self.is_outer = was_outer;
    }
}
