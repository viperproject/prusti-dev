use crate::runtime_checks::boundary_extraction::{is_primitive_number, BoundExtractor};
use proc_macro2::TokenStream;
use quote::{quote, ToTokens};
use rustc_hash::FxHashSet;
use syn::{parse_quote, parse_quote_spanned, spanned::Spanned};

pub(crate) enum QuantifierKind {
    Forall,
    Exists,
}

pub(crate) fn translate_quantifier_expression(
    closure: &syn::ExprClosure,
    kind: QuantifierKind,
    is_outer: bool,
) -> syn::Expr {
    let mut name_set: FxHashSet<String> = FxHashSet::default();
    // the variables that occurr as arguments
    let bound_vars: Vec<(String, syn::Type)> = closure
        .inputs
        .iter()
        .map(|pat: &syn::Pat| {
            if let syn::Pat::Type(syn::PatType {
                pat: box syn::Pat::Ident(id),
                ty: box ty,
                ..
            }) = pat
            {
                let name_str = id.to_token_stream().to_string();
                name_set.insert(name_str.clone());
                (name_str, ty.clone())
            } else {
                // maybe we can throw a more sensible error and make the
                // check function a dummy check function
                panic!("quantifiers without type annotations can not be checked at runtime");
            }
        })
        .collect();

    // look for the runtime_quantifier_bounds attribute:
    let manual_bounds = BoundExtractor::manual_bounds(closure.clone(), bound_vars.clone());
    let bounds = manual_bounds
        .unwrap_or_else(|| BoundExtractor::derive_ranges(*closure.body.clone(), bound_vars));

    let mut expr = *closure.body.clone();

    for ((name, ty), range_expr) in bounds.iter().rev() {
        let name_token: TokenStream = name.parse().unwrap();
        let expr_string = expr
            .span()
            .source_text()
            .unwrap_or_else(|| quote!(expr).to_string());
        let error_string = format!(
            "\n\t> expression {} was violated for index {}=",
            expr_string, name_token
        );
        let error_len = error_string.len();
        // extend the error message if it's a type we know we can
        // present to the user
        let info_statements: syn::Block = if is_primitive_number(ty) && is_outer {
            parse_quote_spanned! {expr.span() => {
                prusti_rtc_info_buffer[prusti_rtc_info_len..prusti_rtc_info_len+#error_len].copy_from_slice(#error_string.as_bytes());
                let num_str = ::prusti_contracts::runtime_check_internals::num_to_str(
                    #name_token,
                    &mut num_buffer
                );
                prusti_rtc_info_buffer[
                    prusti_rtc_info_len+#error_len..prusti_rtc_info_len+#error_len+num_str.len()
                ].copy_from_slice(num_str.as_bytes());
                prusti_rtc_info_len = prusti_rtc_info_len
                    + #error_len
                    + num_str.len();
            }}
        } else {
            parse_quote! {{}}
        };

        // maybe never turn them into strings in the first place..
        expr = match kind {
            QuantifierKind::Forall => {
                let res = quote! {
                    {
                        let mut holds_forall = true;
                        let mut num_buffer = [0u8; 64];
                        for #name_token in #range_expr {
                            if !(#expr) {
                                // extend the error message
                                #info_statements;

                                holds_forall = false;
                                break;
                            }
                        }
                        holds_forall
                    }
                };
                syn::parse2(res).unwrap()
            }
            QuantifierKind::Exists => {
                let res = quote! {
                {
                    let mut exists = false;
                    for #name_token in #range_expr {
                        if #expr {
                            exists = true;
                            break;
                        }
                    }
                    exists
                }
                };
                syn::parse2(res).unwrap()
            }
        }
    }
    expr
}
