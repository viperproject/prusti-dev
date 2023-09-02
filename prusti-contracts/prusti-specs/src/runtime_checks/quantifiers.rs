use crate::runtime_checks::{
    boundary_extraction::{is_primitive_number, BoundExtractor},
    error_messages,
};
use proc_macro2::TokenStream;
use quote::{quote, ToTokens};
use rustc_hash::FxHashSet;

pub(crate) enum QuantifierKind {
    Forall,
    Exists,
}

pub(crate) fn translate_quantifier_expression(
    closure: &syn::ExprClosure,
    kind: QuantifierKind,
    is_outer: bool,
) -> syn::Result<syn::Expr> {
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

    // look for the runtime_quantifier_bounds attribute, or try to derive
    // boundaries from expressions of the form `boundary ==> expr`
    let manual_bounds_opt = BoundExtractor::manual_bounds(closure.clone(), bound_vars.clone());
    let bounds = if let Some(manual_bounds) = manual_bounds_opt {
        manual_bounds?
    } else {
        BoundExtractor::derive_ranges(*closure.body.clone(), bound_vars)?
    };

    let mut expr = *closure.body.clone();

    for ((name, ty), range_expr) in bounds.iter().rev() {
        let name_token: TokenStream = name.parse().unwrap();
        let info_statements = if is_primitive_number(ty) && is_outer {
            Some(error_messages::extend_error_indexed(&expr, &name_token))
        } else {
            None
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
    Ok(expr)
}
