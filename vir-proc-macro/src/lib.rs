#![feature(box_patterns)]

use proc_macro::TokenStream;

mod hash;
mod reify;
pub(crate) mod reify_kind;
mod serde;

#[proc_macro_derive(VirHash)]
pub fn derive_hash(input: TokenStream) -> TokenStream {
    hash::derive_hash(input)
}

#[proc_macro_derive(VirReify, attributes(vir))]
pub fn derive_reify(input: TokenStream) -> TokenStream {
    reify::derive_reify(input)
}

#[proc_macro_derive(VirSerde, attributes(vir))]
pub fn derive_serde(input: TokenStream) -> TokenStream {
    serde::derive_serde(input)
}

fn params_to_args_and_params(
    generics: &syn::Generics,
) -> (Vec<syn::GenericArgument>, Vec<syn::GenericParam>) {
    let mut i = 0;
    let generic_params = generics
        .params
        .iter()
        .filter_map(|param| match param.clone() {
            param @ syn::GenericParam::Type(..) => {
                i += 1;
                (i > 2).then_some(param)
            }
            param => Some(param),
        })
        .collect::<Vec<_>>();
    let mut i = 0;
    let generic_args = generics
        .params
        .iter()
        .map(|param| match param {
            syn::GenericParam::Type(ty) => {
                i += 1;
                match i {
                    1 => syn::parse_quote!(()),
                    2 => syn::parse_quote!(!),
                    _ => {
                        let ident = &ty.ident;
                        syn::parse_quote! { #ident }
                    }
                }
            }
            syn::GenericParam::Lifetime(l) => syn::GenericArgument::Lifetime(l.lifetime.clone()),
            syn::GenericParam::Const(c) => {
                let ident = &c.ident;
                syn::parse_quote! { #ident }
            }
        })
        .collect::<Vec<_>>();
    (generic_args, generic_params)
}
