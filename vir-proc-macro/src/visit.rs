use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, DeriveInput};

use super::reify_kind::ReifyKind;

/// Visits exactly the fields that reification descends into: those holding
/// expressions or other generic VIR data.
pub fn derive_visitable(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = input.ident;
    let body = match input.data {
        syn::Data::Struct(syn::DataStruct {
            fields: syn::Fields::Named(syn::FieldsNamed { named, .. }),
            ..
        }) => {
            let visits = named
                .iter()
                .filter(|field| ReifyKind::of_field(field).should_reify())
                .map(|field| {
                    let name = field.ident.as_ref().unwrap();
                    quote! { self.#name.visit_with(v); }
                })
                .collect::<Vec<_>>();
            quote! { #(#visits)* }
        }
        syn::Data::Enum(syn::DataEnum { variants, .. }) => {
            let variants = variants
                .iter()
                .map(|variant| {
                    let variant_name = &variant.ident;
                    match &variant.fields {
                        syn::Fields::Unnamed(syn::FieldsUnnamed { unnamed, .. }) => {
                            let binds = unnamed
                                .iter()
                                .enumerate()
                                .map(|(idx, field)| {
                                    ReifyKind::of_field(field)
                                        .should_reify()
                                        .then(|| quote::format_ident!("v{idx}"))
                                })
                                .collect::<Vec<_>>();
                            let patterns = binds.iter().map(|bind| match bind {
                                Some(bind) => quote! { #bind },
                                None => quote! { _ },
                            });
                            let visits = binds
                                .iter()
                                .flatten()
                                .map(|bind| quote! { #bind.visit_with(v); });
                            quote! {
                                #name::#variant_name(#(#patterns),*) => { #(#visits)* }
                            }
                        }
                        syn::Fields::Unit => quote! { #name::#variant_name => {} },
                        _ => unreachable!(),
                    }
                })
                .collect::<Vec<_>>();
            quote! { match *self { #(#variants),* } }
        }
        _ => unreachable!(),
    };
    TokenStream::from(quote! {
        impl<'vir, Curr, Next> crate::Visitable<'vir, Curr, Next> for &'vir #name<'vir, Curr, Next> {
            fn visit_with<V: crate::Visitor<'vir, Curr, Next> + ?Sized>(&self, v: &mut V) {
                use crate::Visitable as _;
                #body
            }
        }
    })
}
