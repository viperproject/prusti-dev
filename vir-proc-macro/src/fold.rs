use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, DeriveInput};

use super::reify_kind::ReifyKind;

/// Folds exactly the fields that reification descends into: those holding
/// expressions or other generic VIR data. The data is only reallocated if one
/// of them changed.
pub fn derive_foldable(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = input.ident;
    let body = match input.data {
        syn::Data::Struct(syn::DataStruct {
            fields: syn::Fields::Named(syn::FieldsNamed { named, .. }),
            ..
        }) => {
            let folded = named
                .iter()
                .filter(|field| ReifyKind::of_field(field).should_reify())
                .map(|field| field.ident.as_ref().unwrap())
                .collect::<Vec<_>>();
            let fields = named.iter().map(|field| {
                let name = field.ident.as_ref().unwrap();
                if ReifyKind::of_field(field).should_reify() {
                    quote! { #name: #name.unwrap_or(self.#name) }
                } else {
                    quote! { #name: self.#name }
                }
            });
            quote! {
                #(let #folded = self.#folded.fold_with(f);)*
                if true #(&& #folded.is_none())* {
                    return None;
                }
                Some(crate::with_vcx(|vcx| vcx.alloc(#name { #(#fields),* })))
            }
        }
        syn::Data::Enum(syn::DataEnum { variants, .. }) => {
            let variants = variants
                .iter()
                .map(|variant| {
                    let variant_name = &variant.ident;
                    match &variant.fields {
                        syn::Fields::Unnamed(syn::FieldsUnnamed { unnamed, .. }) => {
                            let vbinds = (0..unnamed.len())
                                .map(|idx| quote::format_ident!("v{idx}"))
                                .collect::<Vec<_>>();
                            let folded = unnamed
                                .iter()
                                .enumerate()
                                .filter(|(_, field)| ReifyKind::of_field(field).should_reify())
                                .map(|(idx, _)| (&vbinds[idx], quote::format_ident!("opt{idx}")))
                                .collect::<Vec<_>>();
                            let compute_fields = folded
                                .iter()
                                .map(|(vbind, obind)| quote! { let #obind = #vbind.fold_with(f); });
                            let unchanged = folded.iter().map(|(_, obind)| obind);
                            let fields = unnamed.iter().enumerate().map(|(idx, field)| {
                                let vbind = &vbinds[idx];
                                if ReifyKind::of_field(field).should_reify() {
                                    let obind = quote::format_ident!("opt{idx}");
                                    quote! { #obind.unwrap_or(#vbind) }
                                } else {
                                    quote! { #vbind }
                                }
                            });
                            quote! {
                                #name::#variant_name(#(#vbinds),*) => {
                                    #(#compute_fields)*
                                    if true #(&& #unchanged.is_none())* {
                                        return None;
                                    }
                                    Some(crate::with_vcx(|vcx| {
                                        vcx.alloc(#name::#variant_name(#(#fields),*))
                                    }))
                                }
                            }
                        }
                        syn::Fields::Unit => quote! { #name::#variant_name => None },
                        _ => unreachable!(),
                    }
                })
                .collect::<Vec<_>>();
            quote! { match **self { #(#variants),* } }
        }
        _ => unreachable!(),
    };
    TokenStream::from(quote! {
        impl<'vir, Curr, Next> crate::Foldable<'vir, Curr, Next> for &'vir #name<'vir, Curr, Next> {
            #[allow(unused_variables)]
            fn fold_with<F: crate::Folder<'vir, Curr, Next> + ?Sized>(&self, f: &mut F) -> Option<Self> {
                use crate::Foldable as _;
                #body
            }
        }
    })
}
