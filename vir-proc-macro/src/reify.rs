use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, DeriveInput};

use super::reify_kind::ReifyKind;

pub fn derive_reify(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = input.ident;
    let slice_impl = quote! {
        impl<'vir, Curr: Copy, NextA, NextB> crate::Reify<'vir, Curr>
            for [&'vir #name<'vir, Curr, ExprKindGen<'vir, NextA, NextB>>]
        {
            type Next = &'vir [&'vir #name<'vir, NextA, NextB>];
            fn reify<'tcx>(&self, vcx: &'vir crate::VirCtxt<'tcx>, lctx: Curr) -> Self::Next {
                vcx.alloc_slice(&self.iter()
                    .map(|elem| elem.reify(vcx, lctx))
                    .collect::<Vec<_>>())
            }
        }
    };
    TokenStream::from(match input.data {
        syn::Data::Struct(syn::DataStruct {
            fields: syn::Fields::Named(syn::FieldsNamed {
                named,
                ..
            }),
            ..
        }) => {
            let compute_fields = named.iter()
                .filter_map(|field| {
                    let name = field.ident.as_ref().unwrap();
                    if ReifyKind::of_field(field).should_reify() {
                        Some(quote! {
                            let #name = self.#name.reify(vcx, lctx);
                        })
                    } else {
                        None
                    }
                })
                .collect::<Vec<_>>();
            let fields = named.iter()
                .map(|field| {
                    let name = field.ident.as_ref().unwrap();
                    if ReifyKind::of_field(field).should_reify() {
                        quote! { #name: #name }
                    } else {
                        quote! { #name: self.#name }
                    }
                })
                .collect::<Vec<_>>();
            quote! {
                impl<'vir, Curr: Copy, NextA, NextB> crate::Reify<'vir, Curr>
                    for &'vir #name<'vir, Curr, ExprKindGen<'vir, NextA, NextB>>
                {
                    type Next = &'vir #name<'vir, NextA, NextB>;
                    fn reify<'tcx>(&self, vcx: &'vir crate::VirCtxt<'tcx>, lctx: Curr) -> Self::Next {
                        #(#compute_fields)*
                        vcx.alloc(#name { #(#fields),* })
                    }
                }
                #slice_impl
            }
        }
        syn::Data::Enum(syn::DataEnum {
            variants,
            ..
        }) => {
            let variants = variants.iter()
                .map(|variant| {
                    let variant_name = &variant.ident;
                    match &variant.fields {
                        syn::Fields::Unnamed(syn::FieldsUnnamed {
                            unnamed,
                            ..
                        }) => {
                            let vbinds = (0..unnamed.len())
                                .map(|idx| quote::format_ident!("v{idx}"))
                                .collect::<Vec<_>>();
                            let obinds = (0..unnamed.len())
                                .map(|idx| quote::format_ident!("opt{idx}"))
                                .collect::<Vec<_>>();
                            let compute_fields = unnamed.iter()
                                .enumerate()
                                .filter_map(|(idx, field)| if ReifyKind::of_field(field).should_reify() {
                                    let vbind = &vbinds[idx];
                                    let obind = &obinds[idx];
                                    Some(quote! {
                                        let #obind = #vbind.reify(vcx, lctx);
                                    })
                                } else {
                                    None
                                })
                                .collect::<Vec<_>>();
                            let fields = unnamed.iter()
                                .enumerate()
                                .map(|(idx, field)| if ReifyKind::of_field(field).should_reify() {
                                    let obind = &obinds[idx];
                                    quote! { #obind }
                                } else {
                                    let vbind = &vbinds[idx];
                                    quote! { #vbind }
                                })
                                .collect::<Vec<_>>();
                            quote! {
                                #name::#variant_name(#(#vbinds),*) => {
                                    #(#compute_fields)*
                                    vcx.alloc(#name::#variant_name(#(#fields),*))
                                }
                            }
                        },
                        syn::Fields::Unit => quote! {
                            #name::#variant_name => &#name::#variant_name
                        },
                        _ => unreachable!(),
                    }
                })
                .collect::<Vec<_>>();
            quote! {
                impl<'vir, Curr: Copy, NextA, NextB> crate::Reify<'vir, Curr>
                    for &'vir #name<'vir, Curr, ExprKindGen<'vir, NextA, NextB>>
                {
                    type Next = &'vir #name<'vir, NextA, NextB>;
                    fn reify<'tcx>(&self, vcx: &'vir crate::VirCtxt<'tcx>, lctx: Curr) -> Self::Next {
                        match self { #(#variants),* }
                    }
                }
                #slice_impl
            }
        }
        _ => unreachable!(),
    })
}
