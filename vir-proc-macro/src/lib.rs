use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, DeriveInput};

fn is_reify_copy(field: &syn::Field) -> bool {
    field.attrs.iter()
        .filter_map(|attr| match &attr.meta {
            syn::Meta::Path(p) => Some(&p.segments),
            _ => None,
        })
        .any(|segs| segs.len() == 1 && segs[0].ident == "reify_copy")
}

#[proc_macro_derive(Reify, attributes(reify_copy))]
pub fn derive_reify(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = input.ident;
    let slice_impl = quote! {
        impl<'vir, Curr: Copy, NextA, NextB> crate::Reify<'vir, Curr>
            for [&'vir #name<'vir, Curr, ExprGen<'vir, NextA, NextB>>]
        {
            type Next = &'vir [&'vir #name<'vir, NextA, NextB>];
            fn reify(&self, vcx: &'vir crate::VirCtxt<'vir>, lctx: Curr) -> Self::Next {
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
                    if is_reify_copy(field) {
                        None
                    } else {
                        Some(quote! {
                            let #name = self.#name.reify(vcx, lctx);
                        })
                    }
                })
                .collect::<Vec<_>>();
            let fields = named.iter()
                .map(|field| {
                    let name = field.ident.as_ref().unwrap();
                    if is_reify_copy(field) {
                        quote! { #name: self.#name }
                    } else {
                        quote! { #name: #name }
                    }
                })
                .collect::<Vec<_>>();
            quote! {
                impl<'vir, Curr: Copy, NextA, NextB> crate::Reify<'vir, Curr>
                    for &'vir #name<'vir, Curr, ExprGen<'vir, NextA, NextB>>
                {
                    type Next = &'vir #name<'vir, NextA, NextB>;
                    fn reify(&self, vcx: &'vir crate::VirCtxt<'vir>, lctx: Curr) -> Self::Next {
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
                                .filter_map(|(idx, field)| {
                                    if is_reify_copy(field) {
                                        None
                                    } else {
                                        let vbind = &vbinds[idx];
                                        let obind = &obinds[idx];
                                        Some(quote! {
                                            let #obind = #vbind.reify(vcx, lctx);
                                        })
                                    }
                                })
                                .collect::<Vec<_>>();
                            let fields = unnamed.iter()
                                .enumerate()
                                .map(|(idx, field)| {
                                    let vbind = &vbinds[idx];
                                    let obind = &obinds[idx];
                                    if is_reify_copy(field) {
                                        quote! { #vbind }
                                    } else {
                                        quote! { #obind }
                                    }
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
                    for &'vir #name<'vir, Curr, ExprGen<'vir, NextA, NextB>>
                {
                    type Next = &'vir #name<'vir, NextA, NextB>;
                    fn reify(&self, vcx: &'vir crate::VirCtxt<'vir>, lctx: Curr) -> Self::Next {
                        match self { #(#variants),* }
                    }
                }
                #slice_impl
            }
        }
        _ => unreachable!(),
    })
}
