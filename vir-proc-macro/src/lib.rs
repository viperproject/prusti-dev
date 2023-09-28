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
        impl<'vir, Curr: Copy, NextA, NextB> crate::Reify<'vir, Curr, NextA, NextB>
            for [&'vir #name<'vir, Curr, ExprGen<'vir, NextA, NextB>>]
        {
            type Next = &'vir [&'vir #name<'vir, NextA, NextB>];
            fn reify(&self, vcx: &'vir crate::VirCtxt<'vir>, lctx: Curr) -> Self::Next {
                self.reify_deep(vcx, lctx)
                    .unwrap_or_else(|| unsafe { std::mem::transmute(self) })
            }
            fn reify_deep(&self, vcx: &'vir crate::VirCtxt<'vir>, lctx: Curr) -> Option<Self::Next> {
                let mut any_change = false;
                let mut vals = self.iter()
                    .map(|elem| {
                        let elem = elem.reify_deep(vcx, lctx);
                        any_change |= elem.is_some();
                        elem
                    })
                    .collect::<Vec<Option<_>>>();
                if !any_change {
                    return None;
                };
                Some(vcx.alloc_slice(&vals.into_iter()
                    .map(|elem| elem.unwrap_or_else(|| unsafe { std::mem::transmute(elem) }))
                    .collect::<Vec<_>>()))
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
                            let #name = self.#name.reify_deep(vcx, lctx);
                            any_change |= #name.is_some();
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
                        quote! { #name: #name
                            .unwrap_or_else(|| unsafe { std::mem::transmute(self.#name) }) }
                    }
                })
                .collect::<Vec<_>>();
            quote! {
                impl<'vir, Curr: Copy, NextA, NextB> crate::Reify<'vir, Curr, NextA, NextB>
                    for &'vir #name<'vir, Curr, ExprGen<'vir, NextA, NextB>>
                {
                    type Next = &'vir #name<'vir, NextA, NextB>;
                    fn reify(&self, vcx: &'vir crate::VirCtxt<'vir>, lctx: Curr) -> Self::Next {
                        self.reify_deep(vcx, lctx)
                            .unwrap_or_else(|| unsafe { std::mem::transmute(self) })
                    }
                    fn reify_deep(&self, vcx: &'vir crate::VirCtxt<'vir>, lctx: Curr) -> Option<Self::Next> {
                        let mut any_change = false;
                        #(#compute_fields)*
                        if !any_change {
                            return None;
                        }
                        Some(vcx.alloc(#name { #(#fields),* }))
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
                                            let #obind = #vbind.reify_deep(vcx, lctx);
                                            any_change |= #obind.is_some();
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
                                        quote! { #obind
                                            .unwrap_or_else(|| unsafe { std::mem::transmute(#vbind) }) }
                                    }
                                })
                                .collect::<Vec<_>>();
                            quote! {
                                #name::#variant_name(#(#vbinds),*) => {
                                    let mut any_change = false;
                                    #(#compute_fields)*
                                    if !any_change {
                                        return None;
                                    }
                                    vcx.alloc(#name::#variant_name(#(#fields),*))
                                }
                            }
                        },
                        syn::Fields::Unit => quote! {
                            #name::#variant_name => return None
                        },
                        _ => unreachable!(),
                    }
                })
                .collect::<Vec<_>>();
            quote! {
                impl<'vir, Curr: Copy, NextA, NextB> crate::Reify<'vir, Curr, NextA, NextB>
                    for &'vir #name<'vir, Curr, ExprGen<'vir, NextA, NextB>>
                {
                    type Next = &'vir #name<'vir, NextA, NextB>;
                    fn reify(&self, vcx: &'vir crate::VirCtxt<'vir>, lctx: Curr) -> Self::Next {
                        self.reify_deep(vcx, lctx)
                            .unwrap_or_else(|| unsafe { std::mem::transmute(self) })
                    }
                    fn reify_deep(&self, vcx: &'vir crate::VirCtxt<'vir>, lctx: Curr) -> Option<Self::Next> {
                        Some(match self { #(#variants),* })
                    }
                }
                #slice_impl
            }
        }
        _ => unreachable!(),
    })
}
