use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, DeriveInput};
use syn::spanned::Spanned;

pub fn derive_hash(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = input.ident;

    TokenStream::from(match input.data {
        syn::Data::Struct(syn::DataStruct {
            fields: syn::Fields::Named(syn::FieldsNamed {
                named,
                ..
            }),
            ..
        }) => {
            let field_idents = named.iter()
                .map(|field| field.ident.as_ref().unwrap())
                .collect::<Vec<_>>();

            quote! {
                impl<'vir> std::hash::Hash for #name<'vir, !, !> {
                    fn hash<H>(&self, state: &mut H)
                    where
                        H: std::hash::Hasher,
                    {
                        use std::hash::Hash;
                        #(self.#field_idents.hash(state);)*
                    }
                }
            }
        }

        syn::Data::Enum(syn::DataEnum {
            variants,
            ..
        }) => {
            let variant_hash_arms = variants.iter()
                .enumerate()
                .map(|(variant_index, variant)| {
                    let variant_ident = &variant.ident;
                    match &variant.fields {
                        syn::Fields::Unnamed(syn::FieldsUnnamed {
                            unnamed,
                            ..
                        }) => {
                            let variant_fields_pat = (0..unnamed.len())
                                .map(|idx| syn::Ident::new(&format!("f{idx}"), unnamed.span()))
                                .collect::<Vec<_>>();

                            quote! {
                                Self::#variant_ident(#(#variant_fields_pat),*) => {
                                    state.write_u8(#variant_index as u8);
                                    #(#variant_fields_pat.hash(state);)*
                                }
                            }
                        },
                        syn::Fields::Unit => quote! {
                            Self::#variant_ident => state.write_u8(#variant_index as u8),
                        },
                        _ => panic!("VirHash can only handle tuple and unit variants"),
                    }
                })
                .collect::<Vec<_>>();

            quote! {
                impl<'vir> std::hash::Hash for #name<'vir, !, !> {
                    fn hash<H>(&self, state: &mut H)
                    where
                        H: std::hash::Hasher,
                    {
                        use std::hash::Hash;
                        match self {
                            #(#variant_hash_arms)*
                            _ => unreachable!(),
                        }
                    }
                }
            }
        }

        _ => unreachable!(),
    })
}
