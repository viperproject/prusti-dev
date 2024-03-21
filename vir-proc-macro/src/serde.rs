use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, DeriveInput};
use syn::spanned::Spanned;

use super::reify_kind::ReifyKind;

pub fn derive_serde(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = input.ident;

    // "UnOpGenData"
    let name_str = syn::LitStr::new(name.to_string().as_str(), name.span());

    let ref_impl = quote! {
        impl<'vir> serde::Deserialize<'vir> for &'vir #name<'vir, !, !> {
            fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
            where D:
                serde::Deserializer<'vir>,
            {
                let owned: #name<'vir, !, !> = #name::<'vir, !, !>::deserialize(deserializer)?;
                Ok(crate::with_vcx(|vcx| vcx.alloc(owned)))
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
            // "struct UnOpGenData"
            let expecting = syn::LitStr::new(
                &format!("struct {}", name.to_string().as_str()),
                name.span(),
            );

            // kind, expr
            let field_idents = named.iter()
                .map(|field| field.ident.as_ref().unwrap())
                .collect::<Vec<_>>();

            // 2
            let field_count = field_idents.len();

            // f_kind, f_expr
            let field_idents_f = field_idents.iter()
                .map(|ident| syn::Ident::new(&format!("f_{}", ident.to_string().as_str()), ident.span()))
                .collect::<Vec<_>>();

            let field_allocs = named.iter()
                .zip(field_idents_f.iter())
                .map(|(field, field_ident_f)| {
                    match ReifyKind::of_field(field) {
                        ReifyKind::PassString => quote! {
                            let s: String = seq_val;
                            let #field_ident_f = crate::with_vcx(|vcx| vcx.alloc_str(&s));
                        },
                        ReifyKind::ReifySlice | ReifyKind::PassSlice => quote! {
                            let vec_of_data: Vec<_> = seq_val;
                            let #field_ident_f = crate::with_vcx(|vcx| {
                                let vec_of_refs = vec_of_data.into_iter()
                                    .map(|val| vcx.alloc(val))
                                    .collect::<Vec<_>>();
                                vcx.alloc_slice(&vec_of_refs)
                            });
                        },
                        ReifyKind::ReifyOption => quote! {
                            let opt: Option<_> = seq_val;
                            let #field_ident_f = crate::with_vcx(|vcx| opt.map(|val| vcx.alloc(val)));
                        },
                        ReifyKind::PassOwned => quote! {
                            let #field_ident_f = seq_val;
                        },
                        ReifyKind::PassRef | ReifyKind::ReifyOwned => quote! {
                            let #field_ident_f = crate::with_vcx(|vcx| vcx.alloc(seq_val));
                        },
                    }
                })
                .collect::<Vec<_>>();

            quote! {
                impl<'vir> serde::Serialize for #name<'vir, !, !> {
                    fn serialize<S>(&self, s: S) -> Result<S::Ok, S::Error>
                    where
                        S: serde::Serializer,
                    {
                        use serde::ser::SerializeSeq;
                        let mut state = s.serialize_seq(Some(#field_count))?;
                        #(
                            state.serialize_element(&self.#field_idents)?;
                        )*
                        state.end()
                    }
                }

                impl<'vir> serde::Deserialize<'vir> for #name<'vir, !, !> {
                    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
                    where D:
                        serde::Deserializer<'vir>,
                    {
                        struct DataVisitor<'vir>(std::marker::PhantomData<&'vir ()>);
                        impl<'vir> serde::de::Visitor<'vir> for DataVisitor<'vir> {
                            type Value = #name<'vir, !, !>;

                            fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
                                formatter.write_str(#expecting)
                            }

                            fn visit_seq<A>(mut self, mut seq: A) -> Result<Self::Value, A::Error>
                            where
                                A: serde::de::SeqAccess<'vir>,
                            {
                                #(
                                    let seq_val = seq.next_element()?.unwrap();
                                    #field_allocs
                                )*
                                Ok(#name {
                                    #(#field_idents: #field_idents_f),*
                                })
                            }
                        }

                        deserializer.deserialize_seq(DataVisitor(std::marker::PhantomData))
                    }
                }

                #ref_impl
            }
        }

        syn::Data::Enum(syn::DataEnum {
            variants,
            ..
        }) => {
            // "enum StmtGenData"
            let expecting = syn::LitStr::new(
                &format!("enum {}", name.to_string().as_str()),
                name.span(),
            );

            // LocalDecl, PureAssign, ...
            let variant_idents = variants.iter()
                .map(|variant| &variant.ident)
                .collect::<Vec<_>>();

            // "localdecl", "pureassign", ...
            let variant_strs = variant_idents.iter()
                .map(|ident| syn::LitStr::new(ident.to_string().as_str(), ident.span()))
                .collect::<Vec<_>>();

            let (variant_ser_arms, (variant_deser_arms, variant_visit_arms)): (Vec<_>, (Vec<_>, Vec<_>)) = variants.iter()
                .enumerate()
                .map(|(variant_index, variant)| {
                    let variant_ident = &variant.ident;
                    let variant_str = syn::LitStr::new(variant_ident.to_string().as_str(), variant_ident.span());
                    match &variant.fields {
                        syn::Fields::Unnamed(syn::FieldsUnnamed {
                            unnamed,
                            ..
                        }) => {
                            let variant_fields_pat = (0..unnamed.len())
                                .map(|idx| syn::Ident::new(&format!("f{idx}"), unnamed.span()))
                                .collect::<Vec<_>>();
                            let variant_field_count = unnamed.len();

                            let variant_allocs = unnamed.iter()
                                .map(|field| match ReifyKind::of_field(field) {
                                    ReifyKind::PassString => quote! {
                                        let s: String = seq_val;
                                        crate::with_vcx(|vcx| vcx.alloc_str(&s))
                                    },
                                    ReifyKind::ReifySlice | ReifyKind::PassSlice => quote! {
                                        let vec_of_data: Vec<_> = seq_val;
                                        crate::with_vcx(|vcx| {
                                            let vec_of_refs = vec_of_data.into_iter()
                                                .map(|val| vcx.alloc(val))
                                                .collect::<Vec<_>>();
                                            vcx.alloc_slice(&vec_of_refs)
                                        })
                                    },
                                    ReifyKind::ReifyOption => quote! {
                                        let opt: Option<_> = seq_val;
                                        crate::with_vcx(|vcx| opt.map(|val| vcx.alloc(val)))
                                    },
                                    ReifyKind::PassOwned => quote! {
                                        seq_val
                                    },
                                    ReifyKind::PassRef | ReifyKind::ReifyOwned => quote! {
                                        crate::with_vcx(|vcx| vcx.alloc(seq_val))
                                    },
                                })
                                .collect::<Vec<_>>();

                            (quote! {
                                Self::#variant_ident(#(#variant_fields_pat),*) => {
                                    let mut s = s.serialize_tuple_variant(
                                        #name_str,
                                        #variant_index as u32,
                                        #variant_str,
                                        #variant_field_count,
                                    )?;
                                    #(s.serialize_field(#variant_fields_pat)?;)*
                                    s.end()
                                }
                            }, (quote! {
                                #variant_index => {
                                    #(let #variant_fields_pat = {
                                        let seq_val = data.next_element()?.expect("not enough data in variant");
                                        #variant_allocs
                                    };)*
                                    Ok(#name::#variant_ident(#(#variant_fields_pat),*))
                                }
                            }, quote! {
                                (#variant_index, data) => {
                                    self.0 = Some(#variant_index);
                                    data.tuple_variant(#variant_field_count, self)
                                }
                            }))
                        },
                        syn::Fields::Unit => {
                            (quote! {
                                Self::#variant_ident => s.serialize_unit_variant(
                                    #name_str,
                                    #variant_index as u32,
                                    #variant_str,
                                ),
                            }, (quote! {
                                #variant_index => unreachable!(),
                            }, quote! {
                                (#variant_index, data) => {
                                    data.unit_variant()?;
                                    Ok(#name::#variant_ident)
                                }
                            }))
                        },
                        _ => panic!("VirSerde can only handle tuple and unit variants"),
                    }
                })
                .unzip();

            quote! {
                impl<'vir> serde::Serialize for #name<'vir, !, !> {
                    fn serialize<S>(&self, s: S) -> Result<S::Ok, S::Error>
                    where
                        S: serde::Serializer,
                    {
                        use serde::ser::SerializeTupleVariant;
                        match self {
                            #(#variant_ser_arms)*
                            _ => unreachable!(),
                        }
                    }
                }

                impl<'vir> serde::Deserialize<'vir> for #name<'vir, !, !> {
                    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
                    where
                        D: serde::Deserializer<'vir>,
                    {
                        static VARIANTS: &[&str] = &[ #(#variant_strs),* ];

                        struct DataVisitor<'vir>(Option<usize>, std::marker::PhantomData<&'vir ()>);

                        impl<'vir> serde::de::Visitor<'vir> for DataVisitor<'vir> {
                            type Value = #name<'vir, !, !>;

                            fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
                                formatter.write_str(#expecting)
                            }

                            fn visit_seq<A>(mut self, mut data: A) -> Result<Self::Value, A::Error>
                            where
                                A: serde::de::SeqAccess<'vir>,
                            {
                                match self.0.expect("unknown enum variant") {
                                    #(#variant_deser_arms)*
                                    _ => unreachable!(),
                                }
                            }

                            fn visit_enum<A>(mut self, mut data: A) -> Result<Self::Value, A::Error>
                            where
                                A: serde::de::EnumAccess<'vir>,
                            {
                                use serde::de::VariantAccess;
                                match data.variant()? {
                                    #(#variant_visit_arms)*
                                    _ => todo!(),
                                }
                            }
                        }

                        deserializer.deserialize_enum(#name_str, VARIANTS, DataVisitor(None, std::marker::PhantomData))
                    }
                }

                #ref_impl
            }
        }

        _ => unreachable!(),
    })
}
