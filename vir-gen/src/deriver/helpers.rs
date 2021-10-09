use syn::parse_quote;

use super::common::DeriveInfo;
use crate::{
    deriver::common::{extract_variant_type, find_variant_enum, find_variant_struct},
    helpers::{append_ident, method_name_from_camel, unbox_type},
};

pub(super) fn derive(
    mut items: Vec<syn::Item>,
    helpers_to_derive: Vec<DeriveInfo>,
) -> Result<Vec<syn::Item>, syn::Error> {
    for DeriveInfo {
        enum_ident,
        variants,
    } in helpers_to_derive
    {
        let mut helpers: Vec<syn::ImplItem> = Vec::new();
        for variant in variants {
            let method_name = method_name_from_camel(&variant.ident);
            let variant_ident = &variant.ident;
            let method = if let Some(variant_type) = extract_variant_type(&variant)? {
                if let Some(variant_enum) = find_variant_enum(&items, variant_type) {
                    let variant_enum_ident = &variant_enum.ident;
                    parse_quote! {
                        pub fn #method_name(arg: #variant_enum_ident) -> #enum_ident {
                            #enum_ident::#variant_ident(arg)
                        }
                    }
                } else {
                    let variant_struct = find_variant_struct(&items, variant_type)?;
                    let variant_struct_ident = &variant_struct.ident;
                    let mut parameters: Vec<syn::FnArg> = Vec::new();
                    let mut parameters_no_pos: Vec<syn::FnArg> = Vec::new();
                    let mut fields: Vec<syn::FieldValue> = Vec::new();
                    let mut fields_no_pos: Vec<syn::FieldValue> = Vec::new();
                    for field in &variant_struct.fields {
                        let name = field.ident.as_ref().unwrap();
                        let parameter_type = unbox_type(&field.ty);
                        let parameter: syn::FnArg = parse_quote!(
                            #name: #parameter_type
                        );
                        let field: syn::FieldValue = if parameter_type == field.ty {
                            parse_quote!(
                                #name
                            )
                        } else {
                            parse_quote!(
                                #name: Box::new(#name)
                            )
                        };
                        if name != "position" {
                            parameters_no_pos.push(parameter.clone());
                            fields_no_pos.push(field.clone());
                        }
                        parameters.push(parameter);
                        fields.push(field);
                    }
                    if parameters.len() != parameters_no_pos.len() {
                        let new_method_name = append_ident(&method_name, "_no_pos");
                        let additional_method = parse_quote! {
                            pub fn #new_method_name(#(#parameters_no_pos),*) -> #enum_ident {
                                #enum_ident::#variant_ident(#variant_struct_ident {
                                    position: Default::default(),
                                    #(#fields_no_pos),*
                                })
                            }
                        };
                        helpers.push(additional_method);
                    }
                    parse_quote! {
                        pub fn #method_name(#(#parameters),*) -> #enum_ident {
                            #enum_ident::#variant_ident(#variant_struct_ident {
                                #(#fields),*
                            })
                        }
                    }
                }
            } else {
                parse_quote! {
                    pub fn #method_name() -> #enum_ident {
                        #enum_ident::#variant_ident
                    }
                }
            };
            helpers.push(method);
        }
        let enum_impl = parse_quote! {
            impl #enum_ident {
                #(#helpers)*
            }
        };
        items.push(enum_impl);
    }
    Ok(items)
}
