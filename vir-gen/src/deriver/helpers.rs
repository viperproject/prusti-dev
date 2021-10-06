use syn::parse_quote;

use super::common::DeriveInfo;
use crate::{
    deriver::common::{extract_variant_type, find_variant_struct},
    helpers::{method_name_from_camel, unbox_type},
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
            let variant_type = extract_variant_type(&variant)?;
            let variant_struct = find_variant_struct(&items, variant_type)?;
            let method_name = method_name_from_camel(&variant.ident);
            let variant_ident = &variant.ident;
            let variant_struct_ident = &variant_struct.ident;
            let mut parameters: Vec<syn::FnArg> = Vec::new();
            let mut fields: Vec<syn::FieldValue> = Vec::new();
            for field in &variant_struct.fields {
                let name = field.ident.as_ref().unwrap();
                let parameter_type = unbox_type(&field.ty);
                parameters.push(parse_quote!(
                    #name: #parameter_type
                ));
                if parameter_type == field.ty {
                    fields.push(parse_quote!(
                        #name
                    ));
                } else {
                    fields.push(parse_quote!(
                        #name: Box::new(#name)
                    ));
                }
            }
            let method = parse_quote! {
                pub fn #method_name(#(#parameters),*) -> #enum_ident {
                    #enum_ident::#variant_ident(#variant_struct_ident {
                        #(#fields),*
                    })
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
