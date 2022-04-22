//! Common code for spec-rewriting

use std::borrow::BorrowMut;
use syn::{parse_quote, spanned::Spanned};
use uuid::Uuid;

/// Trait which signals that the corresponding syn item contains generics
pub(crate) trait HasGenerics {
    fn get_generics(&self) -> &syn::Generics;
}

impl HasGenerics for syn::ItemTrait {
    fn get_generics(&self) -> &syn::Generics {
        &self.generics
    }
}

impl HasGenerics for syn::ItemStruct {
    fn get_generics(&self) -> &syn::Generics {
        &self.generics
    }
}

impl HasGenerics for syn::ItemImpl {
    fn get_generics(&self) -> &syn::Generics {
        &self.generics
    }
}

/// Add `PhantomData` markers for each type parameter to silence errors
/// about unused type parameters. Works for structs with named or unnamed fields
/// Given
/// ```text
/// struct Foo<A,B> {
///     // ... fields ...
/// }
/// ```
/// Result
/// ```text
/// struct Foo<A,B> {
///     // ... fields ...
///     ::core::marker::PhantomData<A>,
///     ::core::marker::PhantomData<B>
/// }
/// ```
pub fn add_phantom_data_for_generic_params(item_struct: &mut syn::ItemStruct) {
    let mut fields = vec![];

    let need_named_fields = matches!(item_struct.fields, syn::Fields::Named(_));

    let generate_field_ident = |span: proc_macro2::Span| {
        if need_named_fields {
            let uuid = Uuid::new_v4().to_simple();
            let field_name = format!("prusti_injected_phantom_field_{}", uuid);
            return Some(syn::Ident::new(field_name.as_str(), span));
        }
        None
    };

    for generic_param in item_struct.generics.params.iter() {
        let ty: Option<syn::Type> = match generic_param {
            syn::GenericParam::Type(type_param) => {
                let ty_ident = &type_param.ident;
                let ty: syn::Type = parse_quote!(::core::marker::PhantomData<#ty_ident>);
                Some(ty)
            }
            syn::GenericParam::Lifetime(lt_def) => {
                let lt = &lt_def.lifetime;
                let ty: syn::Type = parse_quote!(&#lt ::core::marker::PhantomData<()>);
                Some(ty)
            }
            _ => None,
        };

        if ty.is_none() {
            continue;
        }
        let ty = ty.unwrap();

        let field = syn::Field {
            vis: syn::Visibility::Inherited,
            attrs: Vec::default(),
            ident: generate_field_ident(generic_param.span()),
            colon_token: None,
            ty,
        };
        fields.push(field);
    }

    if matches!(item_struct.fields, syn::Fields::Unit) {
        let field_types: Vec<syn::Type> = fields.into_iter().map(|field| field.ty).collect();
        let fields_unnamed: syn::FieldsUnnamed = parse_quote!((#(#field_types),*));
        item_struct.fields = syn::Fields::Unnamed(fields_unnamed);
    } else {
        match item_struct.fields.borrow_mut() {
            syn::Fields::Named(named_fields) => {
                named_fields.named.extend(fields);
            }
            syn::Fields::Unnamed(unnamed_fields) => {
                unnamed_fields.unnamed.extend(fields);
            }
            syn::Fields::Unit => unreachable!(),
        };
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    mod phantom_data {
        use super::*;
        use quote::ToTokens;

        #[test]
        fn phantom_data_for_struct_with_named_fields() {
            let mut item_struct: syn::ItemStruct = parse_quote!(
                struct Foo<A, B, C, 'a> {
                    fld1: A,
                }
            );

            add_phantom_data_for_generic_params(&mut item_struct);

            assert_eq!(5, item_struct.fields.len());
            assert!(matches!(item_struct.fields, syn::Fields::Named(_)));
            let mut fields_iter = item_struct.fields.iter();
            let field = fields_iter.next().unwrap();
            assert_eq!("fld1", field.ident.as_ref().unwrap().to_string());
            assert_eq!("A", field.ty.to_token_stream().to_string());
            let field = fields_iter.next().unwrap();
            assert!(field.ident.as_ref().is_some());
            assert_phantom_type_for("A", field);
            let field = fields_iter.next().unwrap();
            assert!(field.ident.as_ref().is_some());
            assert_phantom_type_for("B", field);
            let field = fields_iter.next().unwrap();
            assert!(field.ident.as_ref().is_some());
            assert_phantom_type_for("C", field);
            let field = fields_iter.next().unwrap();
            assert!(field.ident.as_ref().is_some());
            assert_phantom_ref_for("'a", field);
            assert!(fields_iter.next().is_none());
        }

        #[test]
        fn phantom_data_for_struct_with_unnamed_fields() {
            let mut item_struct: syn::ItemStruct = parse_quote!(
                struct Foo<A, B, C, 'a>(A);
            );

            add_phantom_data_for_generic_params(&mut item_struct);

            assert_eq!(5, item_struct.fields.len());
            assert!(matches!(item_struct.fields, syn::Fields::Unnamed(_)));
            let mut fields_iter = item_struct.fields.iter();
            let field = fields_iter.next().unwrap();
            assert!(field.ident.is_none());
            assert_eq!("A", field.ty.to_token_stream().to_string());
            let field = fields_iter.next().unwrap();
            assert!(field.ident.is_none());
            assert_phantom_type_for("A", field);
            let field = fields_iter.next().unwrap();
            assert!(field.ident.is_none());
            assert_phantom_type_for("B", field);
            let field = fields_iter.next().unwrap();
            assert!(field.ident.is_none());
            assert_phantom_type_for("C", field);
            let field = fields_iter.next().unwrap();
            assert!(field.ident.is_none());
            assert_phantom_ref_for("'a", field);
            assert!(fields_iter.next().is_none());
        }

        #[test]
        fn phantom_data_for_unit_struct() {
            let mut item_struct: syn::ItemStruct = parse_quote!(
                struct Foo<A, 'a>;
            );

            add_phantom_data_for_generic_params(&mut item_struct);

            assert_eq!(2, item_struct.fields.len());
            assert!(matches!(item_struct.fields, syn::Fields::Unnamed(_)));
            let mut fields_iter = item_struct.fields.iter();
            let field = fields_iter.next().unwrap();
            assert!(field.ident.is_none());
            assert_phantom_type_for("A", field);
            let field = fields_iter.next().unwrap();
            assert!(field.ident.is_none());
            assert_phantom_ref_for("'a", field);
            assert!(fields_iter.next().is_none());
        }

        fn assert_phantom_type_for(ty: &str, actual_field: &syn::Field) {
            match &actual_field.ty {
                syn::Type::Path(type_path) => {
                    assert_eq!(
                        format!("::core::marker::PhantomData<{}>", ty),
                        type_path
                            .path
                            .to_token_stream()
                            .to_string()
                            .replace(' ', "")
                    );
                }
                _ => panic!(),
            }
        }

        fn assert_phantom_ref_for(expected_lifetime: &str, actual_field: &syn::Field) {
            match &actual_field.ty {
                syn::Type::Reference(type_ref) => {
                    let actual_lifetime = type_ref.lifetime.as_ref().expect("Expected lifetime");
                    assert_eq!(expected_lifetime, actual_lifetime.to_string().trim());

                    let ty = type_ref.elem.as_ref();
                    assert_eq!(
                        "::core::marker::PhantomData<()>",
                        ty.to_token_stream().to_string().replace(' ', "")
                    );
                }
                _ => panic!(),
            }
        }
    }
}
