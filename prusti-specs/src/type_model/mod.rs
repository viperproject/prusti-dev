//! Processes `#[model]` attributed types
//! Usage documentation can be found in the corresponding macro definition

use proc_macro2::{Ident, TokenStream};
use quote::ToTokens;
use syn::parse_quote;
use syn::spanned::Spanned;
use super::parse_quote_spanned;

// TODO: GENERICS
// Generics should be marked with attributes to be "concrete" or "generic"
// This logic is already existing for extern trait specs -> maybe want to extract common code.

// TODO: Where to put ToModel trait?

// TODO: rustfmt

pub fn rewrite(item_struct: syn::ItemStruct) -> syn::Result<TokenStream> {
    let res = rewrite_internal(item_struct);
    match res {
        Ok(result) => Ok(result.into_token_stream()),
        Err(err) => Err(err.into())
    }
}

type TypeModelGenerationResult<R> = Result<R, TypeModelGenerationError>;

fn rewrite_internal(item_struct: syn::ItemStruct) -> TypeModelGenerationResult<TypeModel> {
    let model_struct = create_model_struct(&item_struct)?;
    let model_impl = create_model_impl(&item_struct, &model_struct)?;

    Ok(TypeModel {
        model_struct,
        model_impl,
    })
}

fn create_model_struct(item_struct: &syn::ItemStruct) -> TypeModelGenerationResult<syn::ItemStruct> {
    if item_struct.fields.len() == 0 {
        return Err(TypeModelGenerationError::MissingStructFields(item_struct.span()).into());
    }

    let ident = &item_struct.ident;

    // Create model
    let model_struct_ident = Ident::new(format!("Prusti{}Model", ident).as_str(), item_struct.ident.span()); // TODO: randomize name! Maybe use name generator?
    let mut model_struct: syn::ItemStruct = parse_quote_spanned! {item_struct.span()=>
        #[derive(Copy, Clone)]
        struct #model_struct_ident {}
    };
    model_struct.fields = item_struct.fields.clone();

    Ok(model_struct)
}

fn create_model_impl(item_struct: &syn::ItemStruct, generated_model_struct: &syn::ItemStruct) -> TypeModelGenerationResult<syn::ItemImpl> {
    let ident = &item_struct.ident;
    let model_struct_ident = &generated_model_struct.ident;
    let mut rewritten_generics: Vec<syn::GenericParam> = Vec::new();
    for param in &item_struct.generics.params {
        match param {
            syn::GenericParam::Lifetime(_) => rewritten_generics.push(parse_quote!('_)),
            syn::GenericParam::Type(type_param) => rewritten_generics.push(syn::GenericParam::Type(type_param.clone())),
            syn::GenericParam::Const(const_param) => return Err(TypeModelGenerationError::ConstParamDisallowed(const_param.span()))
        }
    }

    let impl_path: syn::Path = parse_quote!(
        #ident < #(#rewritten_generics),* >
    );

    // Create impl for provided trait
    Ok(parse_quote_spanned! {item_struct.span()=>
        impl ToModel<#model_struct_ident> for #impl_path {
            #[trusted]
            #[pure]
            fn model(&self) -> #model_struct_ident {
                unimplemented!();
            }
        }
    })
}

/// Errors that can happen during model generation.
/// These are mostly wrong usages of the macro by the user.
#[derive(Debug)]
enum TypeModelGenerationError {
    MissingStructFields(proc_macro2::Span),
    ConstParamDisallowed(proc_macro2::Span),
}

impl std::convert::From<TypeModelGenerationError> for syn::Error {
    fn from(err: TypeModelGenerationError) -> Self {
        match err {
            TypeModelGenerationError::MissingStructFields(span) => syn::Error::new(span, "Missing fields in model"),
            TypeModelGenerationError::ConstParamDisallowed(span) => syn::Error::new(span, "Const generics are disallowed for models"),
        }
    }
}

/// Type to represent generated code during expansion of the `#[model]` macro
struct TypeModel {
    model_struct: syn::ItemStruct,
    model_impl: syn::ItemImpl,
}

impl ToTokens for TypeModel {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.model_struct.to_tokens(tokens);
        self.model_impl.to_tokens(tokens);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rewritten_model_to_tokens() {
        let model_struct: syn::ItemStruct = parse_quote!(struct Foo {});
        let trait_impl: syn::ItemImpl = parse_quote!(impl ToModel for Foo {});

        let rewritten_model = TypeModel {
            model_struct: model_struct.clone(),
            model_impl: trait_impl.clone(),
        };
        let actual_ts = rewritten_model.into_token_stream();

        let mut expected_ts = TokenStream::new();
        model_struct.to_tokens(&mut expected_ts);
        trait_impl.to_tokens(&mut expected_ts);

        assert_eq!(expected_ts.to_string(), actual_ts.to_string());
    }

    #[test]
    fn err_when_no_fields() {
        let input = parse_quote!(struct Foo {});
        let result = rewrite_internal(input);
        assert!(matches!(result, Err(TypeModelGenerationError::MissingStructFields(_))));
    }

    #[test]
    fn ok_generates_model_struct_def_with_named_fields() {
        let input = syn::parse_quote!(
            struct Foo {
                fld1: usize,
                fld2: i32,
            }
        );

        let model = expect_ok(rewrite_internal(input));

        let expected: syn::ItemStruct = syn::parse_quote!(
            #[derive(Copy, Clone)]
            struct PrustiFooModel {
                fld1: usize,
                fld2: i32,
            }
        );
        assert_eq_tokenizable(expected, model.model_struct);
    }

    #[test]
    fn ok_generates_model_struct_def_with_unnamed_fields() {
        let input = parse_quote!(struct Foo(i32,u32,usize););

        let model = expect_ok(rewrite_internal(input));

        let expected: syn::ItemStruct = parse_quote!(
            #[derive(Copy, Clone)]
            struct PrustiFooModel(i32,u32,usize);
        );
        assert_eq_tokenizable(expected, model.model_struct);
    }

    #[test]
    fn ok_generates_impl_for_to_model_trait() {
        let input = parse_quote!(struct Foo(i32,u32,usize););
        let model = expect_ok(rewrite_internal(input));

        let model_ident = &model.model_struct.ident;
        let expected: syn::ItemImpl = parse_quote!(
            impl ToModel<#model_ident> for Foo <> {
                #[trusted]
                #[pure]
                fn model(&self) -> #model_ident {
                    unimplemented!();
                }
            }
        );

        assert_eq_tokenizable(expected, model.model_impl);
    }

    #[test]
    fn ok_uses_inferred_lifetime() {
        let input: syn::ItemStruct = parse_quote!(struct Foo<'a, 'b>(i32,u32,usize););
        let model = expect_ok(rewrite_internal(input));
        let expected_struct: syn::ItemStruct = parse_quote!(
            #[derive(Copy, Clone)]
            struct PrustiFooModel(i32,u32,usize);
        );
        let expected_impl: syn::ItemImpl = parse_quote!(
            impl ToModel<PrustiFooModel> for Foo<'_, '_> {
                #[trusted]
                #[pure]
                fn model(&self) -> PrustiFooModel {
                    unimplemented!();
                }
            }
        );

        assert_eq_tokenizable(expected_struct, model.model_struct);
        assert_eq_tokenizable(expected_impl, model.model_impl);
    }

    #[test]
    fn ok_uses_defined_lifetime() {
        let input: syn::ItemStruct = parse_quote!(struct Foo<i32, T>(i32,u32,usize););
        let model = expect_ok(rewrite_internal(input));
        let expected_struct: syn::ItemStruct = parse_quote!(
            #[derive(Copy, Clone)]
            struct PrustiFooModel(i32,u32,usize);
        );
        let expected_impl: syn::ItemImpl = parse_quote!(
            impl ToModel<PrustiFooModel> for Foo<i32, T> {
                #[trusted]
                #[pure]
                fn model(&self) -> PrustiFooModel {
                    unimplemented!();
                }
            }
        );

        assert_eq_tokenizable(expected_struct, model.model_struct);
        assert_eq_tokenizable(expected_impl, model.model_impl);
    }

    #[test]
    fn err_const_generics_disallowed() {
        let input: syn::ItemStruct = parse_quote!(struct Foo<const PAR: i32>(i32,u32,usize););
        let result = rewrite_internal(input);
        assert!(matches!(result, Err(TypeModelGenerationError::ConstParamDisallowed(_))));
    }

    fn expect_ok(result: Result<TypeModel, TypeModelGenerationError>) -> TypeModel {
        result.expect("Expected Ok result")
    }

    fn assert_eq_tokenizable<T: ToTokens, U: ToTokens>(arg1: T, arg2: U) {
        assert_eq!(arg1.into_token_stream().to_string(), arg2.into_token_stream().to_string());
    }
}