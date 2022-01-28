//! Processes `#[model]` attributed types.
//!
//! Usage documentation can be found in the corresponding macro definition.
//!
//! Given a `#[model]` attributed type `T`, this logic creates the following three items:
//! * A struct `M` which holds the model's fields
//! * A trait which provides a `model` method to be used in specifications
//! * An implementation of the aforementioned trait for `T`.
//!   The implementation is `unimplemented!()`, `#[pure]` and `#[trusted]`
//!
//! The model struct `M` must be copyable.
//!
//! # Note
//! This macro always generates a trait with a `model` method on the fly for every modelled type.
//! With this design, one can even model external types which are not present in the local crate.

use super::parse_quote_spanned;
use proc_macro2::{Ident, TokenStream};
use quote::ToTokens;
use syn::{parse_quote, spanned::Spanned};

/// See module level documentation
pub fn rewrite(item_struct: syn::ItemStruct) -> syn::Result<TokenStream> {
    let res = rewrite_internal(item_struct);
    match res {
        Ok(result) => Ok(result.into_token_stream()),
        Err(err) => Err(err.into()),
    }
}

type TypeModelGenerationResult<R> = Result<R, TypeModelGenerationError>;

fn rewrite_internal(item_struct: syn::ItemStruct) -> TypeModelGenerationResult<TypeModel> {
    let idents = GeneratedIdents::generate(&item_struct);
    let model_struct = create_model_struct(&item_struct, &idents)?;
    let to_model_trait = create_to_model_trait(&item_struct, &model_struct, &idents);
    let model_impl = create_model_impl(&item_struct, &model_struct, &to_model_trait)?;

    Ok(TypeModel {
        model_struct,
        model_impl,
        to_model_trait,
    })
}

fn create_model_struct(
    item_struct: &syn::ItemStruct,
    idents: &GeneratedIdents,
) -> TypeModelGenerationResult<syn::ItemStruct> {
    if item_struct.fields.is_empty() {
        return Err(TypeModelGenerationError::MissingStructFields(
            item_struct.span(),
        ));
    }

    let model_struct_ident = &idents.model_struct_ident;
    let mut model_struct: syn::ItemStruct = parse_quote_spanned! {item_struct.span()=>
        #[derive(Copy, Clone)]
        struct #model_struct_ident {}
    };
    model_struct.fields = item_struct.fields.clone();

    Ok(model_struct)
}

fn create_to_model_trait(
    item_struct: &syn::ItemStruct,
    model_struct: &syn::ItemStruct,
    idents: &GeneratedIdents,
) -> syn::ItemTrait {
    let ident = &model_struct.ident;

    let to_model_trait_ident = &idents.to_model_trait_ident;
    parse_quote_spanned! {item_struct.span()=>
        trait #to_model_trait_ident {
            #[trusted]
            #[pure]
            #[prusti::model_generator]
            fn model(&self) -> #ident { unimplemented!() }
        }
    }
}

fn create_model_impl(
    item_struct: &syn::ItemStruct,
    generated_model_struct: &syn::ItemStruct,
    to_model_trait: &syn::ItemTrait,
) -> TypeModelGenerationResult<syn::ItemImpl> {
    let ident = &item_struct.ident;
    let model_struct_ident = &generated_model_struct.ident;
    let mut rewritten_generics: Vec<syn::GenericParam> = Vec::new();
    for param in &item_struct.generics.params {
        match param {
            syn::GenericParam::Lifetime(_) => rewritten_generics.push(parse_quote!('_)),
            syn::GenericParam::Type(type_param) => {
                rewritten_generics.push(syn::GenericParam::Type(type_param.clone()))
            }
            syn::GenericParam::Const(const_param) => {
                return Err(TypeModelGenerationError::ConstParamDisallowed(
                    const_param.span(),
                ))
            }
        }
    }

    let impl_path: syn::Path = parse_quote!(
        #ident < #(#rewritten_generics),* >
    );

    // Create impl for provided trait
    let to_model_trait_ident = &to_model_trait.ident;
    Ok(parse_quote_spanned! {item_struct.span()=>
        impl #to_model_trait_ident for #impl_path {
            #[trusted]
            #[pure]
            #[prusti::model_generator]
            fn model(&self) -> #model_struct_ident {
                unimplemented!("Models can only be used in specifications")
            }
        }
    })
}

/// [syn::Ident]s which are used for the generated items
struct GeneratedIdents {
    model_struct_ident: syn::Ident,
    to_model_trait_ident: syn::Ident,
}

impl GeneratedIdents {
    fn generate(item_struct: &syn::ItemStruct) -> Self {
        let mut name = item_struct.ident.to_string();

        for param in item_struct.generics.params.iter() {
            if let syn::GenericParam::Type(ty_param) = param {
                name.push_str(ty_param.ident.to_string().as_str());
            }
        }

        GeneratedIdents {
            model_struct_ident: Ident::new(
                format!("Prusti{}Model", name).as_str(),
                item_struct.ident.span(),
            ),
            to_model_trait_ident: Ident::new(
                format!("Prusti{}ToModel", name).as_str(),
                item_struct.ident.span(),
            ),
        }
    }
}

/// Errors that can happen during model generation.
/// These are mostly wrong usages of the macro by the user.
#[derive(Debug)]
enum TypeModelGenerationError {
    /// Thrown when the model contains no fields
    MissingStructFields(proc_macro2::Span),

    /// Thrown when using a const type param in the model
    ConstParamDisallowed(proc_macro2::Span),
}

impl std::convert::From<TypeModelGenerationError> for syn::Error {
    fn from(err: TypeModelGenerationError) -> Self {
        match err {
            TypeModelGenerationError::MissingStructFields(span) => {
                syn::Error::new(span, "Missing fields in model")
            }
            TypeModelGenerationError::ConstParamDisallowed(span) => {
                syn::Error::new(span, "Const generics are disallowed for models")
            }
        }
    }
}

/// Type to represent generated code during expansion of the `#[model]` macro
struct TypeModel {
    /// The struct which represents the model
    model_struct: syn::ItemStruct,

    /// A trait which will be implemented on the modelled type
    /// to return the [TypeModel::model_struct]
    to_model_trait: syn::ItemTrait,

    /// The implementation of the [TypeModel::model_trait] on the modelled type.
    model_impl: syn::ItemImpl,
}

impl ToTokens for TypeModel {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.to_model_trait.to_tokens(tokens);
        self.model_struct.to_tokens(tokens);
        self.model_impl.to_tokens(tokens);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rewritten_model_to_tokens() {
        let to_model_trait: syn::ItemTrait = parse_quote!(
            trait PrustiFooToModel {}
        );
        let model_struct: syn::ItemStruct = parse_quote!(
            struct Foo {}
        );
        let trait_impl: syn::ItemImpl = parse_quote!(impl ToModel for Foo {});

        let rewritten_model = TypeModel {
            to_model_trait: to_model_trait.clone(),
            model_struct: model_struct.clone(),
            model_impl: trait_impl.clone(),
        };
        let actual_ts = rewritten_model.into_token_stream();

        let mut expected_ts = TokenStream::new();
        to_model_trait.to_tokens(&mut expected_ts);
        model_struct.to_tokens(&mut expected_ts);
        trait_impl.to_tokens(&mut expected_ts);

        assert_eq!(expected_ts.to_string(), actual_ts.to_string());
    }

    #[test]
    fn err_when_no_fields() {
        let input = parse_quote!(
            struct Foo {}
        );
        let result = rewrite_internal(input);
        assert!(matches!(
            result,
            Err(TypeModelGenerationError::MissingStructFields(_))
        ));
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
        let input = parse_quote!(
            struct Foo(i32, u32, usize);
        );

        let model = expect_ok(rewrite_internal(input));

        let expected: syn::ItemStruct = parse_quote!(
            #[derive(Copy, Clone)]
            struct PrustiFooModel(i32, u32, usize);
        );
        assert_eq_tokenizable(expected, model.model_struct);
    }

    #[test]
    fn ok_generates_impl_for_to_model_trait() {
        let input = parse_quote!(
            struct Foo(i32, u32, usize);
        );
        let model = expect_ok(rewrite_internal(input));

        let model_ident = &model.model_struct.ident;
        let expected: syn::ItemImpl = parse_quote!(
            impl PrustiFooToModel for Foo <> {
                #[trusted]
                #[pure]
                #[prusti::model_generator]
                fn model(&self) -> #model_ident {
                    unimplemented!("Models can only be used in specifications")
                }
            }
        );

        assert_eq_tokenizable(expected, model.model_impl);
    }

    #[test]
    fn ok_uses_inferred_lifetime() {
        let input: syn::ItemStruct = parse_quote!(
            struct Foo<'a, 'b>(i32, u32, usize);
        );
        let model = expect_ok(rewrite_internal(input));
        let expected_struct: syn::ItemStruct = parse_quote!(
            #[derive(Copy, Clone)]
            struct PrustiFooModel(i32, u32, usize);
        );
        let expected_impl: syn::ItemImpl = parse_quote!(
            impl PrustiFooToModel for Foo<'_, '_> {
                #[trusted]
                #[pure]
                #[prusti::model_generator]
                fn model(&self) -> PrustiFooModel {
                    unimplemented!("Models can only be used in specifications")
                }
            }
        );

        assert_eq_tokenizable(expected_struct, model.model_struct);
        assert_eq_tokenizable(expected_impl, model.model_impl);
    }

    #[test]
    fn ok_uses_defined_lifetime() {
        let input: syn::ItemStruct = parse_quote!(
            struct Foo<i32, T>(i32, u32, usize);
        );
        let model = expect_ok(rewrite_internal(input));
        let expected_struct: syn::ItemStruct = parse_quote!(
            #[derive(Copy, Clone)]
            struct PrustiFooi32TModel(i32, u32, usize);
        );
        let expected_impl: syn::ItemImpl = parse_quote!(
            impl PrustiFooi32TToModel for Foo<i32, T> {
                #[trusted]
                #[pure]
                #[prusti::model_generator]
                fn model(&self) -> PrustiFooi32TModel {
                    unimplemented!("Models can only be used in specifications")
                }
            }
        );

        assert_eq_tokenizable(model.model_struct, expected_struct);
        assert_eq_tokenizable(model.model_impl, expected_impl);
    }

    #[test]
    fn ok_defines_to_model_trait() {
        let input: syn::ItemStruct = parse_quote!(
            struct Foo(i32, u32, usize);
        );

        let model = expect_ok(rewrite_internal(input));
        let actual = model.to_model_trait;

        let expected: syn::ItemTrait = parse_quote!(
            trait PrustiFooToModel {
                #[trusted]
                #[pure]
                #[prusti::model_generator]
                fn model(&self) -> PrustiFooModel {
                    unimplemented!()
                }
            }
        );

        assert_eq_tokenizable(actual, expected);
    }

    #[test]
    fn err_const_generics_disallowed() {
        let input: syn::ItemStruct = parse_quote!(
            struct Foo<const PAR: i32>(i32, u32, usize);
        );
        let result = rewrite_internal(input);
        assert!(matches!(
            result,
            Err(TypeModelGenerationError::ConstParamDisallowed(_))
        ));
    }

    fn expect_ok(result: Result<TypeModel, TypeModelGenerationError>) -> TypeModel {
        result.expect("Expected Ok result")
    }

    fn assert_eq_tokenizable<T: ToTokens, U: ToTokens>(actual: T, expected: U) {
        assert_eq!(
            actual.into_token_stream().to_string(),
            expected.into_token_stream().to_string()
        );
    }
}
