use super::parse_quote_spanned;
use crate::{
    common::add_phantom_data_for_generic_params,
    user_provided_type_params::{
        UserAnnotatedTypeParam, UserAnnotatedTypeParamParser, UserAnnotatedTypeParamParserError,
    },
};
use proc_macro2::{Ident, TokenStream};
use quote::ToTokens;
use syn::{parse_quote, punctuated::Punctuated, spanned::Spanned};
use uuid::Uuid;
use log::{info};

/// See module level documentation
pub fn rewrite(item_struct: syn::ItemStruct) -> syn::Result<TokenStream> {
    info!("item_struct: {:?}", item_struct);
    //let res = rewrite_internal(item_struct);
    Ok(item_struct.into_token_stream())
    /*match res {
        Ok(result) => Ok(result.into_token_stream()),
        Err(err) => Err(err.into()),
    }*/
}

type TypeModelGenerationResult<R> = Result<R, TypeModelGenerationError>;

fn rewrite_internal(item_struct: syn::ItemStruct) -> TypeModelGenerationResult<TypeModel> {
    let idents = GeneratedIdents::generate(&item_struct);

    let model_struct = ModelStruct::create(&item_struct, &idents)?;
    let to_model_trait = ToModelTrait::create(&item_struct, &model_struct, &idents);
    let model_impl = create_model_impl(&item_struct, &model_struct, &to_model_trait)?;

    Ok(TypeModel {
        model_struct: model_struct.item,
        to_model_trait: to_model_trait.item,
        model_impl,
    })
}

struct ModelStruct {
    item: syn::ItemStruct,

    /// The path to the generated struct, e.g. to be used as a return type
    path: syn::Path,
}

impl ModelStruct {
    fn create(
        item_struct: &syn::ItemStruct,
        idents: &GeneratedIdents,
    ) -> TypeModelGenerationResult<Self> {
        if item_struct.fields.is_empty() {
            return Err(TypeModelGenerationError::MissingStructFields(
                item_struct.span(),
            ));
        }

        let model_struct_ident = &idents.model_struct_ident;
        let mut model_struct: syn::ItemStruct = parse_quote_spanned! {item_struct.span()=>
            #[derive(Copy, Clone)]
            #[allow(non_camel_case_types)]
            struct #model_struct_ident {}
        };

        let params = item_struct
            .parse_user_annotated_type_params()
            .map_err(TypeModelGenerationError::NonParsableTypeParam)?;
        model_struct.generics.params.extend(
            params
                .iter()
                .filter_map(UserAnnotatedTypeParam::as_generic_type_param)
                .cloned()
                .map(syn::GenericParam::Type),
        );

        model_struct.fields = item_struct.fields.clone();
        add_phantom_data_for_generic_params(&mut model_struct);

        let generic_idents = model_struct
            .generics
            .params
            .iter()
            .filter_map(|generic_param| match generic_param {
                syn::GenericParam::Type(type_param) => Some(&type_param.ident),
                _ => None,
            });
        let model_path: syn::Path = parse_quote!(
            #model_struct_ident < #(#generic_idents),* >
        );

        Ok(Self {
            item: model_struct,
            path: model_path,
        })
    }
}

struct ToModelTrait {
    item: syn::ItemTrait,

    /// The path to the generated trait, e.g. to be used as a return type
    path: syn::Path,
}

impl ToModelTrait {
    fn create(
        item_struct: &syn::ItemStruct,
        model_struct: &ModelStruct,
        idents: &GeneratedIdents,
    ) -> Self {
        let generic_params: Vec<syn::GenericParam> =
            model_struct.item.generics.params.iter().cloned().collect();
        let generic_params_idents: Vec<Ident> = generic_params
            .iter()
            .filter_map(|generic_param| match generic_param {
                syn::GenericParam::Type(type_param) => Some(type_param.ident.clone()),
                _ => None,
            })
            .collect();

        let model_path = &model_struct.path;

        let to_model_trait_ident = &idents.to_model_trait_ident;
        let item = parse_quote_spanned! {item_struct.span()=>
            #[allow(non_camel_case_types)]
            trait #to_model_trait_ident<#(#generic_params),*> {
                #[pure]
                #[trusted]
                #[prusti::type_models_to_model_fn]
                fn model(&self) -> #model_path;
            }
        };

        let path: syn::Path = parse_quote!(
            #to_model_trait_ident<#(#generic_params_idents),*>
        );

        Self { item, path }
    }
}

fn create_model_impl(
    item_struct: &syn::ItemStruct,
    model_struct: &ModelStruct,
    to_model_trait: &ToModelTrait,
) -> TypeModelGenerationResult<syn::ItemImpl> {
    let ident = &item_struct.ident;

    let mut rewritten_generics: Vec<syn::GenericParam> = Vec::new();
    for param in &item_struct.generics.params {
        match param {
            syn::GenericParam::Lifetime(_) => rewritten_generics.push(parse_quote!('_)),
            syn::GenericParam::Type(type_param) => {
                let mut cloned = type_param.clone();
                cloned.attrs.clear();
                cloned.bounds = Punctuated::default();
                rewritten_generics.push(syn::GenericParam::Type(cloned))
            }
            syn::GenericParam::Const(const_param) => {
                return Err(TypeModelGenerationError::ConstParamDisallowed(
                    const_param.span(),
                ))
            }
        }
    }

    let generic_params: Vec<syn::GenericParam> =
        model_struct.item.generics.params.iter().cloned().collect();

    let impl_path: syn::Path = parse_quote!(
        #ident < #(#rewritten_generics),* >
    );

    let to_model_trait_path = &to_model_trait.path;
    let model_struct_path = &model_struct.path;

    Ok(parse_quote_spanned! {item_struct.span()=>
        #[prusti::type_models_to_model_impl]
        impl<#(#generic_params),*> #to_model_trait_path for #impl_path {
            #[trusted]
            #[pure]
            fn model(&self) -> #model_struct_path {
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

        let uuid = Uuid::new_v4().simple();

        GeneratedIdents {
            model_struct_ident: Ident::new(
                format!("Prusti{}Model_{}", name, uuid).as_str(),
                item_struct.ident.span(),
            ),
            to_model_trait_ident: Ident::new(
                format!("Prusti{}ToModel_{}", name, uuid).as_str(),
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

    /// Thrown when user annotated generics could not be parsed
    NonParsableTypeParam(UserAnnotatedTypeParamParserError),
}

impl std::convert::From<TypeModelGenerationError> for syn::Error {
    fn from(err: TypeModelGenerationError) -> Self {
        match err {
            TypeModelGenerationError::MissingStructFields(span) => {
                syn::Error::new(span, "Type model must have at least one field")
            }
            TypeModelGenerationError::ConstParamDisallowed(span) => {
                syn::Error::new(span, "Const generics are disallowed for models")
            }
            TypeModelGenerationError::NonParsableTypeParam(parse_err) => parse_err.into(),
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
