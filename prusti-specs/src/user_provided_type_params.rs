use proc_macro2::TokenStream;
use quote::ToTokens;
use syn::{spanned::Spanned, TypeParam};
use crate::common::HasGenerics;

#[derive(Debug)]
pub(crate) enum UserAnnotatedTypeParam {
    /// Something concrete, i.e. `i32`
    ConcreteType(syn::TypeParam),
    /// Something non-concrete, i.e. `T`
    GenericType(syn::TypeParam),
}

impl UserAnnotatedTypeParam {
    pub fn try_parse(from: &syn::TypeParam) -> ParserResult<Self> {
        if from.attrs.len() != 1 {
            return Err(UserAnnotatedTypeParamParserError::InvalidAnnotation(
                from.span(),
            ));
        }

        let path = &from.attrs[0].path;
        if path.segments.len() != 1 {
            return Err(UserAnnotatedTypeParamParserError::InvalidAnnotation(
                from.span(),
            ));
        }

        // Closure for cloning and removing the attrs
        let clone_without_attrs = || {
            let mut cloned = from.clone();
            cloned.attrs.clear();
            cloned
        };

        match path.segments[0].ident.to_string().as_str() {
            "generic" => Ok(UserAnnotatedTypeParam::GenericType(clone_without_attrs())),
            "concrete" => Ok(UserAnnotatedTypeParam::ConcreteType(clone_without_attrs())),
            _ => Err(UserAnnotatedTypeParamParserError::UnknownUserAnnotation(
                from.span(),
            )),
        }
    }

    pub fn as_generic_type_param(&self) -> Option<&TypeParam> {
        match self {
            UserAnnotatedTypeParam::GenericType(type_param) => Some(type_param),
            _ => None,
        }
    }

    // Silencing dead code warning, this method is here for completeness and used in tests
    #[allow(dead_code)]
    pub fn as_concrete_type_param(&self) -> Option<&TypeParam> {
        match self {
            UserAnnotatedTypeParam::ConcreteType(type_param) => Some(type_param),
            _ => None,
        }
    }
}

impl ToTokens for UserAnnotatedTypeParam {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match &self {
            UserAnnotatedTypeParam::ConcreteType(ty_param)
            | UserAnnotatedTypeParam::GenericType(ty_param) => ty_param.to_tokens(tokens),
        }
    }
}

#[derive(Debug)]
pub(crate) enum UserAnnotatedTypeParamParserError {
    UnknownUserAnnotation(proc_macro2::Span),
    InvalidAnnotation(proc_macro2::Span),
}

impl std::convert::From<UserAnnotatedTypeParamParserError> for syn::Error {
    fn from(err: UserAnnotatedTypeParamParserError) -> Self {
        use UserAnnotatedTypeParamParserError::*;
        match err {
            InvalidAnnotation(span) | UnknownUserAnnotation(span) => syn::Error::new(
                span,
                "Type parameters must be annotated with exactly one of #[generic] or #[concrete]",
            ),
        }
    }
}

type ParserResult<R> = Result<R, UserAnnotatedTypeParamParserError>;

pub(crate) trait UserAnnotatedTypeParamParser {
    fn parse_user_annotated_type_params(&self) -> ParserResult<Vec<UserAnnotatedTypeParam>>;
}

impl<T: HasGenerics> UserAnnotatedTypeParamParser for T {
    fn parse_user_annotated_type_params(&self) -> ParserResult<Vec<UserAnnotatedTypeParam>> {
        self.generics()
            .params
            .iter()
            .filter_map(|generic_param| match generic_param {
                syn::GenericParam::Type(param) => Some(param),
                _ => None,
            })
            .map(UserAnnotatedTypeParam::try_parse)
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::UserAnnotatedTypeParamParserError::*;
    mod parsing {
        use super::*;
        use crate::user_provided_type_params::UserAnnotatedTypeParam;
        use syn::parse_quote;

        #[test]
        fn unknown_annotation() {
            let type_param: syn::TypeParam = syn::parse_quote!(
                #[hello_world]
                T
            );
            let res = UserAnnotatedTypeParam::try_parse(&type_param);
            assert!(matches!(res, Err(UnknownUserAnnotation(_))));
        }

        #[test]
        fn missing_annotation() {
            let type_param: syn::TypeParam = syn::parse_quote!(T);
            let res = UserAnnotatedTypeParam::try_parse(&type_param);
            assert!(matches!(res, Err(InvalidAnnotation(_))));
        }

        #[test]
        fn ambiguous_annotation() {
            let type_param: syn::TypeParam = syn::parse_quote!(
                #[generic]
                #[concrete]
                T
            );
            let res = UserAnnotatedTypeParam::try_parse(&type_param);
            assert!(matches!(res, Err(InvalidAnnotation(_))));
        }

        #[test]
        fn ok_generic_type() {
            let type_param: syn::TypeParam = syn::parse_quote!(
                #[generic]
                T
            );
            let res = UserAnnotatedTypeParam::try_parse(&type_param);
            assert!(matches!(res, Ok(UserAnnotatedTypeParam::GenericType(_))));
            let expected: syn::TypeParam = parse_quote!(T);
            assert_eq!(
                &expected,
                res.unwrap()
                    .as_generic_type_param()
                    .expect("Expected generic type param")
            );
        }

        #[test]
        fn ok_concrete_type() {
            let type_param: syn::TypeParam = syn::parse_quote!(
                #[concrete]
                T
            );
            let res = UserAnnotatedTypeParam::try_parse(&type_param);
            assert!(matches!(res, Ok(UserAnnotatedTypeParam::ConcreteType(_))));
            let expected: syn::TypeParam = parse_quote!(T);
            assert_eq!(
                &expected,
                res.unwrap()
                    .as_concrete_type_param()
                    .expect("Expected concrete type param")
            );
        }
    }
}
