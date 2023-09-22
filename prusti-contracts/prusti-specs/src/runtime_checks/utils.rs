use proc_macro2::TokenStream;
use quote::ToTokens;

// if expression is a identifier, get the name:
pub(crate) fn expression_name(expr: &syn::Expr) -> Option<String> {
    if let syn::Expr::Path(syn::ExprPath { path, .. }) = expr {
        Some(path.to_token_stream().to_string())
    } else {
        None
    }
}

/// Self explanatory. But also, these are the only supported types
/// for runtime checking quantifiers
pub(crate) fn is_primitive_number(ty: &syn::Type) -> bool {
    matches!(
        ty.to_token_stream().to_string().as_str(),
        "i8" | "i16"
            | "i32"
            | "i64"
            | "i128"
            | "isize"
            | "u8"
            | "u16"
            | "u32"
            | "u64"
            | "u128"
            | "usize"
    )
}

pub(crate) fn ty_unsigned(ty: &syn::Type) -> bool {
    matches!(
        ty.to_token_stream().to_string().as_str(),
        "u8" | "u16" | "u32" | "u64" | "u128" | "usize"
    )
}

/// Whether a type is small enough to be efficiently runtime checked
/// even without an upper / lower bound
pub(crate) fn ty_small_enough(ty: &syn::Type) -> bool {
    matches!(ty.to_token_stream().to_string().as_str(), "u8" | "i8")
}

pub fn get_attribute_contents(name: String, attrs: &Vec<syn::Attribute>) -> Option<TokenStream> {
    for attr in attrs {
        if attr.path.to_token_stream().to_string() == name {
            return Some(attr.tokens.clone());
        }
    }
    None
}
