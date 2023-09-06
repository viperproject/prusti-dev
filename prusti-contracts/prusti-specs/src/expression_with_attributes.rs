use proc_macro2::TokenStream;
use quote::quote;
use syn::parse::{Parse, ParseStream};

// By default, attributes can only be attached to
// items like functions or closures. The point of this is
// to allow attaching attributes to the contents of a
// prusti_assert!() or similar.
// In particular, we want to allow:
// `prusti_assert!(#[insert_runtime_check] expr);
pub(crate) struct ExpressionWithAttributes {
    pub attributes: Vec<syn::Attribute>,
    pub rest: TokenStream,
}

impl Parse for ExpressionWithAttributes {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let attributes = input.call(syn::Attribute::parse_outer)?;
        let rest: TokenStream = input.parse().unwrap();
        Ok(Self { attributes, rest })
    }
}

// maybe we can make this more generic so it can be used in other places..
impl ExpressionWithAttributes {
    pub fn remove_runtime_checks_attr(&mut self) -> Option<syn::Attribute> {
        if let Some(pos) = self.attributes.iter().position(|attr| {
            if let Some(ident) = attr.path.get_ident() {
                if &ident.to_string() == "insert_runtime_check" {
                    return true;
                }
            }
            false
        }) {
            Some(self.attributes.remove(pos))
        } else {
            None
        }
    }

    pub fn tokens(self) -> TokenStream {
        let Self { attributes, rest } = self;
        let mut attrs: TokenStream = attributes.into_iter().map(|attr| attr.tokens).collect();
        attrs.extend(quote!(#rest));
        attrs
    }
}
