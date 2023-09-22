use proc_macro2::TokenStream;
use quote::quote;
use syn::parse::{Parse, ParseStream};

// By default, attributes can only be attached to items like functions or closures.
// The point of this is to allow attaching attributes to the contents of a
// prusti_assert!() or similar (predicate).
// Note: this kind of consuming is only necessary when we want to consume an
// attribute at the beginning of a TokenStream without fully parsing it (mainly
// because the rest still has to be parsed by prusti_parse)
pub(crate) struct AttributeConsumer {
    pub attributes: Vec<syn::Attribute>,
    pub rest: TokenStream,
}

impl Parse for AttributeConsumer {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let attributes = input.call(syn::Attribute::parse_outer)?;
        let rest: TokenStream = input.parse().unwrap();
        Ok(Self { attributes, rest })
    }
}

// maybe we can make this more generic so it can be used in other places..
impl AttributeConsumer {
    pub fn get_attribute(&mut self, name: &str) -> Option<syn::Attribute> {
        if let Some(pos) = self.attributes.iter().position(|attr| {
            if let Some(ident) = attr.path.get_ident() {
                if *ident == name {
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

    // /// A function that can be used to check that all attributes have been
    // /// consumed. Returns an error with the span of the first remaining attribute
    // pub fn check_no_remaining_attrs(&self) -> syn::Result<()> {
    //     if let Some(attr) = self.attributes.first() {
    //         Err(syn::Error::new(
    //             attr.span(),
    //             "This attribute could not be processed and probably doesn't belong here",
    //         ))
    //     } else {
    //         Ok(())
    //     }
    // }

    pub fn tokens(self) -> TokenStream {
        let Self { attributes, rest } = self;
        let mut attrs: TokenStream = attributes.into_iter().map(|attr| quote!(#attr)).collect();
        attrs.extend(quote!(#rest));
        attrs
    }
}
