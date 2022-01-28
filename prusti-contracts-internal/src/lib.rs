extern crate proc_macro;

use proc_macro::TokenStream;
use prusti_specs::{rewrite_prusti_attributes, SpecAttributeKind};

#[proc_macro_attribute]
pub fn requires(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    rewrite_prusti_attributes(SpecAttributeKind::Requires, attr.into(), tokens.into()).into()
}

#[proc_macro_attribute]
pub fn ensures(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    rewrite_prusti_attributes(SpecAttributeKind::Ensures, attr.into(), tokens.into()).into()
}

#[proc_macro_attribute]
pub fn after_expiry(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    rewrite_prusti_attributes(SpecAttributeKind::AfterExpiry, attr.into(), tokens.into()).into()
}

#[proc_macro_attribute]
pub fn assert_on_expiry(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    rewrite_prusti_attributes(
        SpecAttributeKind::AssertOnExpiry,
        attr.into(),
        tokens.into(),
    )
    .into()
}

#[proc_macro_attribute]
pub fn pure(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    rewrite_prusti_attributes(SpecAttributeKind::Pure, attr.into(), tokens.into()).into()
}

#[proc_macro_attribute]
pub fn trusted(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    rewrite_prusti_attributes(SpecAttributeKind::Trusted, attr.into(), tokens.into()).into()
}

#[proc_macro]
pub fn body_invariant(tokens: TokenStream) -> TokenStream {
    prusti_specs::body_invariant(tokens.into()).into()
}

#[proc_macro]
pub fn closure(tokens: TokenStream) -> TokenStream {
    prusti_specs::closure(tokens.into(), false).into()
}

#[proc_macro_attribute]
pub fn refine_trait_spec(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    prusti_specs::refine_trait_spec(attr.into(), tokens.into()).into()
}

#[proc_macro_attribute]
pub fn extern_spec(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    prusti_specs::extern_spec(attr.into(), tokens.into()).into()
}

#[proc_macro]
pub fn predicate(tokens: TokenStream) -> TokenStream {
    prusti_specs::predicate(tokens.into()).into()
}
/// Macro for creating models for a type.
///
/// Types can be annotated with the `#[model]` macro:
/// ```rust
/// use std::iter::Iter;
/// #[model]
/// struct Iter<'a, i32> {
///     position: usize,
///     len: usize,
/// }
/// ```
/// This creates a model for the `Iter` type defined in the standard library to be used
/// as an abstraction in specifications. The model needs to be copyable, i.e. all fields need
/// to be `Copy`.
///
/// The model can then be used in specifications:
/// ```rust
/// #[ensures( result.model().position == 0 )]
/// #[ensures( result.model().len == slice.len() )]
/// #[trusted]
/// fn create_iter(slice: &[i32]) -> std::slice::Iter<'_, i32> {
///     slice.iter()
/// }
/// ```
/// ## Caution
/// The model is only to be used in specifications (pre- and postconditions of functions or methods)
/// and never in code which will be executed. Using `.model()` will cause a panic during runtime.
///
/// ## Remarks
/// * Specifications involving models can only be used in trusted functions or methods, i.e. on
///   explicitly `#[trusted]` methods or on `#[extern_spec]`s.
/// * Models can not be generic, i.e. creating a model for `Vec<T>` is not possible. It is however
///   possible to model concrete generic types, i.e. `Vec<i32>` and `Vec<u32>`
#[proc_macro_attribute]
pub fn model(_attr: TokenStream, tokens: TokenStream) -> TokenStream {
    prusti_specs::type_model(_attr.into(), tokens.into()).into()
}
