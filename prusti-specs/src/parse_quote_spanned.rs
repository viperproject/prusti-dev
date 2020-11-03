///  Same as `parse_quote!`, but applies a given span to all tokens originating within
/// the macro invocation.
///
/// ```
/// # use proc_macro2::Span;
/// # use quote::quote_spanned;
/// #
/// # const IGNORE_TOKENS: &'static str = stringify! {
/// let span = /* ... */;
/// # };
/// # let span = Span::call_site();
/// # let init = 0;
///
/// // On one line, use parentheses.
/// let expr: syn::Expr = parse_quote_spanned!(span=> my_identifier);
///
/// // On multiple lines, place the span at the top and use braces.
/// let mut struct: syn::ItemStruct = parse_quote_spanned! {span=>
///     struct MyStruct {}
/// };
/// ```
#[macro_export]
macro_rules! parse_quote_spanned {
    ($($tt:tt)*) => {{
        let spanned_tokens = quote::quote_spanned!($($tt)*);
        syn::parse_quote!(#spanned_tokens)
    }};
}
