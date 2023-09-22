use proc_macro2::{Span, TokenStream};
use quote::{quote, quote_spanned};
use syn::{parse_quote_spanned, spanned::Spanned};

// the variable names used in the AST to construct and emit meaningful errors
const FAILURE_MESSAGE_STR: &str = "_prusti_rtc_failure_message";
const BUFFER_IDENT: &str = "_prusti_rtc_info_buffer";
const BUFFER_LEN_IDENT: &str = "_prusti_rtc_info_len";

pub(crate) fn failure_message_ident(span: Span) -> syn::Ident {
    syn::Ident::new(FAILURE_MESSAGE_STR, span)
}

pub(crate) fn buffer_ident(span: Span) -> syn::Ident {
    syn::Ident::new(BUFFER_IDENT, span)
}

pub(crate) fn buffer_len_ident(span: Span) -> syn::Ident {
    syn::Ident::new(BUFFER_LEN_IDENT, span)
}

/// Define the error message (or the corresponding fixed sized buffer) so
/// it can be extended with information at runtime
pub(crate) fn define_failure_message(span: Span, message: &String) -> TokenStream {
    if cfg!(feature = "std") {
        let ident = failure_message_ident(span);
        quote_spanned! {span =>
            let mut #ident = #message.to_string();
        }
    } else {
        let failure_message_len = message.len();
        let buffer_length = message.len() * 5;
        let buffer_ident = buffer_ident(span);
        let buffer_len_ident = buffer_len_ident(span);
        quote_spanned! {span =>
            let mut #buffer_ident = [0u8; #buffer_length];
            let mut #buffer_len_ident = #failure_message_len;
            #buffer_ident[..#buffer_len_ident].copy_from_slice(#message.as_bytes());
        }
    }
}

/// Create a str from the buffer of the error message just before it's emitted
/// (only required in case std is not available)
pub(crate) fn construct_failure_message_opt(span: Span) -> Option<TokenStream> {
    let ident = failure_message_ident(span);
    if !cfg!(feature = "std") {
        Some(quote_spanned!(span =>
            let #ident: &str = ::core::str::from_utf8(&_prusti_rtc_info_buffer[.._prusti_rtc_info_len]).unwrap();
        ))
    } else {
        None
    }
}

/// Creates a call to the check() function, that extends the error with additional
/// information in case that the boolean passed to it evaluates to false
pub(crate) fn call_check_expr(expr: syn::Expr, message: String) -> syn::Expr {
    let span = expr.span();
    if cfg!(feature = "std") {
        let failure_message_ident = failure_message_ident(span);
        parse_quote_spanned! {span=>
            ::prusti_contracts::runtime_check_internals::check_expr(#expr, #message, &mut #failure_message_ident)
        }
    } else {
        let buffer_ident = buffer_ident(span);
        let buffer_len_ident = buffer_len_ident(span);
        parse_quote_spanned! {span =>
            ::prusti_contracts::runtime_check_internals::check_expr(#expr, #message, &mut #buffer_ident, &mut #buffer_len_ident)
        }
    }
}

/// If a quantifier fails at a specific index, extend the error message with that
/// information
pub(crate) fn extend_error_indexed(expr: &syn::Expr, name_token: &TokenStream) -> syn::Block {
    let span = expr.span();
    let expr_string = expr
        .span()
        .source_text()
        .unwrap_or_else(|| quote!(expr).to_string());
    let error_string = format!(
        "\n\t> expression {} was violated for index {}=",
        expr_string, name_token
    );
    if cfg!(feature = "std") {
        let failure_message_ident = failure_message_ident(span);
        parse_quote_spanned! {span=>
            {
                #failure_message_ident.push_str(#error_string);
                #failure_message_ident.push_str(format!("{}", #name_token).as_str());
            }
        }
    } else {
        let buffer_ident = buffer_ident(span);
        let buffer_len_ident = buffer_len_ident(span);
        let error_len = error_string.len();
        parse_quote_spanned! {span =>
            {
                #buffer_ident[#buffer_len_ident..#buffer_len_ident+#error_len]
                .copy_from_slice(#error_string.as_bytes());
                let num_str = ::prusti_contracts::runtime_check_internals::num_to_str(
                    #name_token,
                    &mut num_buffer
                    );
                #buffer_ident[
                    #buffer_len_ident+#error_len..#buffer_len_ident+#error_len+num_str.len()
                ].copy_from_slice(num_str.as_bytes());
                #buffer_len_ident = #buffer_len_ident
                    + #error_len
                    + num_str.len();
            }
        }
    }
}
