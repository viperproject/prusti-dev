//! Various extensions to syn types and TokenStreams
use proc_macro2::{TokenStream, TokenTree};
use quote::{quote, quote_spanned, ToTokens};
use syn::{Expr, FnArg, ImplItemMethod, ItemFn, Pat, PatType, Signature, Token, TraitItemMethod};
use syn::parse::Parse;
use syn::punctuated::Punctuated;
use syn::spanned::Spanned;

/// Rewrites every occurence of "self" to "_self" in a token stream
pub trait SelfRewriter {
    fn rewrite_self(self) -> Self;
}

impl<T: ToTokens+Parse> SelfRewriter for T {
    fn rewrite_self(self) -> Self {
        let tokens = self.to_token_stream();
        let tokens_span = tokens.span();
        let rewritten = TokenStream::from_iter(tokens.into_iter().map(|token| match token {
            TokenTree::Group(group) => {
                let new_group =
                    proc_macro2::Group::new(group.delimiter(), group.stream().rewrite_self());
                new_group.to_token_stream()
            }
            TokenTree::Ident(mut ident) => {
                if ident == "self" {
                    ident = proc_macro2::Ident::new("_self", ident.span());
                }
                ident.into_token_stream()
            }
            _ => token.into_token_stream(),
        }));
        parse_quote_spanned!(tokens_span=>
            #rewritten
        )
    }
}

/// Rewrites the receiver of a method-like type, i.e.
/// for a provided type `T`, rewrites the `self` in `fn foo(&mut self)` to `fn foo(_self: &mut T`
pub trait RewriteMethodReceiver {
    fn rewrite_receiver<T: ToTokens>(&mut self, new_ty: &T);
}

impl<H: HasSignature> RewriteMethodReceiver for H {
    fn rewrite_receiver<T: ToTokens>(&mut self, new_ty: &T) {
        self.sig_mut().inputs.rewrite_receiver(new_ty);
    }
}

impl RewriteMethodReceiver for Punctuated<FnArg, Token![,]> {
    fn rewrite_receiver<T: ToTokens>(&mut self, new_ty: &T) {
        for input in self.iter_mut() {
            let input_span = input.span();
            if let FnArg::Receiver(receiver) = input {
                let and = if receiver.reference.is_some() {
                    // TODO: do lifetimes need to be specified here?
                    quote_spanned! {input_span=> &}
                } else {
                    quote! {}
                };
                let mutability = &receiver.mutability;
                let fn_arg: FnArg = parse_quote_spanned! {input_span=>
                    _self : #and #mutability #new_ty
                };
                *input = fn_arg;
            }
        }
    }
}

/// Given a method signature with parameters, this function returns all typed parameters
/// as they were used as arguments for the function call.
/// # Example
/// Given some function `fn foo(&self, arg1: i32, arg2: bool)`,
/// returns `arg1, arg2`
pub trait MethodParamsAsCallArguments {
    fn params_as_call_args(&self) -> Punctuated<Expr, Token![,]>;
}

impl<H: HasSignature> MethodParamsAsCallArguments for H {
    fn params_as_call_args(&self) -> Punctuated<Expr, Token!(,)> {
        self.sig().inputs.params_as_call_args()
    }
}

impl MethodParamsAsCallArguments for Punctuated<FnArg, Token![,]> {
    fn params_as_call_args(&self) -> Punctuated<Expr, Token!(,)> {
        let mut args = Punctuated::new();
        for param in self.iter() {
            let span = param.span();
            if let FnArg::Typed(PatType { pat: box Pat::Ident(ident), .. }) = param {
                args.push(parse_quote_spanned!(span=>#ident));
            }
            args.push_punct(<Token![,]>::default());
        }
        args
    }
}

/// Abstraction over everything that has a [syn::Signature]
pub trait HasSignature {
    fn sig(&self) -> &Signature;
    fn sig_mut(&mut self) -> &mut Signature;
}

impl HasSignature for Signature {
    fn sig(&self) -> &Signature {
        self
    }

    fn sig_mut(&mut self) -> &mut Signature {
        self
    }
}

impl HasSignature for ImplItemMethod {
    fn sig(&self) -> &Signature {
        &self.sig
    }

    fn sig_mut(&mut self) -> &mut Signature {
        &mut self.sig
    }
}

impl HasSignature for ItemFn {
    fn sig(&self) -> &Signature {
        &self.sig
    }

    fn sig_mut(&mut self) -> &mut Signature {
        &mut self.sig
    }
}

impl HasSignature for TraitItemMethod {
    fn sig(&self) -> &Signature {
        &self.sig
    }

    fn sig_mut(&mut self) -> &mut Signature {
        &mut self.sig
    }
}
