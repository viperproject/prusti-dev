//! Various extensions to syn types and TokenStreams
use proc_macro2::{TokenStream, TokenTree};
use quote::{quote, quote_spanned, ToTokens};
use syn::{Expr, FnArg, ImplItemMacro, ImplItemMethod, ItemFn, Macro, Pat, PatType, Signature, Token, TraitItemMacro, TraitItemMethod, TypePath};
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

/// Given a replacement for the `Self` type and the trait it should fulfill,
/// this type rewrites `Self` and associated type paths.
///
/// # Example
/// Given a `Self` replacement `T_Self` and a self trait constraint `Foo<X>`,
/// visiting a function
/// ```
/// fn foo(arg1: Self, arg2: Self::Assoc1) -> Self::Assoc2 { }
/// ```
/// results in
/// ```
/// fn foo(arg1: T_Self, arg2: <T_Self as Foo<X>>::Assoc1) -> <T_Self as Foo<X>>::Assoc2 { }
/// ```
pub trait AssociatedTypeRewritable {
    /// See documentation on [AssociatedTypeRewritable]
    fn rewrite_self_type_to_new_type(&mut self, self_type: &TypePath, self_type_trait: &TypePath);
}

impl<T: HasSignature> AssociatedTypeRewritable for T {
    fn rewrite_self_type_to_new_type(&mut self, self_type: &TypePath, self_type_trait: &TypePath) {
        let mut rewriter = AssociatedTypeRewriter {
            self_type,
            self_type_trait,
        };
        rewriter.rewrite_method_sig(self.sig_mut());
    }
}

/// See documentation on [AssociatedTypeRewritable]
struct AssociatedTypeRewriter<'a> {
    self_type: &'a TypePath,
    self_type_trait: &'a TypePath,
}

impl<'a> AssociatedTypeRewriter<'a> {
    pub fn rewrite_method_sig(&mut self, signature: &mut syn::Signature) {
        syn::visit_mut::visit_signature_mut(self, signature);
    }
}

impl<'a> syn::visit_mut::VisitMut for AssociatedTypeRewriter<'a> {
    fn visit_type_path_mut(&mut self, ty_path: &mut syn::TypePath) {
        if ty_path.qself.is_none()
            && !ty_path.path.segments.is_empty()
            && ty_path.path.segments[0].ident == "Self" {
            if ty_path.path.segments.len() == 1 {
                // replace `Self` type
                *ty_path = self.self_type.clone();
            } else if ty_path.path.segments.len() >= 2 {
                // replace associated types
                let mut path_rest = ty_path.path.segments.clone()
                    .into_pairs()
                    .skip(1)
                    .collect::<syn::punctuated::Punctuated::<syn::PathSegment, _>>();
                if ty_path.path.segments.trailing_punct() {
                    path_rest.push_punct(<syn::Token![::]>::default());
                }
                let self_type = &self.self_type;
                let self_type_trait = &self.self_type_trait;
                *ty_path = parse_quote_spanned! {ty_path.span()=>
                    < #self_type as #self_type_trait > :: #path_rest
                };
            }
        }
        syn::visit_mut::visit_type_path_mut(self, ty_path);
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

/// Abstraction over everything that has a [syn::Macro]
pub trait HasMacro {
    fn mac(&self) -> &Macro;
}

impl HasMacro for TraitItemMacro {
    fn mac(&self) -> &Macro {
        &self.mac
    }
}

impl HasMacro for ImplItemMacro {
    fn mac(&self) -> &Macro {
        &self.mac
    }
}