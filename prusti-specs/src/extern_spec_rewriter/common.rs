use crate::{ExternSpecKind, extract_prusti_attributes, generate_spec_and_assertions, RewritableReceiver, SelfTypeRewriter};
use quote::{quote, ToTokens};
use syn::{Expr, FnArg, parse_quote_spanned, Pat, PatType, Token};
use syn::punctuated::Punctuated;
use syn::spanned::Spanned;
use crate::common::{HasAttributes, HasSignature};
use crate::span_overrider::SpanOverrider;
use crate::untyped::AnyFnItem;
use syn::visit::Visit;
use syn::visit_mut::VisitMut;

/// Counts the number of elided lifetimes in receivers and types.
/// For details see the function `with_explicit_lifetimes`.
struct ElidedLifetimeCounter {
    num_elided_lifetimes: u32
}


impl ElidedLifetimeCounter {
    fn new() -> ElidedLifetimeCounter {
        ElidedLifetimeCounter { num_elided_lifetimes: 0 }
    }
}

impl <'ast> syn::visit::Visit<'ast> for ElidedLifetimeCounter {
    fn visit_receiver(&mut self, receiver: &syn::Receiver) {
        if let Some((_, None)) = receiver.reference {
            self.num_elided_lifetimes += 1;
        }
    }

    fn visit_type_reference(&mut self, reference: &syn::TypeReference) {
        if reference.lifetime.is_none() {
            self.num_elided_lifetimes += 1;
        }
    }
}


fn has_multiple_elided_lifetimes(inputs: &Punctuated<FnArg, syn::token::Comma>) -> bool {
    let mut visitor = ElidedLifetimeCounter::new();
    for input in inputs {
        visitor.visit_fn_arg(input);
    }
    visitor.num_elided_lifetimes > 1
}

fn returns_reference_with_elided_lifetime(return_type: &syn::ReturnType) -> bool {
    let mut visitor = ElidedLifetimeCounter::new();
    visitor.visit_return_type(return_type);
    visitor.num_elided_lifetimes >= 1
}

/// Rust has a special lifetime elision rule for methods containing `&self` or
/// `&mut self` (see rule 3 here: https://doc.rust-lang.org/nomicon/lifetime-elision.html)
///
/// Because the extern spec replaces `self` with `_self`; Rust will not apply this rule
/// to the rewritten spec. This function detects if Rust would apply the rule 3 lifetime elision
/// rules for the original signature; and if so, returns a new signature with explicit lifetime
/// annotations. The explicit lifetime annotations correspond to what Rust would assign
/// for the elided lifetimes in the original signature.
fn with_explicit_lifetimes(sig: &syn::Signature) -> Option<syn::Signature> {

    // This struct is responsible for inserting an explicit lifetime for elided
    // lifetimes in the receiver and output type.
    struct SelfLifetimeInserter {}

    impl syn::visit_mut::VisitMut for SelfLifetimeInserter {
        fn visit_type_reference_mut(&mut self, reference: &mut syn::TypeReference) {
            reference.lifetime = parse_quote_spanned!{reference.span() => 'prusti_self_lifetime };
        }

        fn visit_receiver_mut(&mut self, receiver: &mut syn::Receiver) {
            receiver.reference.as_mut().unwrap().1 = parse_quote_spanned!{receiver.span() => 'prusti_self_lifetime };
        }
    }

    if !returns_reference_with_elided_lifetime(&sig.output) ||
       !has_multiple_elided_lifetimes(&sig.inputs)
    {
        return None;
    }
    let mut new_sig = sig.clone();
    let mut inserter = SelfLifetimeInserter{};

    // Insert explicit lifetime parameter to method signature
    new_sig.generics.params.insert(0, parse_quote_spanned!{new_sig.generics.params.span() => 'prusti_self_lifetime });

    // Assign the explicit lifetime to the reference to self
    if let Some(syn::FnArg::Receiver(r)) = new_sig.inputs.first_mut() {
        inserter.visit_receiver_mut(r)
    }

    // Assign the explicit lifetime to references in the output
    inserter.visit_return_type_mut(&mut new_sig.output);
    Some(new_sig)
}

/// Generates a method stub and spec functions for an externally specified function.
///
/// # Example
/// Given an external specification such as
/// ```ignore
/// #[extern_spec]
/// impl SomeTrait for SomeStruct {
///     // specs
///     fn the_trait_method(&self, arg: Self::AssocType) -> Bar;
/// }
/// ```
///
/// Generates a stub method and *sanitized* spec functions:
/// ```ignore
/// // spec functions with "self" rewritten to "_self: SomeStruct"
/// fn the_trait_method(_self: SomeStruct, arg: <SomeStruct as SomeTrait::AssocType> -> Bar {
///     <SomeStruct as SomeTrait>::the_trait_method(_self, arg);
///     unimplemented!()
/// }
/// ```
///
pub(crate) fn generate_extern_spec_method_stub<T: HasSignature + HasAttributes + Spanned>(
    method: &T,
    self_type: &syn::TypePath,
    self_type_trait: Option<&syn::TypePath>,
    extern_spec_kind: ExternSpecKind,
) -> syn::Result<(syn::ImplItemMethod, Vec<syn::ImplItemMethod>)> {
    let base_sig = method.sig();

    // Make elided lifetimes explicit, if necessary.
    let method_sig = with_explicit_lifetimes(base_sig).unwrap_or_else(|| base_sig.clone());
    let method_sig_span = method_sig.span();
    let method_ident = &method_sig.ident;

    // Determine path to externally specified method in UFCS
    let method_path: syn::ExprPath = match self_type_trait {
        Some(self_type_as_trait) => parse_quote_spanned! {method_sig_span=>
            <#self_type as #self_type_as_trait> :: #method_ident
        },
        None => parse_quote_spanned! {method_sig_span=>
            <#self_type> :: #method_ident
        }
    };

    // Build the method stub
    let method_attrs = method.attrs().clone();
    let method_args = &method_sig.params_as_call_args();
    let extern_spec_kind_string: String = extern_spec_kind.into();
    let stub_method: syn::ImplItemMethod = parse_quote_spanned! {method.span()=>
        #[trusted]
        #[prusti::extern_spec = #extern_spec_kind_string]
        #(#method_attrs)*
        #[allow(unused, dead_code)]
        #method_sig {
            #method_path ( #method_args );
            unimplemented!()
        }
    };

    // Eagerly extract and process specifications
    let mut stub_method = AnyFnItem::ImplMethod(stub_method);
    let prusti_attributes = extract_prusti_attributes(&mut stub_method);
    let (spec_items, generated_attributes) =
        generate_spec_and_assertions(prusti_attributes, &stub_method)?;

    // In the generated spec items and the stub method:
    // - Rewrite associated types
    // - Rewrite "self" to "_self"
    let self_type_path = parse_quote_spanned! {self_type.span()=> #self_type };

    let mut stub_method = stub_method.expect_impl_item();
    stub_method.attrs.extend(generated_attributes);
    stub_method.rewrite_self_type(&self_type_path, self_type_trait);
    stub_method.rewrite_receiver(&self_type_path);

    // Set span of generated method to externally specified method for better error reporting
    syn::visit_mut::visit_impl_item_method_mut(&mut SpanOverrider::new(method_sig_span), &mut stub_method);

    let rewritten_spec_items = spec_items.into_iter().map(|spec_item| {
        match spec_item {
            syn::Item::Fn(spec_item_fn) => {
                let mut spec_item_fn: syn::ImplItemMethod = parse_quote_spanned! {spec_item_fn.span()=>
                    #spec_item_fn
                };
                spec_item_fn.rewrite_self_type(&self_type_path, self_type_trait);
                spec_item_fn.rewrite_receiver(&self_type_path);

                spec_item_fn
            }
            _ => unreachable!(),
        }
    }).collect::<Vec<_>>();

    Ok((stub_method, rewritten_spec_items))
}

/// Given a method signature with parameters, this function returns all typed parameters
/// as they were used as arguments for the function call.
/// # Example
/// Given some function `fn foo(&self, arg1: i32, arg2: bool)`,
/// returns `self, arg1, arg2`
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
        Punctuated::from_iter(
            self.iter()
                .map(|param| {
                    let span = param.span();
                    let call_arg: Expr = match param {
                        FnArg::Typed(PatType { pat: box Pat::Ident(ident), .. }) =>
                            parse_quote_spanned! {span=>#ident },
                        FnArg::Receiver(_) =>
                            parse_quote_spanned! {span=>self},
                        _ =>
                            unimplemented!(),
                    };
                    call_arg
                })
        )
    }
}

/// Add `PhantomData` markers for each type parameter to silence errors
/// about unused type parameters.
///
/// Given
/// ```text
/// struct Foo<A,B> {
/// }
/// ```
/// Result
/// ```text
/// struct Foo<A,B> {
///     ::core::marker::PhantomData<A>,
///     ::core::marker::PhantomData<B>
/// }
/// ```
pub fn add_phantom_data_for_generic_params(item_struct: &mut syn::ItemStruct) {
    let fields = item_struct.generics.params.iter()
        .flat_map(|param| match param {
            syn::GenericParam::Type(tp) => {
                let ident = tp.ident.clone();
                Some(quote!(::core::marker::PhantomData<#ident>))
            }
            syn::GenericParam::Lifetime(ld) => {
                let ident = ld.lifetime.clone();
                Some(quote!(&#ident ::core::marker::PhantomData<()>))
            }
            syn::GenericParam::Const(_cp) => None,
        });

    item_struct.fields = syn::Fields::Unnamed(syn::parse_quote! { ( #(#fields),* ) });
}

/// We take the Generics (parameters) defined with the `#[extern_spec] impl<...>` (the `<...>`)
/// but then need to pass those as arguments: `SomeStruct<...>`. This function translates from
/// the syntax of one to the other; e.g. `<T: Bound, 'l: Bound, const C: usize>` -> `<T, 'l, C>`
pub fn rewrite_generics(gens: &syn::Generics) -> syn::AngleBracketedGenericArguments {
    let args: Vec<syn::GenericArgument> = gens
        .params
        .clone()
        .into_iter()
        .map(|gp| {
            let ts = match gp {
                syn::GenericParam::Type(syn::TypeParam { ident, .. })
                | syn::GenericParam::Const(syn::ConstParam { ident, .. }) => ident.into_token_stream(),
                syn::GenericParam::Lifetime(ld) => ld.lifetime.into_token_stream(),
            };
            syn::parse2::<syn::GenericArgument>(ts).unwrap()
        })
        .collect();
    syn::parse_quote! { < #(#args),* > }
}
