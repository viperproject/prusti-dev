//! Common code for spec-rewriting

use std::borrow::BorrowMut;
use std::collections::HashMap;
use proc_macro2::Ident;
use syn::{GenericParam, parse_quote, TypeParam};
use syn::punctuated::Punctuated;
use syn::spanned::Spanned;
use uuid::Uuid;
pub(crate) use syn_extensions::*;
pub(crate) use self_type_rewriter::*;
pub(crate) use receiver_rewriter::*;

/// Module which provides various extension traits for syn types.
/// These allow for writing of generic code over these types.
mod syn_extensions {
    use syn::{Attribute, Generics, ImplItemMacro, ImplItemMethod, ItemFn, ItemImpl, ItemStruct, ItemTrait, Macro, Signature, TraitItemMacro, TraitItemMethod};

    /// Trait which signals that the corresponding syn item contains generics
    pub(crate) trait HasGenerics {
        fn generics(&self) -> &Generics;
        fn generics_mut(&mut self) -> &mut Generics;
    }

    impl HasGenerics for Generics {
        fn generics(&self) -> &Generics {
            self
        }
        fn generics_mut(&mut self) -> &mut Generics { self }
    }

    impl HasGenerics for ItemTrait {
        fn generics(&self) -> &Generics {
            &self.generics
        }
        fn generics_mut(&mut self) -> &mut Generics { &mut self.generics }
    }

    impl HasGenerics for ItemStruct {
        fn generics(&self) -> &Generics {
            &self.generics
        }
        fn generics_mut(&mut self) -> &mut Generics { &mut self.generics }
    }

    impl HasGenerics for ItemImpl {
        fn generics(&self) -> &syn::Generics {
            &self.generics
        }
        fn generics_mut(&mut self) -> &mut Generics { &mut self.generics }
    }

    /// Abstraction over everything that has a [syn::Signature]
    pub(crate) trait HasSignature {
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
    pub(crate) trait HasMacro {
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

    /// Abstraction over everything that has [syn::Attribute]s
    pub(crate) trait HasAttributes {
        fn attrs(&self) -> &Vec<Attribute>;
    }

    impl HasAttributes for TraitItemMethod {
        fn attrs(&self) -> &Vec<syn::Attribute> {
            &self.attrs
        }
    }

    impl HasAttributes for ImplItemMethod {
        fn attrs(&self) -> &Vec<Attribute> {
            &self.attrs
        }
    }
}

/// See [SelfTypeRewriter]
mod self_type_rewriter {
    use syn::{ImplItemMethod, ItemFn, parse_quote_spanned, TypePath};
    use syn::spanned::Spanned;
    use syn::visit_mut::VisitMut;

    /// Given a replacement for the `Self` type and the trait it should fulfill,
    /// this type rewrites `Self` and associated type paths.
    ///
    /// # Example
    /// Given a `Self` replacement `T_Self` and a self trait constraint `Foo<X>`,
    /// visiting a function
    /// ```
    /// fn foo(&self, arg1: Self, arg2: Self::Assoc1) -> Self::Assoc2 {
    ///     self.bar()
    /// }
    /// ```
    /// results in
    /// ```
    /// fn foo(&self, arg1: T_Self, arg2: <T_Self as Foo<X>>::Assoc1) -> <T_Self as Foo<X>>::Assoc2 {
    ///     self.bar()
    /// }
    /// ```
    pub(crate) trait SelfTypeRewriter {
        fn rewrite_self_type(&mut self, self_type: &TypePath, self_type_trait: Option<&TypePath>);
    }

    impl SelfTypeRewriter for ItemFn {
        fn rewrite_self_type(&mut self, self_type: &TypePath, self_type_trait: Option<&TypePath>) {
            let mut rewriter = Rewriter {self_type, self_type_trait};
            rewriter.rewrite_item_fn(self);
        }
    }

    impl SelfTypeRewriter for ImplItemMethod {
        fn rewrite_self_type(&mut self, self_type: &TypePath, self_type_trait: Option<&TypePath>) {
            let mut rewriter = Rewriter {self_type, self_type_trait};
            rewriter.rewrite_impl_item_method(self);
        }
    }

    struct Rewriter<'a> {
        self_type: &'a TypePath,
        self_type_trait: Option<&'a TypePath>,
    }

    impl<'a> Rewriter<'a> {
        pub fn rewrite_impl_item_method(&mut self, item: &mut ImplItemMethod) {
            syn::visit_mut::visit_impl_item_method_mut(self, item);
        }

        pub fn rewrite_item_fn(&mut self, item: &mut syn::ItemFn) {
            syn::visit_mut::visit_item_fn_mut(self, item);
        }
    }

    impl<'a> VisitMut for Rewriter<'a> {
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
                        .collect::<syn::punctuated::Punctuated<syn::PathSegment, _>>();
                    if ty_path.path.segments.trailing_punct() {
                        path_rest.push_punct(<syn::Token![::]>::default());
                    }
                    let self_type = &self.self_type;
                    let self_type_trait = &self.self_type_trait;
                    let new_type_path: syn::TypePath = parse_quote_spanned! {ty_path.span()=>
                    < #self_type as #self_type_trait > :: #path_rest
                };
                    *ty_path = new_type_path;
                }
            }
            syn::visit_mut::visit_type_path_mut(self, ty_path);
        }
    }
}

/// See [RewritableReceiver]
mod receiver_rewriter {
    use proc_macro2::{Ident, TokenStream, TokenTree};
    use quote::{quote, quote_spanned};
    use syn::{FnArg, ImplItemMethod, ItemFn, Macro, parse_quote_spanned, TypePath};
    use syn::spanned::Spanned;
    use syn::visit_mut::VisitMut;

    /// Rewrites the receiver of a method-like item.
    /// This can be used to convert impl methods to free-standing functions.
    ///
    /// # Example
    /// For a provided new type `T`, the function
    /// ```ignore
    /// fn foo(&mut self, arg1: Bar) -> Baz {
    ///     self.qux()
    /// }
    /// ```
    /// will be rewritten to
    /// ```ignore
    /// fn foo(_self: &mut T, arg1: Bar) -> Baz {
    ///     _self.qux()
    /// }
    /// ```
    pub(crate) trait RewritableReceiver {
        fn rewrite_receiver(&mut self, new_ty: &TypePath);
    }

    impl RewritableReceiver for ImplItemMethod {
        fn rewrite_receiver(&mut self, new_ty: &TypePath) {
            let mut rewriter = Rewriter {new_ty};
            rewriter.rewrite_impl_item_method(self);
        }
    }

    impl RewritableReceiver for ItemFn {
        fn rewrite_receiver(&mut self, new_ty: &TypePath) {
            let mut rewriter = Rewriter {new_ty};
            rewriter.rewrite_item_fn(self);
        }
    }

    struct Rewriter<'a> {
        new_ty: &'a TypePath,
    }

    impl<'a> Rewriter<'a> {
        fn rewrite_impl_item_method(&mut self, item: &mut ImplItemMethod) {
            syn::visit_mut::visit_impl_item_method_mut(self, item);
        }

        fn rewrite_item_fn(&mut self, item: &mut ItemFn) {
            syn::visit_mut::visit_item_fn_mut(self, item);
        }

        fn rewrite_tokens(&self, tokens: TokenStream) -> TokenStream {
            let tokens_span = tokens.span();
            let rewritten = TokenStream::from_iter(tokens.into_iter().map(|token| match token {
                TokenTree::Group(group) => {
                    let new_group =
                        proc_macro2::Group::new(group.delimiter(), self.rewrite_tokens(group.stream()));
                    TokenTree::Group(new_group)
                }
                TokenTree::Ident(ident) if ident == "self" => {
                    TokenTree::Ident(proc_macro2::Ident::new("_self", ident.span()))
                },
                other => other,
            }));
            parse_quote_spanned! {tokens_span=>
                #rewritten
            }
        }
    }

    impl<'a> VisitMut for Rewriter<'a> {
        fn visit_fn_arg_mut(&mut self, fn_arg: &mut FnArg) {
            if let FnArg::Receiver(receiver) = fn_arg {
                let span = receiver.span();
                let and = match &receiver.reference {
                    Some((_, Some(lifetime))) =>
                        quote_spanned!{span => &#lifetime},
                    Some((_, None)) =>
                        quote_spanned!{span => &},
                    None => quote! {}
                };
                let mutability = &receiver.mutability;
                let new_ty = self.new_ty;
                let new_fn_arg: FnArg = parse_quote_spanned! {span=>
                _self : #and #mutability #new_ty
            };
                *fn_arg = new_fn_arg;
            } else {
                syn::visit_mut::visit_fn_arg_mut(self, fn_arg);
            }
        }

        fn visit_ident_mut(&mut self, ident: &mut Ident) {
            if ident == "self" {
                *ident = Ident::new("_self", ident.span());
            }
            syn::visit_mut::visit_ident_mut(self, ident)
        }

        fn visit_macro_mut(&mut self, makro: &mut Macro) {
            // A macro can appear in a spec function (e.g. `matches!`)
            makro.tokens = self.rewrite_tokens(makro.tokens.clone());
            syn::visit_mut::visit_macro_mut(self, makro);
        }
    }
}

/// Copies the [syn::Generics] of `source` to the generics of `target`
/// **Important**: Lifetimes and const params are currently ignored.
/// If `source` has generic params which do not appear in `target`, they are added first.
///
/// # Example
/// ```ignore
/// impl<A: U, B: V> Foo for Bar where WI{
///     fn baz<C>(...) -> ... where WF
/// }
/// ```
/// When merging the `impl` into `baz`, we'll get
/// ```ignore
/// fn baz<A: U, B: V, C>(...) -> ... where WI, WF
/// ```
pub(crate) fn merge_generics<T: HasGenerics>(target: &mut T, source: &T) {
    let generics_target = target.generics_mut();
    let generics_source = source.generics();

    // Merge all type params
    let mut existing_target_type_params: HashMap<Ident, &mut TypeParam> = HashMap::new();
    let mut new_generic_params: Vec<GenericParam> = Vec::new();
    for param_target in generics_target.params.iter_mut() {
        if let GenericParam::Type(type_param_target) = param_target {
            existing_target_type_params.insert(type_param_target.ident.clone(), type_param_target);
        }
    }

    for param_source in generics_source.params.iter() {
        // Lifetimes and consts are currently not handled
        if let GenericParam::Type(type_param_source) = param_source {
            // We can remove the target type param here, because the source will not have the
            // same type param with the same identifiers
            let maybe_type_param_source = existing_target_type_params.remove(&type_param_source.ident);
            if let Some(type_param_target) = maybe_type_param_source {
                type_param_target.bounds.extend(type_param_source.bounds.clone());
            } else {
                new_generic_params.push(GenericParam::Type(type_param_source.clone()));
            }
        }
    }

    // Merge the new parameters with the existing ones.
    // New parameters are added as a prefix.
    if !new_generic_params.is_empty() {
        let existing_params = generics_target.params.clone();
        new_generic_params.extend(existing_params);
        generics_target.params = Punctuated::from_iter(new_generic_params);
    }

    // Merge the where clause
    match (generics_target.where_clause.as_mut(), generics_source.where_clause.as_ref()) {
        (Some(target_where), Some(source_where)) => target_where.predicates.extend(source_where.predicates.clone()),
        (None, Some(source_where)) => generics_target.where_clause = Some(source_where.clone()),
        _ => (),
    }
}

/// Add `PhantomData` markers for each type parameter to silence errors
/// about unused type parameters. Works for structs with named or unnamed fields
/// Given
/// ```text
/// struct Foo<A,B> {
///     // ... fields ...
/// }
/// ```
/// Result
/// ```text
/// struct Foo<A,B> {
///     // ... fields ...
///     ::core::marker::PhantomData<A>,
///     ::core::marker::PhantomData<B>
/// }
/// ```
pub(crate) fn add_phantom_data_for_generic_params(item_struct: &mut syn::ItemStruct) {
    let mut fields = vec![];

    let need_named_fields = matches!(item_struct.fields, syn::Fields::Named(_));

    let generate_field_ident = |span: proc_macro2::Span| {
        if need_named_fields {
            let uuid = Uuid::new_v4().simple();
            let field_name = format!("prusti_injected_phantom_field_{}", uuid);
            return Some(syn::Ident::new(field_name.as_str(), span));
        }
        None
    };

    for generic_param in item_struct.generics.params.iter() {
        let ty: Option<syn::Type> = match generic_param {
            syn::GenericParam::Type(type_param) => {
                let ty_ident = &type_param.ident;
                let ty: syn::Type = parse_quote!(::core::marker::PhantomData<#ty_ident>);
                Some(ty)
            }
            syn::GenericParam::Lifetime(lt_def) => {
                let lt = &lt_def.lifetime;
                let ty: syn::Type = parse_quote!(&#lt ::core::marker::PhantomData<()>);
                Some(ty)
            }
            _ => None,
        };

        if ty.is_none() {
            continue;
        }
        let ty = ty.unwrap();

        let field = syn::Field {
            vis: syn::Visibility::Inherited,
            attrs: Vec::default(),
            ident: generate_field_ident(generic_param.span()),
            colon_token: None,
            ty,
        };
        fields.push(field);
    }

    if matches!(item_struct.fields, syn::Fields::Unit) {
        let field_types: Vec<syn::Type> = fields.into_iter().map(|field| field.ty).collect();
        let fields_unnamed: syn::FieldsUnnamed = parse_quote!((#(#field_types),*));
        item_struct.fields = syn::Fields::Unnamed(fields_unnamed);
    } else {
        match item_struct.fields.borrow_mut() {
            syn::Fields::Named(named_fields) => {
                named_fields.named.extend(fields);
            }
            syn::Fields::Unnamed(unnamed_fields) => {
                unnamed_fields.unnamed.extend(fields);
            }
            syn::Fields::Unit => unreachable!(),
        };
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    mod merge_generics {
        use syn::parse_quote;
        use crate::merge_generics;

        macro_rules! test_merge {
            ([$($source:tt)+] into [$($target:tt)+] gives [$($expected:tt)+]) => {
                let mut target: syn::ItemImpl = parse_quote! { $($target)+ };
                let source: syn::ItemImpl = parse_quote! { $($source)+ };
                merge_generics(&mut target, &source);
                let expected: syn::ItemImpl = parse_quote! { $($expected)+ };
                assert_eq!(expected, target);
            }
        }

        #[test]
        fn test_params() {
            test_merge! {
                [impl<U: B> Foo for Bar {}] into
                [impl<T: A> Foo for Bar {}] gives
                [impl<U: B, T: A> Foo for Bar {}]
            }
            test_merge! {
                [impl<T: B> Foo for Bar {}] into
                [impl<T: A> Foo for Bar {}] gives
                [impl<T: A+B> Foo for Bar {}]
            }
            test_merge! {
                [impl<T: B, U: C> Foo for Bar {}] into
                [impl<T: A> Foo for Bar {}] gives
                [impl<U: C, T: A+B> Foo for Bar {}]
            }
            test_merge! {
                [impl<T: A> Foo for Bar {}] into
                [impl<> Foo for Bar {}] gives
                [impl<T: A> Foo for Bar {}]
            }
        }

        #[test]
        fn test_where_clause() {
            test_merge! {
                [impl<U> Foo for Bar where U: B {}] into
                [impl<T> Foo for Bar where T: A {}] gives
                [impl<U, T> Foo for Bar where T: A, U: B {}]
            }
            test_merge! {
                [impl<T> Foo for Bar where T: B {}] into
                [impl<T> Foo for Bar where T: A {}] gives
                [impl<T> Foo for Bar where T: A, T: B {}]
            }
            test_merge! {
                [impl<T> Foo for Bar where T: A {}] into
                [impl<T> Foo for Bar {}] gives
                [impl<T> Foo for Bar where T: A {}]
            }
        }
    }

    mod phantom_data {
        use super::*;
        use quote::ToTokens;

        #[test]
        fn phantom_data_for_struct_with_named_fields() {
            let mut item_struct: syn::ItemStruct = parse_quote!(
                struct Foo<A, B, C, 'a> {
                    fld1: A,
                }
            );

            add_phantom_data_for_generic_params(&mut item_struct);

            assert_eq!(5, item_struct.fields.len());
            assert!(matches!(item_struct.fields, syn::Fields::Named(_)));
            let mut fields_iter = item_struct.fields.iter();
            let field = fields_iter.next().unwrap();
            assert_eq!("fld1", field.ident.as_ref().unwrap().to_string());
            assert_eq!("A", field.ty.to_token_stream().to_string());
            let field = fields_iter.next().unwrap();
            assert!(field.ident.as_ref().is_some());
            assert_phantom_type_for("A", field);
            let field = fields_iter.next().unwrap();
            assert!(field.ident.as_ref().is_some());
            assert_phantom_type_for("B", field);
            let field = fields_iter.next().unwrap();
            assert!(field.ident.as_ref().is_some());
            assert_phantom_type_for("C", field);
            let field = fields_iter.next().unwrap();
            assert!(field.ident.as_ref().is_some());
            assert_phantom_ref_for("'a", field);
            assert!(fields_iter.next().is_none());
        }

        #[test]
        fn phantom_data_for_struct_with_unnamed_fields() {
            let mut item_struct: syn::ItemStruct = parse_quote!(
                struct Foo<A, B, C, 'a>(A);
            );

            add_phantom_data_for_generic_params(&mut item_struct);

            assert_eq!(5, item_struct.fields.len());
            assert!(matches!(item_struct.fields, syn::Fields::Unnamed(_)));
            let mut fields_iter = item_struct.fields.iter();
            let field = fields_iter.next().unwrap();
            assert!(field.ident.is_none());
            assert_eq!("A", field.ty.to_token_stream().to_string());
            let field = fields_iter.next().unwrap();
            assert!(field.ident.is_none());
            assert_phantom_type_for("A", field);
            let field = fields_iter.next().unwrap();
            assert!(field.ident.is_none());
            assert_phantom_type_for("B", field);
            let field = fields_iter.next().unwrap();
            assert!(field.ident.is_none());
            assert_phantom_type_for("C", field);
            let field = fields_iter.next().unwrap();
            assert!(field.ident.is_none());
            assert_phantom_ref_for("'a", field);
            assert!(fields_iter.next().is_none());
        }

        #[test]
        fn phantom_data_for_unit_struct() {
            let mut item_struct: syn::ItemStruct = parse_quote!(
                struct Foo<A, 'a>;
            );

            add_phantom_data_for_generic_params(&mut item_struct);

            assert_eq!(2, item_struct.fields.len());
            assert!(matches!(item_struct.fields, syn::Fields::Unnamed(_)));
            let mut fields_iter = item_struct.fields.iter();
            let field = fields_iter.next().unwrap();
            assert!(field.ident.is_none());
            assert_phantom_type_for("A", field);
            let field = fields_iter.next().unwrap();
            assert!(field.ident.is_none());
            assert_phantom_ref_for("'a", field);
            assert!(fields_iter.next().is_none());
        }

        fn assert_phantom_type_for(ty: &str, actual_field: &syn::Field) {
            match &actual_field.ty {
                syn::Type::Path(type_path) => {
                    assert_eq!(
                        format!("::core::marker::PhantomData<{}>", ty),
                        type_path
                            .path
                            .to_token_stream()
                            .to_string()
                            .replace(' ', "")
                    );
                }
                _ => panic!(),
            }
        }

        fn assert_phantom_ref_for(expected_lifetime: &str, actual_field: &syn::Field) {
            match &actual_field.ty {
                syn::Type::Reference(type_ref) => {
                    let actual_lifetime = type_ref.lifetime.as_ref().expect("Expected lifetime");
                    assert_eq!(expected_lifetime, actual_lifetime.to_string().trim());

                    let ty = type_ref.elem.as_ref();
                    assert_eq!(
                        "::core::marker::PhantomData<()>",
                        ty.to_token_stream().to_string().replace(' ', "")
                    );
                }
                _ => panic!(),
            }
        }
    }
}
