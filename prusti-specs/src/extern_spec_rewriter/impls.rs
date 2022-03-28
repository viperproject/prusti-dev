use crate::{ExternSpecKind, span_overrider::SpanOverrider, specifications::common::generate_struct_name};
use proc_macro2::TokenStream;
use quote::quote_spanned;
use syn::spanned::Spanned;
use super::common::*;

pub fn rewrite_extern_spec(item_impl: &syn::ItemImpl) -> syn::Result<TokenStream> {
    let rewritten = rewrite_extern_spec_internal(item_impl)?;

    let new_struct = rewritten.generated_struct;
    let new_impl = rewritten.generated_impl;
    Ok(quote_spanned! {item_impl.span()=>
        #new_struct
        #new_impl
    })
}

struct RewrittenExternalSpecs {
    generated_struct: syn::ItemStruct,
    generated_impl: syn::ItemImpl,
}

fn rewrite_extern_spec_internal(item_impl: &syn::ItemImpl) -> syn::Result<RewrittenExternalSpecs> {
    let new_struct = generate_new_struct(item_impl)?;
    let struct_ident = &new_struct.ident;
    let generic_args = rewrite_generics(&new_struct.generics);

    let struct_ty: syn::Type = parse_quote_spanned! {item_impl.span()=>
        #struct_ident #generic_args
    };

    if item_impl.trait_.is_some() {
        let (_, trait_path, _) = item_impl.trait_.as_ref().unwrap();
        if has_generic_arguments(trait_path) {
            return Err(syn::Error::new(
                item_impl.generics.params.span(),
                "Generics for extern trait impls are not supported",
            ));
        }

        let rewritten_impl = rewrite_trait_impl(item_impl.clone(), Box::from(struct_ty))?;

        Ok(RewrittenExternalSpecs {
            generated_struct: new_struct,
            generated_impl: rewritten_impl,
        })
    } else {
        let mut rewritten_item = item_impl.clone();
        rewrite_plain_impl(&mut rewritten_item, Box::from(struct_ty))?;

        Ok(RewrittenExternalSpecs {
            generated_struct: new_struct,
            generated_impl: rewritten_item,
        })
    }
}

fn generate_new_struct(item_impl: &syn::ItemImpl) -> syn::Result<syn::ItemStruct> {
    let struct_name = generate_struct_name(item_impl);
    let struct_ident = syn::Ident::new(&struct_name, item_impl.span());

    let mut new_struct: syn::ItemStruct = parse_quote_spanned! {item_impl.span()=>
        #[allow(non_camel_case_types)] struct #struct_ident {}
    };
    new_struct.generics = item_impl.generics.clone();

    add_phantom_data_for_generic_params(&mut new_struct);
    Ok(new_struct)
}

/// Rewrite all methods in an impl block to calls to the specified methods.
/// The result of this rewriting is then parsed in `ExternSpecResolver`.
fn rewrite_plain_impl(impl_item: &mut syn::ItemImpl, new_ty: Box<syn::Type>) -> syn::Result<()> {
    let item_ty = &mut impl_item.self_ty;
    if let syn::Type::Path(type_path) = item_ty.as_mut() {
        for seg in type_path.path.segments.iter_mut() {
            if let syn::PathArguments::AngleBracketed(genargs) = &mut seg.arguments {
                genargs.colon2_token = Some(<syn::Token![::]>::default());
            }
        }
    }

    for item in impl_item.items.iter_mut() {
        match item {
            syn::ImplItem::Type(_) => {
                return Err(syn::Error::new(
                    item.span(),
                    "Associated types in external impl specs should not be declared",
                ));
            }
            syn::ImplItem::Method(method) => rewrite_method(
                method,
                item_ty,
                None,
                ExternSpecKind::InherentImpl,
            ),
            _ => {
                // TODO: this case also covers methods with `pub` modifier
                // show a more meaningful message if that is the case
                return Err(syn::Error::new(
                    item.span(),
                    "expected a method".to_string(),
                ));
            }
        }
    }
    impl_item.self_ty = new_ty;

    Ok(())
}

fn rewrite_trait_impl(
    impl_item: syn::ItemImpl,
    new_ty: Box<syn::Type>,
) -> syn::Result<syn::ItemImpl> {
    let item_ty = impl_item.self_ty.clone();
    let item_ty_path = if let syn::Type::Path(ref type_path) = *item_ty {
        type_path.clone()
    } else {
        unreachable!("expected type path in extern spec trait impl");
    };

    // Create new impl
    let mut new_impl = impl_item.clone();
    new_impl.self_ty = new_ty;
    new_impl.trait_ = None;
    new_impl.items.clear();

    let item_trait_path = impl_item.trait_.as_ref().unwrap().1.clone();
    let item_trait_typath = parse_quote_spanned! {item_trait_path.span()=> #item_trait_path };
    let mut rewriter = AssociatedTypeRewriter::new(
        &item_ty_path,
        &item_trait_typath,
    );

    // TODO: reduce duplication with rewrite_plain_impl
    for item in impl_item.items.iter() {
        match item {
            syn::ImplItem::Type(_) => {
                return Err(syn::Error::new(
                    item.span(),
                    "Associated types in external impl specs should not be declared",
                ));
            }
            syn::ImplItem::Method(method) => {
                let (_, trait_path, _) = &impl_item.trait_.as_ref().unwrap();

                let mut rewritten_method = method.clone();
                rewrite_method(
                    &mut rewritten_method,
                    &item_ty,
                    Some(trait_path),
                    ExternSpecKind::TraitImpl,
                );

                // Rewrite occurences of associated types in method signature
                rewriter.rewrite_method_sig(&mut rewritten_method.sig);

                new_impl.items.push(syn::ImplItem::Method(rewritten_method));
            }
            _ => {
                // TODO: this case also covers methods with `pub` modifier
                // show a more meaningful message if that is the case
                return Err(syn::Error::new(
                    item.span(),
                    "expected a method".to_string(),
                ));
            }
        }
    }

    Ok(new_impl)
}

fn rewrite_method(
    method: &mut syn::ImplItemMethod,
    original_ty: &syn::Type,
    as_ty: Option<&syn::Path>,
    extern_spec_kind: ExternSpecKind,
) {
    let span = method.span();

    for attr in method.attrs.iter_mut() {
        attr.tokens = rewrite_self(attr.tokens.clone());
    }

    let args = rewrite_method_inputs(original_ty, &mut method.sig.inputs);
    let ident = &method.sig.ident;

    let extern_spec_kind_string: String = extern_spec_kind.into();
    method
        .attrs
        .push(parse_quote_spanned!(span=> #[prusti::extern_spec = #extern_spec_kind_string]));
    method.attrs.push(parse_quote_spanned!(span=> #[trusted]));
    method
        .attrs
        .push(parse_quote_spanned!(span=> #[allow(dead_code)]));

    let mut method_path: syn::ExprPath = match as_ty {
        Some(type_path) => parse_quote_spanned! {ident.span()=>
            < #original_ty as #type_path > :: #ident
        },
        None => parse_quote_spanned! {ident.span()=>
            < #original_ty > :: #ident
        },
    };

    // Fix the span
    syn::visit_mut::visit_expr_path_mut(&mut SpanOverrider::new(ident.span()), &mut method_path);

    method.block = parse_quote_spanned! {span=>
        {
            #method_path (#args);
            unimplemented!()
        }
    };
}

fn has_generic_arguments(path: &syn::Path) -> bool {
    for seg in path.segments.iter() {
        if let syn::PathArguments::AngleBracketed(args) = &seg.arguments {
            if !args.args.is_empty() {
                return true;
            }
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::rewrite_extern_spec_internal;
    use quote::ToTokens;
    use syn::parse_quote;

    fn assert_eq_tokenizable<T: ToTokens, U: ToTokens>(actual: T, expected: U) {
        assert_eq!(
            actual.into_token_stream().to_string(),
            expected.into_token_stream().to_string()
        );
    }

    mod plain_impl {
        use super::*;

        #[test]
        fn generated_struct() {
            let mut inp_impl: syn::ItemImpl = parse_quote!(
                impl<'a, const CONST: i32, T> MyStruct<'a, CONST, T> {}
            );

            let rewritten = rewrite_extern_spec_internal(&mut inp_impl).unwrap();

            let struct_ident = &rewritten.generated_struct.ident;
            let expected: syn::ItemStruct = parse_quote! {
                #[allow (non_camel_case_types)]
                struct #struct_ident<'a, const CONST: i32, T> (
                    &'a ::core::marker::PhantomData<()>,
                    ::core::marker::PhantomData<T>
                );
            };

            assert_eq_tokenizable(rewritten.generated_struct, expected);
        }

        #[test]
        fn impl_no_generics() {
            let mut inp_impl: syn::ItemImpl = parse_quote!(
                impl MyStruct {
                    fn foo(&self);
                    fn bar(&mut self);
                    fn baz(self);
                }
            );

            let rewritten = rewrite_extern_spec_internal(&mut inp_impl).unwrap();

            let newtype_ident = &rewritten.generated_struct.ident;
            let expected: syn::ItemImpl = parse_quote! {
                impl #newtype_ident <> {
                    #[prusti::extern_spec = "inherent_impl"]
                    #[trusted]
                    #[allow(dead_code)]
                    fn foo(_self: &MyStruct) {
                        <MyStruct> :: foo(_self,);
                        unimplemented!()
                    }
                    #[prusti::extern_spec = "inherent_impl"]
                    #[trusted]
                    #[allow(dead_code)]
                    fn bar(_self: &mut MyStruct) {
                        <MyStruct> :: bar(_self,);
                        unimplemented!()
                    }
                    #[prusti::extern_spec = "inherent_impl"]
                    #[trusted]
                    #[allow(dead_code)]
                    fn baz(_self: MyStruct) {
                        <MyStruct> :: baz(_self,);
                        unimplemented!()
                    }
                }
            };

            assert_eq_tokenizable(rewritten.generated_impl.clone(), expected);
        }

        #[test]
        fn impl_generics() {
            let mut inp_impl: syn::ItemImpl = parse_quote!(
                impl<I, O> MyStruct<I, O, i32> {
                    fn foo(&self, arg1: I, arg2: i32) -> O;
                }
            );

            let rewritten = rewrite_extern_spec_internal(&mut inp_impl).unwrap();

            let newtype_ident = &rewritten.generated_struct.ident;
            let expected: syn::ItemImpl = parse_quote! {
                impl<I, O> #newtype_ident<I, O> {
                    #[prusti::extern_spec = "inherent_impl"]
                    #[trusted]
                    #[allow(dead_code)]
                    fn foo(_self: &MyStruct::<I,O, i32>, arg1: I, arg2: i32) -> O {
                        <MyStruct::<I,O,i32>> :: foo(_self, arg1, arg2, );
                        unimplemented!()
                    }
                }
            };

            assert_eq_tokenizable(rewritten.generated_impl.clone(), expected);
        }

        #[test]
        fn impl_specs() {
            let mut inp_impl: syn::ItemImpl = parse_quote!(
                impl MyStruct {
                    #[requires(self.foo > 42 && arg < 50)]
                    #[ensures(self.foo > 50 && result >= 100)]
                    fn foo(&mut self, arg: i32) -> i32;
                }
            );

            let rewritten = rewrite_extern_spec_internal(&mut inp_impl).unwrap();

            let newtype_ident = &rewritten.generated_struct.ident;
            let expected: syn::ItemImpl = parse_quote! {
                impl #newtype_ident <> {
                    #[requires(_self.foo > 42 && arg < 50)]
                    #[ensures(_self.foo > 50 && result >= 100)]
                    #[prusti::extern_spec = "inherent_impl"]
                    #[trusted]
                    #[allow(dead_code)]
                    fn foo(_self: &mut MyStruct, arg: i32) -> i32 {
                        <MyStruct> :: foo(_self, arg, );
                        unimplemented!()
                    }
                }
            };

            assert_eq_tokenizable(rewritten.generated_impl.clone(), expected);
        }
    }

    mod trait_impl {
        use super::*;

        #[test]
        fn no_generics_with_specs() {
            let mut inp_impl: syn::ItemImpl = parse_quote!(
                impl MyTrait for MyStruct {
                    #[requires(self.foo > 42 && arg < 50)]
                    #[ensures(self.foo > 50 && result >= 100)]
                    fn foo(&mut self, arg: i32) -> i32;
                }
            );

            let rewritten = rewrite_extern_spec_internal(&mut inp_impl).unwrap();

            let newtype_ident = &rewritten.generated_struct.ident;
            let expected_impl: syn::ItemImpl = parse_quote! {
                impl #newtype_ident <> {
                    #[requires(_self.foo > 42 && arg < 50)]
                    #[ensures(_self.foo > 50 && result >= 100)]
                    #[prusti::extern_spec = "trait_impl"]
                    #[trusted]
                    #[allow(dead_code)]
                    fn foo(_self: &mut MyStruct, arg: i32) -> i32 {
                        <MyStruct as MyTrait> :: foo(_self, arg, );
                        unimplemented!()
                    }
                }
            };

            assert_eq_tokenizable(rewritten.generated_impl.clone(), expected_impl);
        }

        #[test]
        fn associated_types() {
            let mut inp_impl: syn::ItemImpl = parse_quote!(
                impl MyTrait for MyStruct {
                    fn foo(&mut self) -> Self::Result;
                }
            );

            let rewritten = rewrite_extern_spec_internal(&mut inp_impl).unwrap();

            let newtype_ident = &rewritten.generated_struct.ident;
            let expected_impl: syn::ItemImpl = parse_quote! {
                impl #newtype_ident <> {
                    #[prusti::extern_spec = "trait_impl"]
                    #[trusted]
                    #[allow(dead_code)]
                    fn foo(_self: &mut MyStruct) -> <MyStruct as MyTrait> :: Result {
                        <MyStruct as MyTrait> :: foo(_self, );
                        unimplemented!()
                    }
                }
            };

            assert_eq_tokenizable(rewritten.generated_impl.clone(), expected_impl);
        }

        #[test]
        fn generics_not_supported() {
            let mut inp_impl: syn::ItemImpl = parse_quote!(
                impl MyTrait<I> for MyStruct {
                    fn foo(&mut self, arg1: I);
                }
            );

            let rewritten = rewrite_extern_spec_internal(&mut inp_impl);

            assert!(rewritten.is_err());
        }
    }
}
