use crate::{span_overrider::SpanOverrider, specifications::common::NameGenerator};
use proc_macro2::{Ident, Span, TokenStream};
use quote::quote_spanned;
use syn::spanned::Spanned;
use super::common::*;
use syn::visit_mut::VisitMut;
use crate::SpecImplBlockGenerator;


pub fn rewrite_extern_spec(item_impl: &syn::ItemImpl) -> syn::Result<TokenStream> {
    let rewritten = rewrite_extern_spec_internal(item_impl)?;

    let new_struct = rewritten.generated_struct;
    let impls = rewritten.generated_impls;
    Ok(quote_spanned! {item_impl.span()=>
        #new_struct
        #(#impls),*
    })
}

struct RewrittenExternalSpecs {
    generated_struct: syn::ItemStruct,
    generated_impls: Vec<syn::ItemImpl>,
}

fn rewrite_extern_spec_internal(item_impl: &syn::ItemImpl) -> syn::Result<RewrittenExternalSpecs> {
    let new_struct = generate_new_struct(item_impl)?;
    let struct_ident = &new_struct.ident;
    let generic_args = rewrite_generics(&new_struct.generics);

    let struct_ty: syn::Type = parse_quote_spanned! {item_impl.span()=>
        #struct_ident #generic_args
    };

    if item_impl.trait_.is_some() {
        let mut rewritten_impl = item_impl.clone();

        rewrite_impl_2(&mut rewritten_impl, Box::from(struct_ty.clone()))?;
        rewritten_impl.trait_ = None;

        Ok(RewrittenExternalSpecs {
            generated_struct: new_struct,
            generated_impls: vec![rewritten_impl]
        })

    } else {
        let mut rewritten_item = item_impl.clone();
        rewrite_impl(&mut rewritten_item, Box::from(struct_ty))?;

        Ok(RewrittenExternalSpecs {
            generated_struct: new_struct,
            generated_impls: vec![rewritten_item]
        })
    }
}

fn generate_new_struct(item_impl: &syn::ItemImpl) -> syn::Result<syn::ItemStruct> {
    let name_generator = NameGenerator::new();
    let struct_name = match name_generator.generate_struct_name(item_impl) {
        Ok(name) => name,
        Err(msg) => return Err(syn::Error::new(item_impl.span(), msg)),
    };
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
fn rewrite_impl(impl_item: &mut syn::ItemImpl, new_ty: Box<syn::Type>) -> syn::Result<()> {
    let item_ty = &mut impl_item.self_ty;
    if let syn::Type::Path(type_path) = item_ty.as_mut() {
        for seg in type_path.path.segments.iter_mut() {
            if let syn::PathArguments::AngleBracketed(genargs) = &mut seg.arguments {
                genargs.colon2_token = Some(syn::token::Colon2::default());
            }
        }
    }

    for item in impl_item.items.iter_mut() {
        let item_span = item.span();
        match item {
            syn::ImplItem::Method(method) => {
                for attr in method.attrs.iter_mut() {
                    attr.tokens = rewrite_self(attr.tokens.clone());
                }

                let args = rewrite_method_inputs(item_ty, &mut method.sig.inputs);
                let ident = &method.sig.ident;

                method
                    .attrs
                    .push(parse_quote_spanned!(item_span=> #[prusti::extern_spec]));
                method
                    .attrs
                    .push(parse_quote_spanned!(item_span=> #[trusted]));
                method
                    .attrs
                    .push(parse_quote_spanned!(item_span=> #[allow(dead_code)]));

                let mut method_path: syn::ExprPath = parse_quote_spanned! {ident.span()=>
                    < #item_ty > :: #ident
                };

                // Fix the span
                syn::visit_mut::visit_expr_path_mut(
                    &mut SpanOverrider::new(ident.span()),
                    &mut method_path,
                );

                method.block = parse_quote_spanned! {item_span=>
                    {
                        #method_path (#args);
                        unimplemented!()
                    }
                };
            },
            syn::ImplItem::Type(ty) => {
                // ignore
            }
            _ => {
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


/// Rewrite all methods in an impl block to calls to the specified methods.
/// The result of this rewriting is then parsed in `ExternSpecResolver`.
fn rewrite_impl_2(impl_item: &mut syn::ItemImpl, new_ty: Box<syn::Type>) -> syn::Result<()> {
    let (_, trait_path, _) = &impl_item.clone().trait_.unwrap();


    let item_ty = &mut impl_item.self_ty;
    if let syn::Type::Path(type_path) = item_ty.as_mut() {
        for seg in type_path.path.segments.iter_mut() {
            if let syn::PathArguments::AngleBracketed(genargs) = &mut seg.arguments {
                genargs.colon2_token = Some(syn::token::Colon2::default());
            }
        }
    }

    for item in impl_item.items.iter_mut() {
        let item_span = item.span();
        match item {
            syn::ImplItem::Method(method) => {
                for attr in method.attrs.iter_mut() {
                    attr.tokens = rewrite_self(attr.tokens.clone());
                }

                let args = rewrite_method_inputs(item_ty, &mut method.sig.inputs);
                let ident = &method.sig.ident;

                method
                    .attrs
                    .push(parse_quote_spanned!(item_span=> #[prusti::extern_spec]));
                method
                    .attrs
                    .push(parse_quote_spanned!(item_span=> #[trusted]));
                method
                    .attrs
                    .push(parse_quote_spanned!(item_span=> #[allow(dead_code)]));

                let mut method_path: syn::ExprPath = parse_quote_spanned! {ident.span()=>
                    < #item_ty as #trait_path > :: #ident
                };

                // Fix the span
                syn::visit_mut::visit_expr_path_mut(
                    &mut SpanOverrider::new(ident.span()),
                    &mut method_path,
                );

                method.block = parse_quote_spanned! {item_span=>
                    {
                        #method_path (#args);
                        unimplemented!()
                    }
                };
            },
            syn::ImplItem::Type(ty) => {
                // ignore
            }
            _ => {
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

#[cfg(test)]
mod tests {
    use quote::ToTokens;
    use syn::parse_quote;
    use super::rewrite_extern_spec_internal;

    fn assert_eq_tokenizable<T: ToTokens, U: ToTokens>(actual: T, expected: U) {
        assert_eq!(actual.into_token_stream().to_string(), expected.into_token_stream().to_string());
    }

    mod plain_impl {
        use super::*;

        #[test]
        fn generated_struct(){
            let mut inp_impl: syn::ItemImpl = parse_quote!(
                impl<'a, const CONST: i32, T> MyStruct<'a, CONST, T> {}
            );

            let rewritten = rewrite_extern_spec_internal(&mut inp_impl).unwrap();

            let struct_ident = &rewritten.generated_struct.ident;
            let expected: syn::ItemStruct = parse_quote!{
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
                    #[prusti::extern_spec]
                    #[trusted]
                    #[allow(dead_code)]
                    fn foo(_self: &MyStruct) {
                        <MyStruct> :: foo(_self,);
                        unimplemented!()
                    }
                    #[prusti::extern_spec]
                    #[trusted]
                    #[allow(dead_code)]
                    fn bar(_self: &mut MyStruct) {
                        <MyStruct> :: bar(_self,);
                        unimplemented!()
                    }
                    #[prusti::extern_spec]
                    #[trusted]
                    #[allow(dead_code)]
                    fn baz(_self: MyStruct) {
                        <MyStruct> :: baz(_self,);
                        unimplemented!()
                    }
                }
            };

            assert_eq!(rewritten.generated_impls.len(), 1);
            assert_eq_tokenizable(rewritten.generated_impls[0].clone(), expected);
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
                    #[prusti::extern_spec]
                    #[trusted]
                    #[allow(dead_code)]
                    fn foo(_self: &MyStruct::<I,O, i32>, arg1: I, arg2: i32) -> O {
                        <MyStruct::<I,O,i32>> :: foo(_self, arg1, arg2, );
                        unimplemented!()
                    }
                }
            };

            assert_eq!(rewritten.generated_impls.len(), 1);
            assert_eq_tokenizable(rewritten.generated_impls[0].clone(), expected);
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
                    #[prusti::extern_spec]
                    #[trusted]
                    #[allow(dead_code)]
                    fn foo(_self: &mut MyStruct, arg: i32) -> i32 {
                        <MyStruct> :: foo(_self, arg, );
                        unimplemented!()
                    }
                }
            };

            assert_eq!(rewritten.generated_impls.len(), 1);
            assert_eq_tokenizable(rewritten.generated_impls[0].clone(), expected);
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
                    #[prusti::extern_spec]
                    #[trusted]
                    #[allow(dead_code)]
                    fn foo(_self: &mut MyStruct, arg: i32) -> i32 {
                        <MyStruct as MyTrait> :: foo(_self, arg, );
                        unimplemented!()
                    }
                }
            };

            assert_eq!(rewritten.generated_impls.len(), 1);
            assert_eq_tokenizable(rewritten.generated_impls[0].clone(), expected_impl);
        }

        #[test]
        #[ignore]
        // TODO
        fn associated_types() {
            let mut inp_impl: syn::ItemImpl = parse_quote!(
                impl MyTrait for MyStruct {
                    type Result = i32;
                    fn foo(&mut self, arg: i32) -> Self::Result;
                }
            );

            let rewritten = rewrite_extern_spec_internal(&mut inp_impl).unwrap();

            let newtype_ident = &rewritten.generated_struct.ident;
            let expected_impl: syn::ItemImpl = parse_quote! {
                impl #newtype_ident <> {
                    #[prusti::extern_spec]
                    #[trusted]
                    #[allow(dead_code)]
                    fn foo(_self: &mut MyStruct, arg: i32) -> i32 {
                        <MyStruct as MyTrait<Result = i32>> :: foo(_self, arg, );
                        unimplemented!()
                    }
                }
            };

            assert_eq!(rewritten.generated_impls.len(), 1);
            assert_eq_tokenizable(rewritten.generated_impls[0].clone(), expected_impl);
        }

        #[test]
        #[ignore]
        // TODO
        fn generics_not_supported() {
            let mut inp_impl: syn::ItemImpl = parse_quote!(
                impl MyTrait<I, O, i32> for MyStruct {
                    fn foo(&mut self, arg1: I, arg2: i32) -> O;
                }
            );

            let rewritten = rewrite_extern_spec_internal(&mut inp_impl);

            assert!(rewritten.is_err());
            // TODO: Check for conrete error
        }

    }

}