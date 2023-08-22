use super::common::*;
use crate::{
    is_predicate_macro, specifications::common::generate_struct_name, ExternSpecKind, SPECS_VERSION,
};
use proc_macro2::TokenStream;
use quote::quote_spanned;
use syn::{parse_quote_spanned, spanned::Spanned};

pub fn rewrite_extern_spec(item_impl: &syn::ItemImpl) -> syn::Result<TokenStream> {
    let rewritten = rewrite_extern_spec_internal(item_impl)?;

    let new_struct = rewritten.generated_struct;
    let new_impl = rewritten.generated_impl;
    Ok(quote_spanned! {item_impl.span()=>
        #[prusti::specs_version = #SPECS_VERSION]
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
        #[allow(non_camel_case_types)] struct #struct_ident;
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

    let mut rewritten_items = Vec::new();
    for item in impl_item.items.iter_mut() {
        match item {
            syn::ImplItem::Type(_) => {
                return Err(syn::Error::new(
                    item.span(),
                    "Associated types in external impl specs should not be declared",
                ));
            }
            syn::ImplItem::Method(method) => {
                check_is_stub(&method.block)?;

                let (rewritten_method, spec_items) = generate_extern_spec_method_stub(
                    method,
                    item_ty,
                    None,
                    ExternSpecKind::InherentImpl,
                )?;

                rewritten_items.extend(spec_items.into_iter().map(syn::ImplItem::Method));
                rewritten_items.push(syn::ImplItem::Method(rewritten_method));
            }
            syn::ImplItem::Macro(makro) if is_predicate_macro(makro) => {
                return Err(syn::Error::new(
                    makro.span(),
                    "Can not declare abstract predicate in external spec",
                ));
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
    impl_item.self_ty = new_ty;
    impl_item.items = rewritten_items;

    Ok(())
}

fn rewrite_trait_impl(
    impl_item: syn::ItemImpl,
    new_ty: Box<syn::Type>,
) -> syn::Result<syn::ItemImpl> {
    let item_ty = impl_item.self_ty.clone();

    // Create new impl
    let mut new_impl = impl_item.clone();
    new_impl.self_ty = new_ty;
    new_impl.trait_ = None;
    new_impl.items.clear();

    let item_trait_path = impl_item.trait_.as_ref().unwrap().1.clone();
    let item_trait_typath: syn::TypePath =
        parse_quote_spanned! {item_trait_path.span()=> #item_trait_path };

    // TODO: reduce duplication with rewrite_plain_impl
    for item in impl_item.items.into_iter() {
        match item {
            syn::ImplItem::Type(_) => {
                return Err(syn::Error::new(
                    item.span(),
                    "Associated types in external impl specs should not be declared",
                ));
            }
            syn::ImplItem::Method(method) => {
                check_is_stub(&method.block)?;

                let (rewritten_method, spec_items) = generate_extern_spec_method_stub(
                    &method,
                    &item_ty,
                    Some(&item_trait_typath),
                    ExternSpecKind::TraitImpl,
                )?;

                new_impl
                    .items
                    .extend(spec_items.into_iter().map(syn::ImplItem::Method));
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

#[cfg(test)]
mod tests {
    use super::rewrite_extern_spec_internal;
    use quote::ToTokens;
    use syn::parse_quote;

    #[allow(dead_code)]
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
            let inp_impl: syn::ItemImpl = parse_quote!(
                impl<'a, const CONST: i32, T> MyStruct<'a, CONST, T> {}
            );

            let rewritten = rewrite_extern_spec_internal(&inp_impl).unwrap();

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
            let inp_impl: syn::ItemImpl = parse_quote!(
                impl MyStruct {
                    fn foo(&self);
                    fn bar(&mut self);
                    fn baz(self);
                }
            );

            let rewritten = rewrite_extern_spec_internal(&inp_impl).unwrap();

            let newtype_ident = &rewritten.generated_struct.ident;
            let expected: syn::ItemImpl = parse_quote! {
                impl #newtype_ident <> {
                    #[prusti::extern_spec = "inherent_impl"]
                    #[allow(unused, dead_code)]
                    #[prusti::trusted]
                    fn foo(_self: &MyStruct) {
                        <MyStruct> :: foo :: <>(_self)
                    }
                    #[prusti::extern_spec = "inherent_impl"]
                    #[allow(unused, dead_code)]
                    #[prusti::trusted]
                    fn bar(_self: &mut MyStruct) {
                        <MyStruct> :: bar :: <>(_self)
                    }
                    #[prusti::extern_spec = "inherent_impl"]
                    #[allow(unused, dead_code)]
                    #[prusti::trusted]
                    fn baz(_self: MyStruct) {
                        <MyStruct> :: baz :: <>(_self)
                    }
                }
            };

            assert_eq_tokenizable(rewritten.generated_impl.clone(), expected);
        }

        #[test]
        fn impl_generics() {
            let inp_impl: syn::ItemImpl = parse_quote!(
                impl<I, O> MyStruct<I, O, i32> {
                    fn foo(&self, arg1: I, arg2: i32) -> O;
                }
            );

            let rewritten = rewrite_extern_spec_internal(&inp_impl).unwrap();

            let newtype_ident = &rewritten.generated_struct.ident;
            let expected: syn::ItemImpl = parse_quote! {
                impl<I, O> #newtype_ident<I, O> {
                    #[prusti::extern_spec = "inherent_impl"]
                    #[allow(unused, dead_code)]
                    #[prusti::trusted]
                    fn foo(_self: &MyStruct::<I,O, i32>, arg1: I, arg2: i32) -> O {
                        <MyStruct::<I,O,i32>> :: foo :: <>(_self, arg1, arg2)
                    }
                }
            };

            assert_eq_tokenizable(rewritten.generated_impl.clone(), expected);
        }

        #[test]
        fn impl_forwarded_generics() {
            let inp_impl: syn::ItemImpl = parse_quote!(
                impl MyStruct {
                    fn foo<T: Copy>(&self) -> bool;
                }
            );

            let rewritten = rewrite_extern_spec_internal(&inp_impl).unwrap();

            let newtype_ident = &rewritten.generated_struct.ident;
            let expected: syn::ItemImpl = parse_quote! {
                impl #newtype_ident <> {
                    #[prusti::extern_spec = "inherent_impl"]
                    #[allow(unused, dead_code)]
                    #[prusti::trusted]
                    fn foo<T: Copy>(_self: &MyStruct) -> bool {
                        <MyStruct> :: foo :: <T>(_self)
                    }
                }
            };

            assert_eq_tokenizable(rewritten.generated_impl.clone(), expected);
        }
    }

    mod trait_impl {
        use super::*;

        #[test]
        fn associated_types() {
            let inp_impl: syn::ItemImpl = parse_quote!(
                impl MyTrait for MyStruct {
                    fn foo(&mut self) -> Self::Result;
                }
            );

            let rewritten = rewrite_extern_spec_internal(&inp_impl).unwrap();

            let newtype_ident = &rewritten.generated_struct.ident;
            let expected_impl: syn::ItemImpl = parse_quote! {
                impl #newtype_ident <> {
                    #[prusti::extern_spec = "trait_impl"]
                    #[allow(unused, dead_code)]
                    #[prusti::trusted]
                    fn foo(_self: &mut MyStruct) -> <MyStruct as MyTrait> :: Result {
                        <MyStruct as MyTrait> :: foo :: <>(_self)
                    }
                }
            };

            assert_eq_tokenizable(rewritten.generated_impl.clone(), expected_impl);
        }

        #[test]
        fn generic_trait() {
            let inp_impl: syn::ItemImpl = parse_quote!(
                impl MyTrait<Foo> for MyStruct {
                    fn foo(&mut self, arg1: Foo);
                }
            );

            let rewritten = rewrite_extern_spec_internal(&inp_impl).unwrap();

            let newtype_ident = &rewritten.generated_struct.ident;
            let expected_impl: syn::ItemImpl = parse_quote! {
                impl #newtype_ident <> {
                    #[prusti::extern_spec = "trait_impl"]
                    #[allow(unused, dead_code)]
                    #[prusti::trusted]
                    fn foo(_self: &mut MyStruct, arg1: Foo) {
                        <MyStruct as MyTrait<Foo>> :: foo :: <>(_self, arg1)
                    }
                }
            };

            assert_eq_tokenizable(rewritten.generated_impl.clone(), expected_impl);
        }

        #[test]
        fn generic_blanket_impl() {
            let inp_impl: syn::ItemImpl = parse_quote!(
                impl<I> MyTrait<I> for MyStruct {
                    fn foo(&mut self, arg1: I);
                }
            );

            let rewritten = rewrite_extern_spec_internal(&inp_impl).unwrap();

            let newtype_ident = &rewritten.generated_struct.ident;
            let expected_impl: syn::ItemImpl = parse_quote! {
                impl<I> #newtype_ident <I> {
                    #[prusti::extern_spec = "trait_impl"]
                    #[allow(unused, dead_code)]
                    #[prusti::trusted]
                    fn foo(_self: &mut MyStruct, arg1: I) {
                        <MyStruct as MyTrait<I>> :: foo :: <>(_self, arg1)
                    }
                }
            };

            assert_eq_tokenizable(rewritten.generated_impl.clone(), expected_impl);
        }
    }
}
