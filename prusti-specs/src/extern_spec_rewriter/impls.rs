use crate::{span_overrider::SpanOverrider, specifications::common::NameGenerator};
use proc_macro2::TokenStream;
use quote::{quote, quote_spanned};
use syn::spanned::Spanned;
use super::common::*;


pub fn rewrite_extern_spec(item_impl: &mut syn::ItemImpl) -> syn::Result<TokenStream> {
    let new_struct = generate_new_struct(item_impl)?;
    let struct_ident = &new_struct.ident;
    let generic_args = rewrite_generics(&new_struct.generics);

    let struct_ty: syn::Type = parse_quote_spanned! {item_impl.span()=>
        #struct_ident #generic_args
    };

    let rewritten_item = rewrite_impl(item_impl, Box::from(struct_ty))?;

    Ok(quote_spanned! {item_impl.span()=>
        #new_struct
        #rewritten_item
    })
}

fn generate_new_struct(item_struct: &syn::ItemImpl) -> syn::Result<syn::ItemStruct> {
    let name_generator = NameGenerator::new();
    let struct_name = match name_generator.generate_struct_name(item_struct) {
        Ok(name) => name,
        Err(msg) => return Err(syn::Error::new(item_struct.span(), msg)),
    };
    let struct_ident = syn::Ident::new(&struct_name, item_struct.span());

    let mut new_struct: syn::ItemStruct = parse_quote_spanned! {item_struct.span()=>
        #[allow(non_camel_case_types)] struct #struct_ident {}
    };
    new_struct.generics = item_struct.generics.clone();

    add_phantom_data_for_generic_params(&mut new_struct);
    Ok(new_struct)
}

/// Rewrite all methods in an impl block to calls to the specified methods.
/// The result of this rewriting is then parsed in `ExternSpecResolver`.
fn rewrite_impl(impl_item: &mut syn::ItemImpl, new_ty: Box<syn::Type>) -> syn::Result<TokenStream> {
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

                let mut method_path: syn::ExprPath = parse_quote_spanned! {ident.span()=>
                    #item_ty :: #ident
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

    Ok(quote! {
        #impl_item
    })
}
