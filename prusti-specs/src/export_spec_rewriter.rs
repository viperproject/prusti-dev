use proc_macro2::{TokenStream, TokenTree};
use quote::{quote, quote_spanned, ToTokens};
use syn::spanned::Spanned;

// generate a hash of path
fn hash_path(path: syn::Path) -> u64 {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    println!("path to hash: {:?} \n", &path);
    let mut hasher = DefaultHasher::new();
    path.hash(&mut hasher);
    hasher.finish()
}

// generate a macro identifier with given path in this format:
// {last_segment in path}_{hash(path)}
fn generate_macro_ident(path: syn::Path) -> syn::Ident {
    let ident = path.segments.last().unwrap().ident.to_owned();
    syn::Ident::new(&format!("{}_{}", ident, hash_path(path)), ident.span())
}

// generate macro for export based on given identifier and item
fn generate_macro_for_export<T: ToTokens>(
    macro_ident: syn::Ident,
    macro_content: T,
) -> TokenStream {
    quote_spanned! {macro_ident.span() =>
        #[macro_export]
        macro_rules! #macro_ident {
            () => {
                #macro_content
            };
        }
    }
}

// helper macro for getting the value of attribute with given name in an item
// attribute must be in this format: #[name(value)]
// if attribute is not present then path is not changed
// @param: $path_mut_ref must be a mutable reference of Path, i.e. &mut syn::Path / mut syn::Path
macro_rules! get_prusti_path_in_attr {
    ($item: ident, $attr_str: literal, $path_mut_ref: ident) => {
        if let Some(export_path_attr) = $item.attrs.iter().find(|attr| {
            attr.path.segments.len() == 2
                && &attr.path.segments.last().unwrap().ident.to_string() == $attr_str
        }) {
            for tt in export_path_attr.tokens.to_owned() {
                if let TokenTree::Group(group) = tt {
                    $path_mut_ref = syn::parse2(group.stream()).unwrap();
                }
            }
        }
    };
}

// expand the module path recorded when traversing AST
fn expand_mod_path_in_macro(
    path: &syn::Path,
    mut tokens: TokenStream,
    uses_same_level: &TokenStream,
) -> TokenStream {
    match &path.segments.empty_or_trailing() {
        true => tokens,
        false => {
            for seg in path.segments.to_owned().into_iter().rev() {
                tokens = quote!(
                    mod #seg {
                        #uses_same_level
                        #tokens
                    }
                );
            }
            tokens
        }
    }
}

fn expand_type_path_in_macro(
    path: &syn::Path,
    tokens: TokenStream,
    uses_same_level: &TokenStream,
    type_path: &syn::Path,
) -> TokenStream {
    let type_path_macro_ident = generate_macro_ident(type_path.to_owned());
    match type_path.segments.empty_or_trailing() {
        true => expand_mod_path_in_macro(path, tokens, uses_same_level),
        false => expand_mod_path_in_macro(
            path,
            quote!(
                $crate::#type_path_macro_ident!();
                #tokens
            ),
            uses_same_level,
        ),
    }
}

pub fn rewrite_export_spec(path: &syn::Path, item: &syn::Item) -> syn::Result<TokenStream> {
    let mut macros_tokens = TokenStream::new();
    let mod_path = syn::Path {
        leading_colon: None,
        segments: syn::punctuated::Punctuated::new(),
    };
    match item {
        syn::Item::Fn(item_fn) => {
            rewrite_fn(
                path,
                mod_path,
                item_fn,
                &mut macros_tokens,
                &TokenStream::new(),
            );
        }
        syn::Item::Mod(item_mod) => {
            // println!("{}", );
            rewrite_mod(
                path,
                mod_path,
                item_mod,
                &mut macros_tokens,
                &TokenStream::new(),
            )?;
        }
        syn::Item::Impl(item_impl) => {
            rewrite_impl(
                path,
                mod_path,
                item_impl,
                &mut macros_tokens,
                &TokenStream::new(),
            )?;
        }
        syn::Item::Struct(item_struct) => {
            rewrite_struct(
                item_struct,
                mod_path,
                &mut macros_tokens,
                &TokenStream::new(),
            );
        }
        _ => {
            unimplemented!();
        }
    };
    Ok(macros_tokens)
}

fn rewrite_mod(
    export_path: &syn::Path,
    mut mod_path: syn::Path,
    item_mod: &syn::ItemMod,
    macros_tokens: &mut TokenStream,
    uses_same_level: &TokenStream,
) -> syn::Result<()> {
    let mut path = export_path.to_owned();
    let macro_content = expand_mod_path_in_macro(&mod_path, quote!(#item_mod), uses_same_level);
    path.segments.push(syn::PathSegment {
        ident: item_mod.ident.clone(),
        arguments: syn::PathArguments::None,
    });

    mod_path.segments.push(syn::PathSegment {
        ident: item_mod.ident.clone(),
        arguments: syn::PathArguments::None,
    });

    let mut uses = TokenStream::new();

    for item in item_mod.content.as_ref().unwrap().1.iter() {
        let mod_path = mod_path.to_owned();
        match item {
            syn::Item::Fn(item_fn) => {
                rewrite_fn(&path, mod_path, item_fn, macros_tokens, &uses);
            }
            syn::Item::Impl(item_impl) => {
                rewrite_impl(&path, mod_path, item_impl, macros_tokens, &uses)?;
            }
            syn::Item::Mod(item_mod) => {
                rewrite_mod(&path, mod_path, item_mod, macros_tokens, &uses)?;
            }
            syn::Item::Struct(item_struct) => {
                rewrite_struct(item_struct, mod_path, macros_tokens, &uses);
            }
            syn::Item::Use(item_use) => {
                uses.extend(quote!(#item_use));
            }
            _ => {
                return Err(syn::Error::new(
                    item.span(),
                    "expected a mod/fn/impl".to_string(),
                ));
            }
        }
    }

    get_prusti_path_in_attr!(item_mod, "export_path", path);
    let macro_ident = generate_macro_ident(path);
    macros_tokens.extend(generate_macro_for_export(macro_ident, macro_content));
    Ok(())
}

fn rewrite_fn(
    export_path: &syn::Path,
    mod_path: syn::Path,
    item_fn: &syn::ItemFn,
    macros_tokens: &mut TokenStream,
    uses_same_level: &TokenStream,
) {
    let mut path = export_path.to_owned();
    let macro_content = expand_mod_path_in_macro(&mod_path, quote!(#item_fn), uses_same_level);
    let ident = item_fn.sig.ident.to_owned();
    path.segments.push(syn::PathSegment {
        ident: ident,
        arguments: syn::PathArguments::None,
    });

    get_prusti_path_in_attr!(item_fn, "export_path", path);
    let macro_ident = generate_macro_ident(path);
    macros_tokens.extend(generate_macro_for_export(macro_ident, macro_content));
}

fn rewrite_struct(
    item_struct: &syn::ItemStruct,
    mod_path: syn::Path,
    macros_tokens: &mut TokenStream,
    uses_same_level: &TokenStream,
) {
    let struct_ident = &item_struct.ident;
    let generics = &item_struct.generics;
    let struct_path: syn::Path = parse_quote_spanned!(item_struct.span() =>
        #struct_ident #generics
    );
    let macro_content = expand_mod_path_in_macro(&mod_path, quote!(#item_struct), uses_same_level);
    let macro_ident = generate_macro_ident(struct_path);
    macros_tokens.extend(generate_macro_for_export(macro_ident, macro_content));
}

fn rewrite_impl(
    export_path: &syn::Path,
    mod_path: syn::Path,
    item_impl: &syn::ItemImpl,
    macros_tokens: &mut TokenStream,
    uses_same_level: &TokenStream,
) -> syn::Result<()> {
    let mut path = export_path.to_owned();
    let mut type_path = syn::Path {
        leading_colon: None,
        segments: syn::punctuated::Punctuated::new(),
    };
    get_prusti_path_in_attr!(item_impl, "type_path", type_path);

    let macro_content =
        expand_type_path_in_macro(&mod_path, quote!(#item_impl), uses_same_level, &type_path);
    let item_ty = &item_impl.self_ty;
    if let syn::Type::Path(type_path) = item_ty.as_ref() {
        path.segments.extend(type_path.path.segments.clone());
    }

    // println!("path in impl: {:?} \n", path);
    for item in item_impl.items.iter() {
        match item {
            syn::ImplItem::Method(item_method) => {
                rewrite_method(&path, item_method, &mod_path, macros_tokens);
            }
            _ => {
                return Err(syn::Error::new(
                    item.span(),
                    "expected a method".to_string(),
                ));
            }
        }
    }

    get_prusti_path_in_attr!(item_impl, "export_path", path);
    parse_valid_export_type(&mut path);
    let macro_ident = generate_macro_ident(path);
    macros_tokens.extend(generate_macro_for_export(macro_ident, macro_content));
    Ok(())
}

fn rewrite_method(
    path: &syn::Path,
    item_method: &syn::ImplItemMethod,
    impl_mod_path: &syn::Path,
    macros_tokens: &mut TokenStream,
) {
    let mut path = path.to_owned();

    let mut type_path = syn::Path {
        leading_colon: None,
        segments: syn::punctuated::Punctuated::new(),
    };

    get_prusti_path_in_attr!(item_method, "type_path", type_path);
    let macro_content = expand_type_path_in_macro(
        impl_mod_path,
        quote!(
            impl #type_path {
                #item_method
            }
        ),
        &TokenStream::new(),
        &type_path,
    );
    path.segments.push(syn::PathSegment {
        ident: item_method.sig.ident.clone(),
        arguments: syn::PathArguments::None,
    });

    get_prusti_path_in_attr!(item_method, "export_path", path);
    parse_valid_export_type(&mut path);
    let macro_ident = generate_macro_ident(path);
    macros_tokens.extend(generate_macro_for_export(macro_ident, macro_content));
}

pub fn parse_valid_export(attr: TokenStream) -> syn::Result<syn::Path> {
    let span = attr.span();
    match attr.is_empty() {
        true => Err(syn::Error::new(span, "export path must be non-empty")),
        false => match attr.to_string().trim() == "::" {
            true => Ok(syn::Path {
                leading_colon: None,
                segments: syn::punctuated::Punctuated::new(),
            }),
            false => syn::parse2(attr).map_err(|_e| syn::Error::new(span, "invalid export path")),
        },
    }
}

fn parse_valid_export_type(ty_path: &mut syn::Path) {
    for seg in &mut ty_path.segments {
        if let syn::PathArguments::AngleBracketed(_) = &mut seg.arguments {
            seg.arguments = syn::PathArguments::None;
        }
    }
}