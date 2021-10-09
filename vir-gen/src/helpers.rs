fn append(s: &mut String, iter: impl Iterator<Item = char>) {
    for c in iter {
        s.push(c);
    }
}

/// Converts `CamelCase` to `camel_case`
pub fn method_name_from_camel(ident: &syn::Ident) -> syn::Ident {
    prefixed_method_name_from_camel("", ident)
}

/// Converts `CamelCase` to `<prefix>camel_case`
pub fn prefixed_method_name_from_camel(prefix: &str, ident: &syn::Ident) -> syn::Ident {
    let string = ident.to_string();
    let mut iterator = string.chars();
    let mut new_ident = String::from(prefix);
    append(&mut new_ident, iterator.next().unwrap().to_lowercase());
    for c in iterator {
        if c.is_uppercase() {
            new_ident.push('_');
            append(&mut new_ident, c.to_lowercase());
        } else {
            new_ident.push(c);
        }
    }
    let new_ident = match new_ident.as_ref() {
        "struct" | "enum" | "union" | "type" => {
            new_ident.push('_');
            new_ident
        }
        _ => new_ident,
    };
    syn::Ident::new(&new_ident, ident.span())
}

pub fn append_ident(ident: &syn::Ident, suffix: &str) -> syn::Ident {
    let name = format!("{}{}", ident, suffix);
    syn::Ident::new(&name, ident.span())
}

/// If `ty` is `Box<T>`, return `T`.
pub fn unbox_type(ty: &syn::Type) -> syn::Type {
    match ty {
        syn::Type::Path(syn::TypePath {
            qself: None,
            path:
                syn::Path {
                    leading_colon: None,
                    segments,
                },
        }) if segments.len() == 1 => match &segments[0] {
            syn::PathSegment {
                ident,
                arguments:
                    syn::PathArguments::AngleBracketed(syn::AngleBracketedGenericArguments {
                        args, ..
                    }),
            } if ident == "Box" && args.len() == 1 => {
                if let syn::GenericArgument::Type(inner_ty) = &args[0] {
                    return inner_ty.clone();
                }
            }
            _ => {}
        },
        _ => {}
    }
    ty.clone()
}
