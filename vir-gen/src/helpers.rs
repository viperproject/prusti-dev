fn append(s: &mut String, iter: impl Iterator<Item = char>) {
    for c in iter {
        s.push(c);
    }
}

/// Converts CamelCase to camel_case
pub fn method_name_from_camel(ident: &syn::Ident) -> syn::Ident {
    let string = ident.to_string();
    let mut iterator = string.chars();
    let mut new_ident = String::new();
    append(&mut new_ident, iterator.next().unwrap().to_lowercase());
    for c in iterator {
        if c.is_uppercase() {
            new_ident.push('_');
            append(&mut new_ident, c.to_lowercase());
        } else {
            new_ident.push(c);
        }
    }
    syn::Ident::new(&new_ident, ident.span())
}
