use std::{fs::File, io::Read, mem, path::PathBuf};
use syn::{fold::Fold, spanned::Spanned};

mod ast;

/// Expand the ast by reading in all modules.
pub(crate) fn expand(item: syn::ItemMod, path: PathBuf) -> (syn::ItemMod, Vec<syn::Error>) {
    let mut expander = Expander {
        current_path: path,
        errors: Vec::new(),
    };
    let new_item = expander.fold_item_mod(item);
    (new_item, expander.errors)
}

struct Expander {
    current_path: PathBuf,
    errors: Vec<syn::Error>,
}

impl Fold for Expander {
    fn fold_item_mod(&mut self, mut item: syn::ItemMod) -> syn::ItemMod {
        if item.content.is_none() {
            match load_file(self.current_path.clone(), &item.ident) {
                Ok((new_path, file)) => {
                    item.attrs.extend(file.attrs.into_iter().map(|mut attr| {
                        attr.style = syn::AttrStyle::Outer;
                        attr
                    }));
                    item.content = Some((syn::token::Brace(item.span()), file.items));
                    let old_path = mem::replace(&mut self.current_path, new_path);
                    let new_item = self.fold_item_mod(item);
                    self.current_path = old_path;
                    new_item
                }
                Err(error) => {
                    self.errors.push(error);
                    item
                }
            }
        } else {
            syn::fold::fold_item_mod(self, item)
        }
    }
}

fn load_file(mut current_path: PathBuf, ident: &syn::Ident) -> syn::Result<(PathBuf, syn::File)> {
    current_path.pop();
    current_path.push(format!("{}.rs", ident));
    if !current_path.exists() {
        current_path.pop();
        current_path.push(format!("{}/mod.rs", ident));
    }
    let mut file = File::open(&current_path).map_err(|err| {
        syn::Error::new(
            ident.span(),
            format!("could not open {:?}: {}", current_path, err),
        )
    })?;
    let mut content = String::new();
    file.read_to_string(&mut content).map_err(|err| {
        syn::Error::new(
            ident.span(),
            format!("could not read {:?}: {}", current_path, err),
        )
    })?;

    let file = syn::parse_file(&content)?;
    Ok((current_path, file))
}
