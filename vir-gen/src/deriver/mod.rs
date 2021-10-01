use syn::{fold::Fold, parse_quote, spanned::Spanned};

mod helpers;

pub(crate) fn expand(ir: syn::ItemMod) -> (syn::ItemMod, Vec<syn::Error>) {
    let mut expander = Expander { errors: Vec::new() };
    let expanded_ir = expander.fold_item_mod(ir);
    (expanded_ir, expander.errors)
}

struct Expander {
    errors: Vec<syn::Error>,
}

impl Fold for Expander {
    fn fold_item_mod(&mut self, mut item_mod: syn::ItemMod) -> syn::ItemMod {
        eprintln!("mod: {:?}", item_mod.ident);
        if let Some((brace, mut content)) = item_mod.content {
            let helpers_to_derive = self::helpers::collect(&mut content);
            let content = match self::helpers::derive(content, helpers_to_derive) {
                Ok(content) => content,
                Err(error) => unimplemented!("error: {:?}", error),
            };
            let content = content
                .into_iter()
                .map(|item| {
                    if let syn::Item::Mod(inner_item_mod) = item {
                        syn::Item::Mod(self.fold_item_mod(inner_item_mod))
                    } else {
                        item
                    }
                })
                .collect();
            item_mod.content = Some((brace, content));
        }
        item_mod
    }
}
