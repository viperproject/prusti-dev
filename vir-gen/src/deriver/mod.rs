use syn::fold::Fold;

mod common;
mod constructors;
mod helpers;
mod visitors;

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
        if let Some((brace, mut content)) = item_mod.content {
            let helpers_to_derive = self::common::collect(&mut content, "derive_helpers");
            let visitors_to_derive = self::common::collect(&mut content, "derive_visitors");
            let mut content = match self::helpers::derive(content, helpers_to_derive) {
                Ok(content) => content,
                Err(error) => unimplemented!("error: {:?}", error),
            };
            let visitors = match self::visitors::derive(&content, visitors_to_derive) {
                Ok(content) => content,
                Err(error) => unimplemented!("error: {:?}", error),
            };
            match self::constructors::derive(&mut content) {
                Ok(()) => {}
                Err(error) => unimplemented!("error: {:?}", error),
            };
            let mut content: Vec<syn::Item> = content
                .into_iter()
                .map(|item| {
                    if let syn::Item::Mod(inner_item_mod) = item {
                        syn::Item::Mod(self.fold_item_mod(inner_item_mod))
                    } else {
                        item
                    }
                })
                .collect();
            content.extend(visitors);
            item_mod.content = Some((brace, content));
        }
        item_mod
    }
}
