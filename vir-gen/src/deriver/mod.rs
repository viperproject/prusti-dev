use syn::fold::Fold;

mod common;
mod helpers;
mod lower;
mod singles;
mod visitors;

pub(crate) fn expand(
    ir: syn::ItemMod,
    original_irs: &[syn::ItemMod],
) -> (syn::ItemMod, Vec<syn::Error>) {
    let mut expander = Expander {
        errors: Default::default(),
        current_path: Default::default(),
        original_irs,
    };
    let expanded_ir = expander.fold_item_mod(ir);
    (expanded_ir, expander.errors)
}

struct Expander<'a> {
    errors: Vec<syn::Error>,
    current_path: Vec<syn::Ident>,
    original_irs: &'a [syn::ItemMod],
}

impl<'a> Fold for Expander<'a> {
    fn fold_item_mod(&mut self, mut item_mod: syn::ItemMod) -> syn::ItemMod {
        self.current_path.push(item_mod.ident.clone());
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
            match self::singles::derive(&mut content) {
                Ok(()) => {}
                Err(error) => unimplemented!("error: {:?}", error),
            };
            match self::lower::derive(&mut content, self.original_irs) {
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
        self.current_path.pop();
        item_mod
    }
}
