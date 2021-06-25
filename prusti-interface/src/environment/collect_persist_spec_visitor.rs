use log::{trace, debug};
use rustc_ast::ast::{self, MacDelimiter::Brace, MacroDef, MacArgs, ItemKind};
use rustc_ast::tokenstream::{self, DelimSpan, TokenStream, TokenTree, TreeAndSpacing};
use rustc_ast::node_id::NodeId;
use rustc_ast::ptr::P;
use rustc_ast::visit::Visitor;
use rustc_span::{Span, symbol};
use crate::utils::{has_prusti_attr};

pub struct PersistSpecCollector{
    tokens_cursor: tokenstream::Cursor,
}

impl PersistSpecCollector {
    pub fn new() -> Self {
        PersistSpecCollector {
            tokens_cursor: TokenStream::default().trees(),
        }
    }

    pub fn collect_specs(mut self, krate: &mut ast::Crate){
        let append_tokens: TokenStream = self.tokens_cursor.collect();

        if let Some(item) = krate.items.iter_mut().find(|item| {
            has_prusti_attr(&item.attrs, "export_all")
        }) {
            match &mut item.kind {
                ItemKind::MacroDef(mac_def) => {
                    match &mut *mac_def.body {
                        MacArgs::Delimited(_, _, tokens) => {
                            let mut tree: Vec<TokenTree> = tokens.to_owned().into_trees().collect();
                            let count = tree.len()-2;
                            let mut expand_location_token = &mut tree[count];
                            match expand_location_token {
                                TokenTree::Delimited(_, _, tokens) => {
                                    *tokens = append_tokens;
                                },
                                _ => return
                            }
                            let tree_and_spacing: Vec<TreeAndSpacing> = tree.into_iter().map(|tt| {
                                TreeAndSpacing::from(tt)
                            }).collect();
                            *tokens = TokenStream::new(tree_and_spacing);
                        },
                            
                            
                        _ => return
                    }
                },
                _ => return
            }
        } else {
            return
        }
    }
}

impl<'ast> Visitor<'ast> for PersistSpecCollector {


    fn visit_item(&mut self, item: &'ast ast::Item) {

        let attrs = &item.attrs;

        if has_prusti_attr(attrs, "persist") {
            match &item.kind {
                ast::ItemKind::Mod(_, mod_kind) => {
                    if let Some(lazy_mod_tokens) = &item.tokens {
                        let mod_tokens = lazy_mod_tokens.create_token_stream().to_tokenstream();
                        self.tokens_cursor.append(mod_tokens);
                    }
    
    
                },
                ast::ItemKind::Fn(_) => {
                    if let Some(lazy_fn_tokens) = &item.tokens {
                        let fn_tokens = lazy_fn_tokens.create_token_stream().to_tokenstream();
                        println!("fn_tokens: {:?} \n\n", &fn_tokens);
                        self.tokens_cursor.append(fn_tokens);
                    }
    
                    return;
                },
                ast::ItemKind::Impl(_) => {
                    if let Some(lazy_impl_tokens) = &item.tokens {
                        let impl_tokens = lazy_impl_tokens.create_token_stream().to_tokenstream();
                        println!("impl tokens: {:?} \n\n", &impl_tokens);
                        self.tokens_cursor.append(impl_tokens);
                    }
    
                    return;
                },
                _ => {
                    return;
                }
            }
        }
        
    }
}

