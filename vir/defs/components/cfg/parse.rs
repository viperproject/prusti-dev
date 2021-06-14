vir_raw_block! { GuardedBasicBlock =>
    mod basic_block_kw {
        syn::custom_keyword!(guard);
        syn::custom_keyword!(goto);
    }
    pub struct BasicBlock {
        pub label: syn::Ident,
        pub guard: Expression,
        pub statements: Vec<Statement>,
        pub successor_labels: Vec<syn::Ident>,
        pub successors: Vec<usize>,
    }
    impl syn::parse::Parse for BasicBlock {
        fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
            let label = input.parse::<syn::Ident>()?;
            if label == "exit" {
                return Err(syn::Error::new(
                    label.span(),
                    "`exit` is reserved for exiting procedure",
                ));
            } else if label == "entry" {
                return Err(syn::Error::new(
                    label.span(),
                    "`entry` is reserved for the invisible entry block",
                ));
            }
            let content;
            syn::braced!(content in input);
            content.parse::<basic_block_kw::guard>()?;
            let guard = content.parse()?;
            content.parse::<syn::Token![;]>()?;
            let mut statements = Vec::new();
            let successor_labels = loop {
                if content.peek(basic_block_kw::goto) {
                    content.parse::<basic_block_kw::goto>()?;
                    let labels_content;
                    syn::braced!(labels_content in content);
                    let punctuated: syn::punctuated::Punctuated<_, syn::Token![,]> =
                        labels_content.parse_terminated(syn::Ident::parse)?;
                    break punctuated.into_iter().collect();
                } else {
                    statements.push(content.parse()?);
                }
            };
            Ok(Self {
                label,
                guard,
                statements,
                successor_labels,
                successors: Vec::new(),
            })
        }
    }
    impl quote::ToTokens for BasicBlock {
        fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
            let label = self.label.to_string();
            let guard = &self.guard;
            let mut statement_tokens = proc_macro2::TokenStream::new();
            for statement in &self.statements {
                statement_tokens.extend(quote::quote! {
                    #statement,
                });
            }
            let mut successor_tokens = proc_macro2::TokenStream::new();
            for successor in &self.successors {
                successor_tokens.extend(quote::quote! {
                    #successor.into(),
                });
            }
            tokens.extend(quote::quote! {
                {
                    BasicBlock {
                        label: #label.into(),
                        guard: #guard,
                        statements: vec![#statement_tokens].into(),
                        successors: vec![#successor_tokens],
                    }
                }
            });
        }
    }
}
