vir_raw_block! { kw =>
    pub mod kw {
        syn::custom_keyword!(sort);
        syn::custom_keyword!(axiom);
    }
}

vir_raw_block! { UninterpretedSortDeclaration =>
    impl syn::parse::Parse for UninterpretedSortDeclaration {
        fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
            input.parse::<kw::sort>()?;
            let name = input.parse()?;
            input.parse::<syn::Token![;]>()?;
            Ok(Self { name })
        }
    }
    impl quote::ToTokens for UninterpretedSortDeclaration {
        fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
            let name = format!("{}", self.name);
            tokens.extend(quote::quote! {
                UninterpretedSortDeclaration {
                    name: #name.into(),
                }
            });
        }
    }
}

vir_raw_block! { VariableDeclaration =>
    impl syn::parse::Parse for VariableDeclaration {
        fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
            let name = input.parse()?;
            input.parse::<syn::Token![:]>()?;
            let sort = input.parse()?;
            Ok(Self { name, sort })
        }
    }
    impl quote::ToTokens for VariableDeclaration {
        fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
            let name = format!("{}", self.name);
            let sort = &self.sort;
            tokens.extend(quote::quote! {
                VariableDeclaration {
                    name: #name.into(),
                    sort: #sort,
                }
            });
        }
    }
}

vir_raw_block! { FunctionDeclaration =>
    impl syn::parse::Parse for FunctionDeclaration {
        fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
            input.parse::<syn::Token![fn]>()?;
            let name = input.parse()?;
            let parameters;
            syn::parenthesized!(parameters in input);
            let punctuated: syn::punctuated::Punctuated<_, syn::Token![,]> =
                parameters.parse_terminated(VariableDeclaration::parse)?;
            let parameters = punctuated.into_iter().collect();
            input.parse::<syn::Token![->]>()?;
            let return_sort = input.parse()?;
            input.parse::<syn::Token![;]>()?;
            Ok(Self {
                name,
                parameters,
                return_sort,
            })
        }
    }
    impl quote::ToTokens for FunctionDeclaration {
        fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
            let name = format!("{}", self.name);
            let mut parameter_tokens = proc_macro2::TokenStream::new();
            for parameter in &self.parameters {
                parameter_tokens.extend(quote::quote! { #parameter, });
            }
            let sort = &self.return_sort;
            tokens.extend(quote::quote! {
                FunctionDeclaration {
                    name: #name.into(),
                    parameters: vec![#parameter_tokens],
                    return_sort: #sort,
                }
            });
        }
    }
}

vir_raw_block! { AxiomDeclaration =>
    impl syn::parse::Parse for AxiomDeclaration {
        fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
            input.parse::<kw::axiom>()?;
            let name = input.parse()?;
            let content;
            syn::braced!(content in input);
            let body = content.parse()?;
            if !content.is_empty() {
                return Err(syn::Error::new(content.span(), "unexpected tokens"));
            }
            Ok(Self { name, body })
        }
    }
    impl quote::ToTokens for AxiomDeclaration {
        fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
            let name = format!("{}", self.name);
            let body = &self.body;
            tokens.extend(quote::quote! {
                AxiomDeclaration {
                    name: Some(#name.into()),
                    body: #body,
                }
            });
        }
    }
}
