vir_raw_block! { kw =>
    pub mod kw {
        syn::custom_keyword!(assert);
        syn::custom_keyword!(assume);
        syn::custom_keyword!(havoc);
        syn::custom_keyword!(assign);
    }
}

vir_raw_block! { Assert =>
    impl syn::parse::Parse for Assert {
        fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
            input.parse::<kw::assert>()?;
            let statement = Self {
                label: input.parse()?,
                assertion: input.parse()?,
            };
            input.parse::<syn::Token![;]>()?;
            Ok(statement)
        }
    }
    impl quote::ToTokens for Assert {
        fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
            let label = self.label.to_string();
            let assertion = &self.assertion;
            tokens.extend(quote::quote! {
                Assert { label: Some(#label.into()), assertion: #assertion }
            })
        }
    }
}

vir_raw_block! { Assume =>
    impl syn::parse::Parse for Assume {
        fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
            input.parse::<kw::assume>()?;
            let statement = Self {
                label: input.parse()?,
                assertion: input.parse()?,
            };
            input.parse::<syn::Token![;]>()?;
            Ok(statement)
        }
    }
    impl quote::ToTokens for Assume {
        fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
            let label = self.label.to_string();
            let assertion = &self.assertion;
            tokens.extend(quote::quote! {
                Assume { label: Some(#label.into()), assertion: #assertion }
            })
        }
    }
}

vir_raw_block! { Havoc =>
    impl syn::parse::Parse for Havoc {
        fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
            input.parse::<kw::havoc>()?;
            let statement = Self::Variable(input.parse()?);
            input.parse::<syn::Token![;]>()?;
            Ok(statement)
        }
    }
    impl quote::ToTokens for Havoc {
        fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
            match self {
                Havoc::Variable(variable) => {
                    tokens.extend(quote::quote! {
                        Havoc::Variable(#variable)
                    })
                }
            }
        }
    }
}

vir_raw_block! { Assign =>
    impl syn::parse::Parse for Assign {
        fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
            input.parse::<kw::assign>()?;
            let variable = input.parse()?;
            input.parse::<syn::Token![=]>()?;
            let expression = input.parse()?;
            input.parse::<syn::Token![;]>()?;
            Ok(Self { variable, expression })
        }
    }
    impl quote::ToTokens for Assign {
        fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
            let variable = &self.variable;
            let expression = &self.expression;
            tokens.extend(quote::quote! {
                Assign { variable: #variable, expression: #expression }
            })
        }
    }
}