vir_raw_block! { Sort =>
    pub mod kw {
        syn::custom_keyword!(Bool);
        syn::custom_keyword!(Int);
        syn::custom_keyword!(Real);
    }
    impl syn::parse::Parse for Sort {
        fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
            let lookahead = input.lookahead1();
            if lookahead.peek(kw::Bool) {
                input.parse::<kw::Bool>()?;
                Ok(Self::Bool)
            } else if lookahead.peek(kw::Int) {
                input.parse::<kw::Int>()?;
                Ok(Self::Int)
            } else if lookahead.peek(kw::Real) {
                input.parse::<kw::Real>()?;
                Ok(Self::Real)
            } else {
                Ok(Self::Uninterpreted { name: input.parse()? })
            }
        }
    }
    impl quote::ToTokens for Sort {
        fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
            match self {
                Sort::Bool => {
                    tokens.extend(quote::quote! {svirpti_vir::high::Sort::Bool})
                },
                Sort::Int => {
                    tokens.extend(quote::quote! {svirpti_vir::high::Sort::Int})
                },
                Sort::Real => {
                    tokens.extend(quote::quote! {svirpti_vir::high::Sort::Real})
                },
                Sort::Uninterpreted { name } => {
                    tokens.extend(quote::quote! {svirpti_vir::high::Sort::Uninterpreted { name: #name }})
                },
            }
        }
    }
}
