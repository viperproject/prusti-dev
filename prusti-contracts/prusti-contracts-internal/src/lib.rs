#![cfg_attr(not(feature = "prusti"), no_std)]

#[cfg(not(feature = "prusti"))]
mod private {
    use proc_macro::TokenStream;

    #[proc_macro_attribute]
    pub fn requires(_attr: TokenStream, tokens: TokenStream) -> TokenStream {
        tokens
    }

    #[proc_macro_attribute]
    pub fn invariant(_attr: TokenStream, tokens: TokenStream) -> TokenStream {
        tokens
    }

    #[proc_macro_attribute]
    pub fn ensures(_attr: TokenStream, tokens: TokenStream) -> TokenStream {
        tokens
    }

    #[proc_macro_attribute]
    pub fn after_expiry(_attr: TokenStream, tokens: TokenStream) -> TokenStream {
        tokens
    }

    #[proc_macro_attribute]
    pub fn assert_on_expiry(_attr: TokenStream, tokens: TokenStream) -> TokenStream {
        tokens
    }

    #[proc_macro_attribute]
    pub fn pure(_attr: TokenStream, tokens: TokenStream) -> TokenStream {
        tokens
    }

    #[proc_macro_attribute]
    pub fn trusted(_attr: TokenStream, tokens: TokenStream) -> TokenStream {
        tokens
    }

    #[proc_macro]
    pub fn body_invariant(_tokens: TokenStream) -> TokenStream {
        TokenStream::new()
    }

    #[proc_macro]
    pub fn prusti_assert(_tokens: TokenStream) -> TokenStream {
        TokenStream::new()
    }

    #[proc_macro]
    pub fn prusti_assume(_tokens: TokenStream) -> TokenStream {
        TokenStream::new()
    }

    #[proc_macro_attribute]
    pub fn refine_trait_spec(_attr: TokenStream, tokens: TokenStream) -> TokenStream {
        tokens
    }

    #[proc_macro_attribute]
    pub fn extern_spec(_attr: TokenStream, _tokens: TokenStream) -> TokenStream {
        TokenStream::new()
    }

    #[proc_macro]
    pub fn predicate(_tokens: TokenStream) -> TokenStream {
        TokenStream::new()
    }

    #[proc_macro_attribute]
    pub fn model(_attr: TokenStream, _tokens: TokenStream) -> TokenStream {
        TokenStream::new()
    }

    #[proc_macro_attribute]
    pub fn ghost_constraint(_attr: TokenStream, tokens: TokenStream) -> TokenStream {
        tokens
    }

    #[proc_macro]
    pub fn ghost(_tokens: TokenStream) -> TokenStream {
        TokenStream::new()
    }
}

#[cfg(feature = "prusti")]
mod private {
    use proc_macro::TokenStream;
    use prusti_specs::{rewrite_prusti_attributes, SpecAttributeKind};

    #[proc_macro_attribute]
    pub fn requires(attr: TokenStream, tokens: TokenStream) -> TokenStream {
        rewrite_prusti_attributes(SpecAttributeKind::Requires, attr.into(), tokens.into()).into()
    }

    #[proc_macro_attribute]
    pub fn ensures(attr: TokenStream, tokens: TokenStream) -> TokenStream {
        rewrite_prusti_attributes(SpecAttributeKind::Ensures, attr.into(), tokens.into()).into()
    }

    #[proc_macro_attribute]
    pub fn after_expiry(attr: TokenStream, tokens: TokenStream) -> TokenStream {
        rewrite_prusti_attributes(SpecAttributeKind::AfterExpiry, attr.into(), tokens.into()).into()
    }

    #[proc_macro_attribute]
    pub fn assert_on_expiry(attr: TokenStream, tokens: TokenStream) -> TokenStream {
        rewrite_prusti_attributes(
            SpecAttributeKind::AssertOnExpiry,
            attr.into(),
            tokens.into(),
        )
        .into()
    }

    #[proc_macro_attribute]
    pub fn pure(attr: TokenStream, tokens: TokenStream) -> TokenStream {
        rewrite_prusti_attributes(SpecAttributeKind::Pure, attr.into(), tokens.into()).into()
    }

    #[proc_macro_attribute]
    pub fn trusted(attr: TokenStream, tokens: TokenStream) -> TokenStream {
        prusti_specs::trusted(attr.into(), tokens.into()).into()
    }

    #[proc_macro]
    pub fn body_invariant(tokens: TokenStream) -> TokenStream {
        prusti_specs::body_invariant(tokens.into()).into()
    }

    #[proc_macro]
    pub fn prusti_assert(tokens: TokenStream) -> TokenStream {
        prusti_specs::prusti_assertion(tokens.into()).into()
    }

    #[proc_macro]
    pub fn prusti_assume(tokens: TokenStream) -> TokenStream {
        prusti_specs::prusti_assume(tokens.into()).into()
    }

    #[proc_macro]
    pub fn closure(tokens: TokenStream) -> TokenStream {
        prusti_specs::closure(tokens.into(), false).into()
    }

    #[proc_macro_attribute]
    pub fn refine_trait_spec(attr: TokenStream, tokens: TokenStream) -> TokenStream {
        prusti_specs::refine_trait_spec(attr.into(), tokens.into()).into()
    }

    #[proc_macro_attribute]
    pub fn extern_spec(attr: TokenStream, tokens: TokenStream) -> TokenStream {
        prusti_specs::extern_spec(attr.into(), tokens.into()).into()
    }

    #[proc_macro_attribute]
    pub fn invariant(attr: TokenStream, tokens: TokenStream) -> TokenStream {
        prusti_specs::invariant(attr.into(), tokens.into()).into()
    }

    #[proc_macro]
    pub fn predicate(tokens: TokenStream) -> TokenStream {
        prusti_specs::predicate(tokens.into()).into()
    }

    #[proc_macro_attribute]
    pub fn model(_attr: TokenStream, tokens: TokenStream) -> TokenStream {
        prusti_specs::type_model(_attr.into(), tokens.into()).into()
    }

    #[proc_macro_attribute]
    pub fn ghost_constraint(attr: TokenStream, tokens: TokenStream) -> TokenStream {
        rewrite_prusti_attributes(
            SpecAttributeKind::GhostConstraint,
            attr.into(),
            tokens.into(),
        )
        .into()
    }

    #[proc_macro]
    pub fn ghost(tokens: TokenStream) -> TokenStream {
        prusti_specs::ghost(tokens.into()).into()
    }
}

#[proc_macro_attribute]
pub fn print_counterexample(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    prusti_specs::print_counterexample(attr.into(), tokens.into()).into()
}
