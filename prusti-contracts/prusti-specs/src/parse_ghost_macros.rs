use syn::parse::{Parse, ParseStream};

pub(crate) struct OnDropUnwind {
    pub dropped_place: syn::Expr,
    pub block: syn::Block,
}

impl Parse for OnDropUnwind {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let dropped_place = input.parse()?;
        let token = input.parse::<syn::Token![=>]>()?;
        let statements = syn::Block::parse_within(input)?;
        let block = syn::Block {
            brace_token: syn::token::Brace {
                span: token.spans[0],
            },
            stmts: statements,
        };
        Ok(Self {
            dropped_place,
            block,
        })
    }
}

pub(crate) struct WithFinally {
    pub executed_block: Vec<syn::Stmt>,
    pub on_panic_block: syn::Block,
    pub finally_block: syn::Block,
}

impl Parse for WithFinally {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let executed_block: syn::Block = input.parse()?;
        let on_panic_block = input.parse()?;
        let finally_block = input.parse()?;
        Ok(Self {
            executed_block: executed_block.stmts,
            on_panic_block,
            finally_block,
        })
    }
}
