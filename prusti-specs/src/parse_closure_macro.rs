use syn::parse::{Parse, ParseStream};

pub(crate) struct ClosureWithSpec {
    pub pres: Vec<syn::Expr>,
    pub posts: Vec<syn::Expr>,
    pub cl: syn::ExprClosure
}

impl Parse for ClosureWithSpec {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let mut requires: Vec<syn::Expr> = vec! [];
        let mut ensures: Vec<syn::Expr> = vec! [];
        let mut cl: Option<syn::ExprClosure> = None;

        while !input.is_empty() {
            if input.peek(syn::Ident) {
                let id: syn::Ident = input.parse()?;
                let expr: syn::Expr = input.parse()?;
                input.parse::<syn::Token![,]>()?;

                if id == "requires" {
                    requires.push(expr);
                } else if id == "ensures" {
                    ensures.push(expr);
                } else {
                    return Err(syn::Error::new(id.span(), "invalid closure specification"));
                }
            } else {
                cl = Some(input.parse()?);
            }
        }

        if cl.is_none() {
            return Err(syn::Error::new(input.span(), "closure specification without closure"));
        }

        Ok(ClosureWithSpec {
            pres: requires,
            posts: ensures,
            cl: cl.unwrap()
        })
    }
}
