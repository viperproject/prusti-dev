use syn::parse::{Parse, ParseStream};

pub(crate) struct ClosureWithSpec {
    pub pres: Vec<syn::Expr>,
    pub posts: Vec<syn::Expr>,
    pub cl: syn::ExprClosure
}

impl Parse for ClosureWithSpec {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let mut attrs = input.call(syn::Attribute::parse_outer)?;
        let mut cl: syn::ExprClosure = input.parse()?;

        let mut pres: Vec<syn::Result<syn::Expr>> = vec![];
        let mut posts: Vec<syn::Result<syn::Expr>> = vec![];

        // collect and remove any specification attributes
        // leave other attributes intact
        attrs.drain_filter(|attr| {
            if let Some(id) = attr.path.get_ident() {
                match id.to_string().as_ref() {
                    "requires" => pres.push(syn::parse2(attr.tokens.clone())),
                    "ensures" => posts.push(syn::parse2(attr.tokens.clone())),
                    _ => return false
                }
                true
            } else {
                false
            }
        });
        cl.attrs = attrs;

        Ok(Self {
            pres: pres.into_iter().collect::<syn::Result<Vec<_>>>()?,
            posts: posts.into_iter().collect::<syn::Result<Vec<_>>>()?,
            cl,
        })
    }
}
