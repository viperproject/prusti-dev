trait Interface {
    type UninterpretedSortSymbol;
    type Context;
}

mod display;
mod parse;
mod parse_ast;
mod rsmt;

pub enum Sort {
    Bool,
    Int,
    Real,
    /// A user-defined uninterpreted sort.
    Uninterpreted {
        name: UninterpretedSortSymbol,
    },
}

impl Sort {
    pub fn is_integer(&self) -> bool {
        std::matches!(self, Sort::Int)
    }
}

pub trait WithSort<C: Context> {
    fn sort<'a>(&'a self, context: &'a C) -> &'a Sort;
}
