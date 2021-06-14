trait Interface {
    type Sort;
    type Expression;
}

pub struct UninterpretedSortDeclaration {
    pub name: syn::Ident,
}

pub struct VariableDeclaration {
    pub name: syn::Ident,
    pub sort: Sort,
}

pub struct FunctionDeclaration {
    pub name: syn::Ident,
    pub parameters: Vec<VariableDeclaration>,
    pub return_sort: Sort,
}

pub struct AxiomDeclaration {
    pub name: syn::Ident,
    pub body: Expression,
}
