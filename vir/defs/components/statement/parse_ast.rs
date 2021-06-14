trait Interface {
    type Expression;
    type Variable;
}

pub struct Assert {
    pub assertion: Expression,
    pub label: syn::Ident,
}

pub struct Assume {
    pub assertion: Expression,
    pub label: syn::Ident,
}

pub enum Havoc {
    Variable(Variable),
}

pub struct Assign {
    pub variable: Variable,
    pub expression: Expression,
}
