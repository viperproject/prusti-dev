trait Interface {
    type LabelSymbol;
    type Expression;
    type Variable;
}

mod helpers;
mod parse;
mod parse_ast;
mod display;

pub struct Assert {
    pub assertion: Expression,
    pub label: Option<LabelSymbol>,
}

pub struct Assume {
    pub assertion: Expression,
    pub label: Option<LabelSymbol>,
}

pub enum Havoc {
    Variable(Variable),
}

pub struct Assign {
    pub variable: Variable,
    pub expression: Expression,
}