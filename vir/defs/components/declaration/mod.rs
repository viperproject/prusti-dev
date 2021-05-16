trait Interface {
    type Sort;
    type Type;
    type Expression;
    type UninterpretedSortSymbol;
    type VariableSymbol;
    type FunctionSymbol;
    type LabelSymbol;
    type AxiomNameSymbol;
    type FieldNameSymbol;
    type AdtNameSymbol;
}

mod parse;
mod parse_ast;
mod rsmt;
mod display;

pub struct UninterpretedSortDeclaration {
    pub name: UninterpretedSortSymbol,
}

pub struct VariableDeclaration {
    pub name: VariableSymbol,
    pub sort: Sort,
}

pub struct FunctionDeclaration {
    pub name: FunctionSymbol,
    pub parameters: Vec<VariableDeclaration>,
    pub return_sort: Sort,
}

pub struct LabelDeclaration {
    pub name: LabelSymbol,
}

pub struct AxiomDeclaration {
    pub name: Option<AxiomNameSymbol>,
    pub body: Expression,
}
