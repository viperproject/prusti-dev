trait Interface {
    type Expression;
    type VariableSymbol;
    type Sort;
    type FunctionSymbol;
    type LabelSymbol;
}

mod display;
mod evaluation;
mod helpers;
mod parse;
mod parse_ast;
mod rsmt;
mod sort;

pub struct Variable {
    pub name: VariableSymbol,
}

pub enum Constant {
    Bool(bool),
    Int(i64),
}

pub struct UnaryOperation {
    pub kind: UnaryOperationKind,
    pub arg: Box<Expression>,
}

pub enum UnaryOperationKind {
    Not,
    Minus,
}

pub struct BinaryOperation {
    pub kind: BinaryOperationKind,
    pub left: Box<Expression>,
    pub right: Box<Expression>,
}

pub enum BinaryOperationKind {
    EqCmp,
    NeCmp,
    GtCmp,
    GeCmp,
    LtCmp,
    LeCmp,
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    And,
    Or,
    Implies,
}

pub struct Conditional {
    pub guard: Box<Expression>,
    pub then_expr: Box<Expression>,
    pub else_expr: Box<Expression>,
}

pub struct Quantifier {
    pub kind: QuantifierKind,
    /// Bounded variables.
    pub variables: Vec<BoundedVariableDecl>,
    /// A quantifier is triggered when at least one of the triggers matches.
    pub triggers: Vec<Trigger>,
    pub body: Box<Expression>,
}

pub enum QuantifierKind {
    ForAll,
    Exists,
}

pub struct BoundedVariableDecl {
    pub name: VariableSymbol,
    pub sort: Sort,
}

pub struct Trigger {
    pub parts: Vec<Expression>,
}

pub struct FunctionApplication {
    /// Invoked function.
    pub function: FunctionSymbol,
    pub args: Vec<Expression>,
}

pub struct LabelledExpression {
    pub name: LabelSymbol,
    pub positivity: LabelPositivity,
    pub expression: Box<Expression>,
}

pub enum LabelPositivity {
    Positive,
    Negative,
}
