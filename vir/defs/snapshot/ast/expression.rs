pub(crate) use super::{
    field::FieldDecl,
    position::Position,
    ty::{Type, VariantIndex},
    variable::VariableDecl,
};
use crate::common::display;

#[derive_helpers]
#[derive_visitors]
pub enum Expression {
    /// A local variable.
    Local(Local),
    /// An enum variant.
    Variant(Variant),
    /// A field access. (Field accesses can never fail.)
    Field(Field),
    /// A reference or pointer dereference. (Sometimes can fail.)
    Deref(Deref),
    /// The inverse of Deref.
    AddrOf(AddrOf),
    LabelledOld(LabelledOld),
    Constant(Constant),
    UnaryOp(UnaryOp),
    BinOp(BinOp),
    /// Container Operation on a Viper container (e.g. Seq index)
    ContainerOp(ContainerOp),
    /// Viper Seq
    Seq(Seq),
    Conditional(Conditional),
    Quantifier(Quantifier),
    /// let variable == (expr) in body
    LetExpr(LetExpr),
    FuncApp(FuncApp),
    /// Inform the fold-unfold algorithm that at this program point a enum type can be downcasted
    /// to one of its variants. This statement is a no-op for Viper.
    /// Arguments:
    /// * expression in which the downcast is visible
    /// * place to the enumeration that is downcasted
    /// * field that encodes the variant
    Downcast(Downcast),
}

#[display(fmt = "{}", "variable.name")]
pub struct Local {
    pub variable: VariableDecl,
    pub position: Position,
}

#[display(fmt = "{}[{}]", base, variant_index)]
pub struct Variant {
    pub base: Box<Expression>,
    pub variant_index: VariantIndex,
    // invariant: variant_index == typ.variant_index
    pub ty: Type,
    pub position: Position,
}

#[display(fmt = "{}.{}", base, "field.name")]
pub struct Field {
    pub base: Box<Expression>,
    pub field: FieldDecl,
    pub position: Position,
}

#[display(fmt = "{}.*", base)]
pub struct Deref {
    pub base: Box<Expression>,
    pub ty: Type,
    pub position: Position,
}

#[display(fmt = "{}.&", base)]
pub struct AddrOf {
    pub base: Box<Expression>,
    pub ty: Type,
    pub position: Position,
}

#[display(fmt = "old[{}]({})", label, base)]
pub struct LabelledOld {
    pub label: String,
    pub base: Box<Expression>,
    pub position: Position,
}

#[display(fmt = "{}", value)]
pub struct Constant {
    pub value: ConstantValue,
    pub ty: Type,
    pub position: Position,
}

pub enum ConstantValue {
    Bool(bool),
    Int(i64),
    BigInt(String),
    /// All function pointers share the same constant, because their function
    /// is determined by the type system.
    FnPtr,
}

pub enum UnaryOpKind {
    Not,
    Minus,
}

#[display(fmt = "{}{}", op_kind, argument)]
pub struct UnaryOp {
    pub op_kind: UnaryOpKind,
    pub argument: Box<Expression>,
    pub position: Position,
}

pub enum BinaryOpKind {
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

#[display(fmt = "{}{}{}", left, op_kind, right)]
pub struct BinOp {
    pub op_kind: BinaryOpKind,
    pub left: Box<Expression>,
    pub right: Box<Expression>,
    pub position: Position,
}

pub enum ContainerOpKind {
    SeqIndex,
    SeqConcat,
    SeqLen,
}

#[display(fmt = "{}{}{}", left, op_kind, right)]
pub struct ContainerOp {
    pub op_kind: ContainerOpKind,
    pub left: Box<Expression>,
    pub right: Box<Expression>,
    pub position: Position,
}

#[display(fmt = "Seq({})", "display::cjoin(elements)")]
pub struct Seq {
    pub ty: Type,
    pub elements: Vec<Expression>,
    pub position: Position,
}

#[display(fmt = "({} ? {} : {})", guard, then_expr, else_expr)]
pub struct Conditional {
    pub guard: Box<Expression>,
    pub then_expr: Box<Expression>,
    pub else_expr: Box<Expression>,
    pub position: Position,
}

#[display(fmt = "{}", "display::cjoin(terms)")]
pub struct Trigger {
    pub terms: Vec<Expression>,
}

pub enum QuantifierKind {
    ForAll,
    Exists,
}

#[display(
    fmt = "{}(|{}| {}, triggers=[{}])",
    kind,
    "display::cjoin(variables)",
    body,
    "display::join(\"; \", triggers)"
)]
pub struct Quantifier {
    pub kind: QuantifierKind,
    pub variables: Vec<VariableDecl>,
    pub triggers: Vec<Trigger>,
    pub body: Box<Expression>,
    pub position: Position,
}

#[display(fmt = "let {} = {} in {}", variable, def, body)]
pub struct LetExpr {
    pub variable: VariableDecl,
    pub def: Box<Expression>,
    pub body: Box<Expression>,
    pub position: Position,
}

#[display(fmt = "{}({})", function_name, "display::cjoin(arguments)")]
pub struct FuncApp {
    pub function_name: String,
    pub arguments: Vec<Expression>,
    pub parameters: Vec<VariableDecl>,
    pub return_type: Type,
    pub position: Position,
}

#[display(fmt = "(downcast {} to {} in {})", enum_place, "field.name", base)]
pub struct Downcast {
    pub base: Box<Expression>,
    pub enum_place: Box<Expression>,
    pub field: FieldDecl,
    pub position: Position,
}
