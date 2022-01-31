pub(crate) use super::{field::FieldDecl, position::Position, ty::Type, variable::VariableDecl};
use crate::common::display;

#[derive_helpers]
#[derive_visitors]
#[derive(derive_more::From, derive_more::IsVariant)]
pub enum Expression {
    /// A Viper variable.
    ///
    /// Note: This is different from a local variable in other IRs.
    Local(Local),
    /// A Viper field access.
    ///
    /// Note: This is different from a field access in other IRs.
    Field(Field),
    LabelledOld(LabelledOld),
    Constant(Constant),
    MagicWand(MagicWand),
    PredicateAccessPredicate(PredicateAccessPredicate),
    FieldAccessPredicate(FieldAccessPredicate),
    Unfolding(Unfolding),
    UnaryOp(UnaryOp),
    BinOp(BinOp),
    /// Container operation on a Viper container (e.g. Seq index).
    ContainerOp(ContainerOp),
    /// Viper sequence constructor.
    Seq(Seq),
    Conditional(Conditional),
    Quantifier(Quantifier),
    LetExpr(LetExpr),
    FuncApp(FuncApp),
    DomainFuncApp(DomainFuncApp),
    InhaleExhale(InhaleExhale),
}

#[display(fmt = "{}", "variable.name")]
pub struct Local {
    pub variable: VariableDecl,
    pub position: Position,
}

#[display(fmt = "{}.{}", base, "field.name")]
pub struct Field {
    pub base: Box<Expression>,
    pub field: FieldDecl,
    pub position: Position,
}

#[display(fmt = "old{}({})", "display::option!(label, \"[{}]\", \"\")", base)]
pub struct LabelledOld {
    pub label: Option<String>,
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
    Float(FloatConst),
    BitVector(BitVectorConst),
}

pub enum FloatConst {
    F32(u32),
    F64(u64),
}

pub enum BitVectorConst {
    BV8(u8),
    BV16(u16),
    BV32(u32),
    BV64(u64),
    BV128(u128),
}

#[display(fmt = "({} --* {})", left, right)]
pub struct MagicWand {
    pub left: Box<Expression>,
    pub right: Box<Expression>,
    pub position: Position,
}

#[display(fmt = "acc({}({}), {})", name, "display::cjoin(arguments)", permission)]
pub struct PredicateAccessPredicate {
    pub name: String,
    pub arguments: Vec<Expression>,
    pub permission: PermAmount,
    pub position: Position,
}

#[display(fmt = "acc({}, {})", base, permission)]
pub struct FieldAccessPredicate {
    pub base: Box<Expression>,
    pub permission: PermAmount,
    pub position: Position,
}

pub enum PermAmount {
    Read,
    Write,
    /// The permission remaining after ``Read`` was subtracted from ``Write``.
    Remaining,
}

#[display(
    fmt = "(unfolding acc({}({}), {}) in {})",
    predicate,
    "display::cjoin(arguments)",
    permission,
    base
)]
pub struct Unfolding {
    pub predicate: String,
    pub arguments: Vec<Expression>,
    pub permission: PermAmount,
    pub base: Box<Expression>,
    pub position: Position,
}

pub enum UnaryOpKind {
    Not,
    Minus,
}

#[display(fmt = "{}({})", op_kind, argument)]
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

#[display(fmt = "({}) {} ({})", left, op_kind, right)]
pub struct BinOp {
    pub op_kind: BinaryOpKind,
    pub left: Box<Expression>,
    pub right: Box<Expression>,
    pub position: Position,
}

#[display(fmt = "{}{}{}", left, op_kind, right)]
pub struct ContainerOp {
    pub op_kind: ContainerOpKind,
    pub left: Box<Expression>,
    pub right: Box<Expression>,
    pub position: Position,
}

pub enum ContainerOpKind {
    SeqIndex,
    SeqConcat,
    SeqLen,
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

#[display(
    fmt = "{}::{}({})",
    domain_name,
    function_name,
    "display::cjoin(arguments)"
)]
pub struct DomainFuncApp {
    pub domain_name: String,
    pub function_name: String,
    pub arguments: Vec<Expression>,
    pub parameters: Vec<VariableDecl>,
    pub return_type: Type,
    pub position: Position,
}

#[display(fmt = "[{};{}]", inhale_expression, exhale_expression)]
pub struct InhaleExhale {
    pub inhale_expression: Box<Expression>,
    pub exhale_expression: Box<Expression>,
    pub position: Position,
}
