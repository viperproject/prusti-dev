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
    BinaryOp(BinaryOp),
    PermBinaryOp(PermBinaryOp),
    /// Container operation on a Viper container (e.g. Seq index).
    ContainerOp(ContainerOp),
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

/// Note: we do not have explicit constant values for bit vectors and floating
/// points because they are stored as `Int`/`BigInt` and translated into Viper
/// based on the `Constant.ty` field.
pub enum ConstantValue {
    Bool(bool),
    Int(i64),
    Float32(u32),
    Float64(u64),
    BigInt(String),
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
    pub permission: Box<Expression>,
    pub position: Position,
}

#[display(fmt = "acc({}, {})", base, permission)]
pub struct FieldAccessPredicate {
    pub base: Box<Expression>,
    pub permission: Box<Expression>,
    pub position: Position,
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
    pub permission: Box<Expression>,
    pub base: Box<Expression>,
    pub position: Position,
}

#[derive(Copy)]
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

#[derive(Copy)]
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
pub struct BinaryOp {
    pub op_kind: BinaryOpKind,
    pub left: Box<Expression>,
    pub right: Box<Expression>,
    pub position: Position,
}

#[derive(Copy)]
pub enum PermBinaryOpKind {
    Add,
    Sub,
    Mul,
    Div,
}

#[display(fmt = "({}) {} ({})", left, op_kind, right)]
pub struct PermBinaryOp {
    pub op_kind: PermBinaryOpKind,
    pub left: Box<Expression>,
    pub right: Box<Expression>,
    pub position: Position,
}

#[display(
    fmt = "Container{}[{}]({})",
    kind,
    container_type,
    "display::cjoin(operands)"
)]
pub struct ContainerOp {
    pub kind: ContainerOpKind,
    pub container_type: Type,
    pub operands: Vec<Expression>,
    pub position: Position,
}

pub enum ContainerOpKind {
    SeqEmpty,
    SeqConstructor,
    SeqIndex,
    SeqConcat,
    SeqLen,
    MapEmpty,
    MapUpdate,
    MapContains,
    MapLookup,
    MapLen,
    SetEmpty,
    SetConstructor,
    SetUnion,
    SetIntersection,
    SetSubset,
    SetMinus,
    SetContains,
    SetCardinality,
    MultiSetEmpty,
    MultiSetConstructor,
    MultiSetUnion,
    MultiSetIntersection,
    MultiSetSubset,
    MultiSetMinus,
    MultiSetContains,
    MultiSetCardinality,
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
