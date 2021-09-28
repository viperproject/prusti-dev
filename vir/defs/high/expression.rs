use super::{
    position::Position,
    typ::{Type, VariantIndex},
    variable::VariableDecl,
};

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
    Const(Const),
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

pub struct Local {
    pub variable: VariableDecl,
    pub position: Position,
}

pub struct Variant {
    pub base: Box<Expression>,
    pub variant_index: VariantIndex,
    pub position: Position,
}

pub struct Field {
    pub base: Box<Expression>,
    pub name: String,
    pub typ: Type,
    pub position: Position,
}

pub struct Deref {
    pub base: Box<Expression>,
    pub typ: Type,
    pub position: Position,
}

pub struct AddrOf {
    pub base: Box<Expression>,
    pub typ: Type,
    pub position: Position,
}

pub struct LabelledOld {
    pub label: String,
    pub base: Box<Expression>,
    pub position: Position,
}

pub struct Const {
    pub value: ConstValue,
    pub position: Position,
}

pub enum ConstValue {
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

pub struct UnaryOp {
    pub op_kind: UnaryOpKind,
    pub argument: Box<Expression>,
    pub position: Position,
}

pub enum BinOpKind {
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

pub struct BinOp {
    pub op_kind: BinOpKind,
    pub left: Box<Expression>,
    pub right: Box<Expression>,
    pub position: Position,
}

pub enum ContainerOpKind {
    SeqIndex,
    SeqConcat,
    SeqLen,
}

pub struct ContainerOp {
    pub op_kind: ContainerOpKind,
    pub left: Box<Expression>,
    pub right: Box<Expression>,
    pub position: Position,
}

pub struct Seq {
    pub typ: Type,
    pub elements: Vec<Expression>,
    pub position: Position,
}

pub struct Conditional {
    pub guard: Box<Expression>,
    pub then_expr: Box<Expression>,
    pub else_expr: Box<Expression>,
    pub position: Position,
}

pub struct Trigger {
    pub terms: Vec<Expression>,
}

pub enum QuantifierKind {
    ForAll,
    Exists,
}

pub struct Quantifier {
    pub kind: QuantifierKind,
    pub variables: Vec<VariableDecl>,
    pub triggers: Vec<Trigger>,
    pub body: Box<Expression>,
    pub position: Position,
}

pub struct LetExpr {
    pub variable: VariableDecl,
    pub def: Box<Expression>,
    pub body: Box<Expression>,
    pub position: Position,
}

pub struct FuncApp {
    pub function_name: String,
    pub arguments: Vec<Expression>,
    pub formal_arguments: Vec<VariableDecl>,
    pub return_type: Type,
    pub position: Position,
}

pub struct Downcast {
    pub base: Box<Expression>,
    pub enum_place: Box<Expression>,
    pub field: Field,
}
