pub(crate) use super::{
    field::FieldDecl,
    position::Position,
    predicate::Predicate,
    ty::{Type, VariantIndex},
    variable::VariableDecl,
};
use crate::common::display;
pub use crate::polymorphic::FloatConst;

#[derive_helpers]
#[derive_visitors]
#[derive(derive_more::From, derive_more::IsVariant, derive_more::Unwrap)]
pub enum Expression {
    /// A local variable.
    Local(Local),
    /// A constructor of a complex type.
    Constructor(Constructor),
    /// An enum variant.
    Variant(Variant),
    /// A field access. (Field accesses can never fail.)
    Field(Field),
    /// A reference or pointer dereference. (Sometimes can fail.)
    Deref(Deref),
    /// A reference or pointer dereference. (Sometimes can fail.)
    Final(Final),
    /// The inverse of Deref.
    AddrOf(AddrOf),
    LabelledOld(LabelledOld),
    Constant(Constant),
    UnaryOp(UnaryOp),
    BinaryOp(BinaryOp),
    /// Container Operation on a Viper container (e.g. Seq index)
    ContainerOp(ContainerOp),
    /// Viper Seq
    Seq(Seq),
    Conditional(Conditional),
    Quantifier(Quantifier),
    /// let variable == (expr) in body
    LetExpr(LetExpr),
    FuncApp(FuncApp),
    BuiltinFuncApp(BuiltinFuncApp),
    /// Inform the fold-unfold algorithm that at this program point a enum type can be downcasted
    /// to one of its variants. This statement is a no-op for Viper.
    /// Arguments:
    /// * expression in which the downcast is visible
    /// * place to the enumeration that is downcasted
    /// * field that encodes the variant
    // FIXME: Is downcast really needed? Isn't variant enough?
    Downcast(Downcast),
    /// An accessibility predicate such as `own`.
    AccPredicate(AccPredicate),
    /// An unpacking of an accessibility predicate.
    Unfolding(Unfolding),
    /// `eval_in(predicate, argument)` expression.
    EvalIn(EvalIn),
}

#[display(fmt = "{}", "variable.name")]
pub struct Local {
    pub variable: VariableDecl,
    pub position: Position,
}

#[display(fmt = "{}({})", ty, "display::cjoin(arguments)")]
pub struct Constructor {
    /// The type to be constructed.
    pub ty: Type,
    /// The arguments passed to the constructor.
    pub arguments: Vec<Expression>,
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

#[display(fmt = "{}.^", base)]
pub struct Final {
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
    Float(FloatConst),
    String(String),
    /// All function pointers share the same constant, because their function
    /// is determined by the type system.
    FnPtr,
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
    LifetimeIntersection,
}

#[display(fmt = "({}) {} ({})", left, op_kind, right)]
pub struct BinaryOp {
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

#[display(fmt = "({} {} {})", left, op_kind, right)]
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
    pub type_arguments: Vec<Type>,
    pub arguments: Vec<Expression>,
    pub parameters: Vec<VariableDecl>,
    pub return_type: Type,
    pub position: Position,
}

#[derive(Copy)]
pub enum BuiltinFunc {
    SnapshotEquality,
    Size,
    PaddingSize,
    Align,
    Discriminant,
    LifetimeIncluded,
    LifetimeIntersect,
    EmptyMap,
    UpdateMap,
    MapContains,
    LookupMap,
    MapLen,
    EmptySeq,
    SingleSeq,
    LookupSeq,
    ConcatSeq,
    SeqLen,
    NewInt,
    Index,
    Len,
    /// A ghost function for computing offset.
    PtrAddressOffset,
    /// Special-cased `wrapping_offset` function on pointers.
    PtrWrappingOffset,
    /// Special-cased `offset` function on pointers.
    PtrOffset,
    /// Special-cased `is_null` function on pointers.
    PtrIsNull,
    IsValid, // TODO: Delete.
    EnsureOwnedPredicate,
    // GetSnapshot,
    /// Take the inner-most lifetime of a place.
    TakeLifetime,
    /// Read a single Byte from a sequence of Bytes.
    ReadByte,
    /// Retrieve the bytes of a memory block.
    MemoryBlockBytes,
    /// Dereference a raw pointer at a given index.
    DerefOwn,
    /// Cast `*mut T` to `*const T`.
    CastMutToConstPointer,
    /// Cast from some integer type to another.
    CastIntToInt,
    BeforeExpiry,
    AfterExpiry,
    /// A function represents UniqueRef with its arguments not yet properly typed.
    BuildingUniqueRefPredicate,
    /// A function represents FracRef with its arguments not yet properly typed.
    BuildingFracRefPredicate,
}

#[display(fmt = "__builtin__{}({})", function, "display::cjoin(arguments)")]
pub struct BuiltinFuncApp {
    pub function: BuiltinFunc,
    pub type_arguments: Vec<Type>,
    pub arguments: Vec<Expression>,
    pub return_type: Type,
    pub position: Position,
}

// FIXME: Is downcast really needed? Isn't variant enough?
#[display(fmt = "(downcast {} to {} in {})", enum_place, "field.name", base)]
pub struct Downcast {
    pub base: Box<Expression>,
    pub enum_place: Box<Expression>,
    pub field: FieldDecl,
    pub position: Position,
}

#[display(fmt = "acc({})", predicate)]
pub struct AccPredicate {
    pub predicate: Box<Predicate>,
    pub position: Position,
}

#[display(fmt = "unfolding({}, {})", predicate, body)]
pub struct Unfolding {
    pub predicate: Box<Predicate>,
    pub body: Box<Expression>,
    pub position: Position,
}

#[derive(Copy)]
pub enum EvalInContextKind {
    /// The standard `eval_in(acc(...), ...)` context.
    Predicate,
    /// Like `Predicate`, but the predicate is an opened ref predicate.
    OpenedRefPredicate,
    /// This is a `folding` expression generated by fold-unfold.
    SafeConstructor,
    /// The `eval_in(old(...), ...)` context.
    Old,
    /// Like `Old`, but the predicate is an opened ref predicate.
    OldOpenedRefPredicate,
}

#[display(fmt = "eval_in<{}>({}, {})", context_kind, context, body)]
pub struct EvalIn {
    pub context: Box<Expression>,
    pub context_kind: EvalInContextKind,
    pub body: Box<Expression>,
    pub position: Position,
}
