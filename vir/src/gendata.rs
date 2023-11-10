use std::fmt::Debug;

use crate::data::*;
use crate::genrefs::*;
use crate::refs::*;

use vir_proc_macro::*;

#[derive(Reify)]
pub struct UnOpGenData<'vir, Curr, Next> {
    #[reify_copy] pub kind: UnOpKind,
    pub expr: ExprGen<'vir, Curr, Next>,
}

#[derive(Reify)]
pub struct BinOpGenData<'vir, Curr, Next> {
    #[reify_copy] pub kind: BinOpKind,
    pub lhs: ExprGen<'vir, Curr, Next>,
    pub rhs: ExprGen<'vir, Curr, Next>,
}

#[derive(Reify)]
pub struct TernaryGenData<'vir, Curr, Next> {
    pub cond: ExprGen<'vir, Curr, Next>,
    pub then: ExprGen<'vir, Curr, Next>,
    pub else_: ExprGen<'vir, Curr, Next>,
}

#[derive(Reify)]
pub struct ForallGenData<'vir, Curr, Next> {
    #[reify_copy] pub qvars: &'vir [LocalDecl<'vir>],
    pub triggers: &'vir [&'vir [ExprGen<'vir, Curr, Next>]],
    pub body: ExprGen<'vir, Curr, Next>,
}

#[derive(Reify)]
pub struct FuncAppGenData<'vir, Curr, Next> {
    #[reify_copy] pub target: &'vir str, // TODO: identifiers
    pub args: &'vir [ExprGen<'vir, Curr, Next>],
}

#[derive(Reify)]
pub struct PredicateAppGenData<'vir, Curr, Next> {
    #[reify_copy] pub target: &'vir str, // TODO: identifiers
    pub args: &'vir [ExprGen<'vir, Curr, Next>],
}

#[derive(Reify)]
pub struct UnfoldingGenData<'vir, Curr, Next> {
    pub target: PredicateAppGen<'vir, Curr, Next>,
    pub expr: ExprGen<'vir, Curr, Next>,
}

#[derive(Reify)]
pub struct AccFieldGenData<'vir, Curr, Next> {
    pub recv: ExprGen<'vir, Curr, Next>,
    #[reify_copy] pub field: &'vir str, // TODO: identifiers
    // TODO: permission amount
}

#[derive(Reify)]
pub struct LetGenData<'vir, Curr, Next> {
    #[reify_copy] pub name: &'vir str,
    pub val: ExprGen<'vir, Curr, Next>,
    pub expr: ExprGen<'vir, Curr, Next>,
}

/*
// TODO: something like this would be a cleaner solution for ExprGenData's
//   generic; when tested, this runs into an infinite loop in rustc ...?
pub trait GenRow {
    type Curr;
    type Next: GenRow;
}
impl GenRow for () {
    type Curr = !;
    type Next = ();
}
impl<A, B: GenRow> GenRow for fn(A) -> B {
    type Curr = A;
    type Next = B;
}*/

pub enum ExprGenData<'vir, Curr: 'vir, Next: 'vir> {
    Local(Local<'vir>),
    Field(ExprGen<'vir, Curr, Next>, &'vir str), // TODO: FieldApp?
    Old(ExprGen<'vir, Curr, Next>),
    //LabelledOld(Expr<'vir>, &'vir str),
    Const(Const<'vir>),
    // magic wand
    AccField(AccFieldGen<'vir, Curr, Next>),
    Unfolding(UnfoldingGen<'vir, Curr, Next>),
    UnOp(UnOpGen<'vir, Curr, Next>),
    BinOp(BinOpGen<'vir, Curr, Next>),
    // perm ops?
    // container ops?
    // map ops?
    // sequence, map, set, multiset literals
    Ternary(TernaryGen<'vir, Curr, Next>),
    Forall(ForallGen<'vir, Curr, Next>),
    Let(LetGen<'vir, Curr, Next>),
    FuncApp(FuncAppGen<'vir, Curr, Next>),
    PredicateApp(PredicateAppGen<'vir, Curr, Next>), // TODO: this should not be used instead of acc?
    // domain func app
    // inhale/exhale

    Lazy(&'vir str, Box<dyn for <'a> Fn(&'vir crate::VirCtxt<'a>, Curr) -> Next + 'vir>),

    Todo(&'vir str),
}
impl<'vir, Curr, Next> ExprGenData<'vir, Curr, Next> {
    pub fn lift<Prev>(&self) -> ExprGen<'vir, Prev, ExprGen<'vir, Curr, Next>> {
        match self {
            Self::Lazy(..) => panic!("cannot lift lazy expression"),
            e => unsafe { std::mem::transmute(e) },
        }
    }
}
// + position, meta?

#[derive(Reify)]
pub struct DomainAxiomGenData<'vir, Curr, Next> {
    #[reify_copy] pub name: &'vir str, // ? or comment, then auto-gen the names?
    pub expr: ExprGen<'vir, Curr, Next>,
}

#[derive(Reify)]
pub struct DomainGenData<'vir, Curr, Next> {
    #[reify_copy] pub name: &'vir str, // TODO: identifiers
    #[reify_copy] pub typarams: &'vir [&'vir str],
    pub axioms: &'vir [DomainAxiomGen<'vir, Curr, Next>],
    #[reify_copy] pub functions: &'vir [DomainFunction<'vir>],
}

#[derive(Reify)]
pub struct PredicateGenData<'vir, Curr, Next> {
    #[reify_copy] pub name: &'vir str, // TODO: identifiers
    #[reify_copy] pub args: &'vir [LocalDecl<'vir>],
    pub expr: Option<ExprGen<'vir, Curr, Next>>,
}

#[derive(Reify)]
pub struct FunctionGenData<'vir, Curr, Next> {
    #[reify_copy] pub name: &'vir str, // TODO: identifiers
    #[reify_copy] pub args: &'vir [LocalDecl<'vir>],
    #[reify_copy] pub ret: Type<'vir>,
    pub pres: &'vir [ExprGen<'vir, Curr, Next>],
    pub posts: &'vir [ExprGen<'vir, Curr, Next>],
    pub expr: Option<ExprGen<'vir, Curr, Next>>,
}

// TODO: why is this called "pure"?
#[derive(Reify)]
pub struct PureAssignGenData<'vir, Curr, Next> {
    pub lhs: ExprGen<'vir, Curr, Next>,
    //pub dest: Local<'vir>,
    //pub projs: &'vir [&'vir str],
    pub rhs: ExprGen<'vir, Curr, Next>,
}

#[derive(Reify)]
pub struct MethodCallGenData<'vir, Curr, Next> {
    #[reify_copy] pub targets: &'vir [Local<'vir>],
    #[reify_copy] pub method: &'vir str,
    pub args: &'vir [ExprGen<'vir, Curr, Next>],
}

#[derive(Reify)]
pub enum StmtGenData<'vir, Curr, Next> {
    LocalDecl(#[reify_copy] LocalDecl<'vir>, Option<ExprGen<'vir, Curr, Next>>),
    PureAssign(PureAssignGen<'vir, Curr, Next>),
    Inhale(ExprGen<'vir, Curr, Next>),
    Exhale(ExprGen<'vir, Curr, Next>),
    Unfold(PredicateAppGen<'vir, Curr, Next>),
    Fold(PredicateAppGen<'vir, Curr, Next>),
    MethodCall(MethodCallGen<'vir, Curr, Next>),
    Comment(#[reify_copy] &'vir str),
    Dummy(#[reify_copy] &'vir str),
}

#[derive(Reify)]
pub struct GotoIfGenData<'vir, Curr, Next> {
    pub value: ExprGen<'vir, Curr, Next>,
    pub targets: &'vir [(ExprGen<'vir, Curr, Next>, CfgBlockLabel<'vir>)],
    #[reify_copy] pub otherwise: CfgBlockLabel<'vir>,
}

#[derive(Reify)]
pub enum TerminatorStmtGenData<'vir, Curr, Next> {
    AssumeFalse,
    Goto(#[reify_copy] CfgBlockLabel<'vir>),
    GotoIf(GotoIfGen<'vir, Curr, Next>),
    Exit,
    Dummy(#[reify_copy] &'vir str),
}

#[derive(Debug, Reify)]
pub struct CfgBlockGenData<'vir, Curr, Next> {
    #[reify_copy] pub label: CfgBlockLabel<'vir>,
    pub stmts: &'vir [StmtGen<'vir, Curr, Next>],
    pub terminator: TerminatorStmtGen<'vir, Curr, Next>,
}

#[derive(Reify)]
pub struct MethodGenData<'vir, Curr, Next> {
    #[reify_copy] pub name: &'vir str, // TODO: identifiers
    #[reify_copy] pub args: &'vir [LocalDecl<'vir>],
    #[reify_copy] pub rets: &'vir [LocalDecl<'vir>],
    // TODO: pre/post - add a comment variant
    pub pres: &'vir [ExprGen<'vir, Curr, Next>],
    pub posts: &'vir [ExprGen<'vir, Curr, Next>],
    pub blocks: Option<&'vir [CfgBlockGen<'vir, Curr, Next>]>, // first one is the entrypoint
}

#[derive(Debug, Reify)]
pub struct ProgramGenData<'vir, Curr, Next> {
    #[reify_copy] pub fields: &'vir [Field<'vir>],
    pub domains: &'vir [DomainGen<'vir, Curr, Next>],
    pub predicates: &'vir [PredicateGen<'vir, Curr, Next>],
    pub functions: &'vir [FunctionGen<'vir, Curr, Next>],
    pub methods: &'vir [MethodGen<'vir, Curr, Next>],
    // verification flags?
}
