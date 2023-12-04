use std::fmt::Debug;

use crate::data::*;
use crate::genrefs::*;
use crate::refs::*;

use vir_proc_macro::*;

#[derive(Reify)]
pub struct UnOpGenData<'vir, Curr, Next> {
    #[reify_copy] pub(crate) kind: UnOpKind,
    pub(crate) expr: ExprGen<'vir, Curr, Next>,
}

#[derive(Reify)]
pub struct BinOpGenData<'vir, Curr, Next> {
    #[reify_copy] pub(crate) kind: BinOpKind,
    pub(crate) lhs: ExprGen<'vir, Curr, Next>,
    pub(crate) rhs: ExprGen<'vir, Curr, Next>,
}

#[derive(Reify)]
pub struct TernaryGenData<'vir, Curr, Next> {
    pub(crate) cond: ExprGen<'vir, Curr, Next>,
    pub(crate) then: ExprGen<'vir, Curr, Next>,
    pub(crate) else_: ExprGen<'vir, Curr, Next>,
}

#[derive(Reify)]
pub struct ForallGenData<'vir, Curr, Next> {
    #[reify_copy] pub(crate) qvars: &'vir [LocalDecl<'vir>],
    pub(crate) triggers: &'vir [&'vir [ExprGen<'vir, Curr, Next>]],
    pub(crate) body: ExprGen<'vir, Curr, Next>,
}

#[derive(Reify)]
pub struct FuncAppGenData<'vir, Curr, Next> {
    #[reify_copy] pub(crate) target: &'vir str, // TODO: identifiers
    pub(crate) args: &'vir [ExprGen<'vir, Curr, Next>],
    #[reify_copy] pub(crate) result_ty: Option<Type<'vir>>,
}

#[derive(Reify)]
pub struct PredicateAppGenData<'vir, Curr, Next> {
    #[reify_copy] pub(crate) target: &'vir str, // TODO: identifiers
    pub(crate) args: &'vir [ExprGen<'vir, Curr, Next>],
    pub(crate) perm: Option<ExprGen<'vir, Curr, Next>>,
}

#[derive(Reify)]
pub struct UnfoldingGenData<'vir, Curr, Next> {
    pub(crate) target: PredicateAppGen<'vir, Curr, Next>,
    pub(crate) expr: ExprGen<'vir, Curr, Next>,
}

#[derive(Reify)]
pub struct AccFieldGenData<'vir, Curr, Next> {
    pub(crate) recv: ExprGen<'vir, Curr, Next>,
    #[reify_copy] pub(crate) field: Field<'vir>, // TODO: identifiers
    pub(crate) perm: Option<ExprGen<'vir, Curr, Next>>,
}

#[derive(Reify)]
pub struct LetGenData<'vir, Curr, Next> {
    #[reify_copy] pub(crate) name: &'vir str,
    pub(crate) val: ExprGen<'vir, Curr, Next>,
    pub(crate) expr: ExprGen<'vir, Curr, Next>,
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


// TODO add position and other metadata
pub struct ExprGenData<'vir, Curr: 'vir, Next: 'vir>{
    pub kind: ExprKindGen<'vir, Curr, Next>
}

pub enum ExprKindGenData<'vir, Curr: 'vir, Next: 'vir> {
    Local(Local<'vir>),
    Field(ExprGen<'vir, Curr, Next>, Field<'vir>), // TODO: FieldApp?
    Old(ExprGen<'vir, Curr, Next>),
    //LabelledOld(Expr<'vir>, &'vir str),
    Const(Const<'vir>),
    Result,
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
    pub fn lift<Prev>(&self) -> ExprGen<'vir, Prev, ExprKindGen<'vir, Curr, Next>> {
        match self.kind {
            ExprKindGenData::Lazy(..) => panic!("cannot lift lazy expression"),
            _ => unsafe { std::mem::transmute(self) },
        }
    }
}

#[derive(Reify)]
pub struct DomainAxiomGenData<'vir, Curr, Next> {
    #[reify_copy] pub(crate) name: &'vir str, // ? or comment, then auto-gen the names?
    pub(crate) expr: ExprGen<'vir, Curr, Next>,
}

#[derive(Reify)]
pub struct DomainGenData<'vir, Curr, Next> {
    #[reify_copy] pub(crate) name: &'vir str, // TODO: identifiers
    #[reify_copy] pub(crate) typarams: &'vir [DomainParamData<'vir>],
    pub(crate) axioms: &'vir [DomainAxiomGen<'vir, Curr, Next>],
    #[reify_copy] pub(crate) functions: &'vir [DomainFunction<'vir>],
}

#[derive(Reify)]
pub struct PredicateGenData<'vir, Curr, Next> {
    #[reify_copy] pub(crate) name: &'vir str, // TODO: identifiers
    #[reify_copy] pub(crate) args: &'vir [LocalDecl<'vir>],
    pub(crate) expr: Option<ExprGen<'vir, Curr, Next>>,
}

#[derive(Reify)]
pub struct FunctionGenData<'vir, Curr, Next> {
    #[reify_copy] pub(crate) name: &'vir str, // TODO: identifiers
    #[reify_copy] pub(crate) args: &'vir [LocalDecl<'vir>],
    #[reify_copy] pub(crate) ret: Type<'vir>,
    pub(crate) pres: &'vir [ExprGen<'vir, Curr, Next>],
    pub(crate) posts: &'vir [ExprGen<'vir, Curr, Next>],
    pub(crate) expr: Option<ExprGen<'vir, Curr, Next>>,
}

// TODO: why is this called "pure"?
#[derive(Reify)]
pub struct PureAssignGenData<'vir, Curr, Next> {
    pub(crate) lhs: ExprGen<'vir, Curr, Next>,
    //pub dest: Local<'vir>,
    //pub projs: &'vir [&'vir str],
    pub(crate) rhs: ExprGen<'vir, Curr, Next>,
}

#[derive(Reify)]
pub struct MethodCallGenData<'vir, Curr, Next> {
    #[reify_copy] pub(crate) targets: &'vir [Local<'vir>],
    #[reify_copy] pub(crate) method: &'vir str,
    pub(crate) args: &'vir [ExprGen<'vir, Curr, Next>],
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
    pub(crate) value: ExprGen<'vir, Curr, Next>,
    pub(crate) targets: &'vir [(
        ExprGen<'vir, Curr, Next>,
        CfgBlockLabel<'vir>,
        &'vir [StmtGen<'vir, Curr, Next>],
    )],
    #[reify_copy] pub(crate) otherwise: CfgBlockLabel<'vir>,
    pub(crate) otherwise_statements: &'vir [StmtGen<'vir, Curr, Next>],
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
    #[reify_copy] pub(crate) label: CfgBlockLabel<'vir>,
    pub(crate) stmts: &'vir [StmtGen<'vir, Curr, Next>],
    pub(crate) terminator: TerminatorStmtGen<'vir, Curr, Next>,
}

#[derive(Reify)]
pub struct MethodGenData<'vir, Curr, Next> {
    #[reify_copy] pub(crate) name: &'vir str, // TODO: identifiers
    #[reify_copy] pub(crate) args: &'vir [LocalDecl<'vir>],
    #[reify_copy] pub(crate) rets: &'vir [LocalDecl<'vir>],
    // TODO: pre/post - add a comment variant
    pub(crate) pres: &'vir [ExprGen<'vir, Curr, Next>],
    pub(crate) posts: &'vir [ExprGen<'vir, Curr, Next>],
    pub(crate) blocks: Option<&'vir [CfgBlockGen<'vir, Curr, Next>]>, // first one is the entrypoint
}

#[derive(Debug, Reify)]
pub struct ProgramGenData<'vir, Curr, Next> {
    #[reify_copy] pub(crate) fields: &'vir [Field<'vir>],
    pub(crate) domains: &'vir [DomainGen<'vir, Curr, Next>],
    pub(crate) predicates: &'vir [PredicateGen<'vir, Curr, Next>],
    pub(crate) functions: &'vir [FunctionGen<'vir, Curr, Next>],
    pub(crate) methods: &'vir [MethodGen<'vir, Curr, Next>],
    // verification flags?
}
