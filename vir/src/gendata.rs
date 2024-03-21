use std::fmt::Debug;

use crate::data::*;
use crate::debug_info::DebugInfo;
use crate::genrefs::*;
use crate::refs::*;

use vir_proc_macro::*;

#[derive(VirHash, VirReify, VirSerde)]
pub struct UnOpGenData<'vir, Curr, Next> {
    #[vir(reify_pass)] pub kind: UnOpKind,
    pub expr: ExprGen<'vir, Curr, Next>,
}

#[derive(VirHash, VirReify, VirSerde)]
pub struct BinOpGenData<'vir, Curr, Next> {
    #[vir(reify_pass)] pub kind: BinOpKind,
    pub lhs: ExprGen<'vir, Curr, Next>,
    pub rhs: ExprGen<'vir, Curr, Next>,
}

impl<'vir, Curr, Next> BinOpGenData<'vir, Curr, Next> {
    pub fn ty(&self) -> Type<'vir> {
        match self.kind {
              BinOpKind::CmpEq
            | BinOpKind::CmpNe
            | BinOpKind::CmpGt
            | BinOpKind::CmpLt
            | BinOpKind::CmpGe
            | BinOpKind::CmpLe => &TypeData::Bool,
            BinOpKind::And | BinOpKind::Or => &TypeData::Bool,
            BinOpKind::Add | BinOpKind::Sub | BinOpKind::Mul | BinOpKind::Div | BinOpKind::Mod => self.lhs.ty(),
        }
    }
}

#[derive(VirHash, VirReify, VirSerde)]
pub struct TernaryGenData<'vir, Curr, Next> {
    pub cond: ExprGen<'vir, Curr, Next>,
    pub then: ExprGen<'vir, Curr, Next>,
    pub else_: ExprGen<'vir, Curr, Next>,
}

#[derive(VirHash, VirReify, VirSerde)]
pub struct ForallGenData<'vir, Curr, Next> {
    #[vir(reify_pass)] pub qvars: &'vir [LocalDecl<'vir>],
    pub triggers: &'vir [TriggerGen<'vir, Curr, Next>],
    pub body: ExprGen<'vir, Curr, Next>,
}

#[derive(VirHash, VirReify, VirSerde)]
pub struct TriggerGenData<'vir, Curr, Next> {
    pub exprs: &'vir [ExprGen<'vir, Curr, Next>],
}

#[derive(VirHash, VirReify, VirSerde)]
pub struct FuncAppGenData<'vir, Curr, Next> {
    pub target: &'vir str, // TODO: identifiers
    pub args: &'vir [ExprGen<'vir, Curr, Next>],
    #[vir(reify_pass, is_ref)] pub result_ty: Type<'vir>,
}

#[derive(VirHash, VirReify, VirSerde)]
pub struct PredicateAppGenData<'vir, Curr, Next> {
    pub target: &'vir str, // TODO: identifiers
    pub args: &'vir [ExprGen<'vir, Curr, Next>],
    pub perm: Option<ExprGen<'vir, Curr, Next>>,
}

#[derive(VirHash, VirReify, VirSerde)]
pub struct UnfoldingGenData<'vir, Curr, Next> {
    pub target: PredicateAppGen<'vir, Curr, Next>,
    pub expr: ExprGen<'vir, Curr, Next>,
}

#[derive(VirHash, VirReify, VirSerde)]
pub struct AccFieldGenData<'vir, Curr, Next> {
    pub recv: ExprGen<'vir, Curr, Next>,
    #[vir(reify_pass, is_ref)] pub field: Field<'vir>, // TODO: identifiers
    pub perm: Option<ExprGen<'vir, Curr, Next>>,
}

#[derive(VirHash, VirReify, VirSerde)]
pub struct LetGenData<'vir, Curr, Next> {
    pub name: &'vir str,
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

// TODO add position and other metadata
#[derive(VirHash, VirSerde)]
pub struct ExprGenData<'vir, Curr: 'vir, Next: 'vir> {
    pub kind: ExprKindGen<'vir, Curr, Next>,
    #[vir(reify_pass)] pub debug_info: DebugInfo,
}

impl <'vir, Curr: 'vir, Next: 'vir> ExprGenData<'vir, Curr, Next> {
    pub fn new(kind: ExprKindGen<'vir, Curr, Next>) -> Self {
        Self {
            kind,
            debug_info: DebugInfo::new(),
        }
    }
}

#[derive(VirHash, VirSerde)]
pub enum ExprKindGenData<'vir, Curr: 'vir, Next: 'vir> {
    Local(Local<'vir>),
    Field(ExprGen<'vir, Curr, Next>, Field<'vir>), // TODO: FieldApp?
    Old(ExprGen<'vir, Curr, Next>),
    //LabelledOld(Expr<'vir>, &'vir str),
    Const(Const<'vir>),
    /// Result of a pure function
    Result(Type<'vir>),
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

    Lazy(LazyGen<'vir, Curr, Next>),

    Todo(&'vir str),
}

unsafe impl<'vir> Send for ExprKindGenData<'vir, !, !> {}
unsafe impl<'vir> Sync for ExprKindGenData<'vir, !, !> {}

impl<'vir, Curr, Next> ExprKindGenData<'vir, Curr, Next> {
    pub fn ty(&self) -> Type<'vir> {
        match self {
            ExprKindGenData::Local(l) => l.ty,
            ExprKindGenData::Field(_, f) => f.ty,
            ExprKindGenData::Old(e) => e.ty(),
            ExprKindGenData::Const(c) => c.ty(),
            ExprKindGenData::Result(ty) => ty,
            ExprKindGenData::AccField(_) => &TypeData::Bool,
            ExprKindGenData::Unfolding(f) => f.expr.ty(),
            ExprKindGenData::UnOp(u) => u.expr.ty(),
            ExprKindGenData::BinOp(b) => b.ty(),
            ExprKindGenData::Ternary(t) => t.then.ty(),
            ExprKindGenData::Forall(_) => &TypeData::Bool,
            ExprKindGenData::Let(l) => l.expr.ty(),
            ExprKindGenData::FuncApp(a) => a.result_ty,
            ExprKindGenData::PredicateApp(_) => &TypeData::Predicate,
            ExprKindGenData::Lazy(_) => panic!("cannot get type of lazy expression"),
            ExprKindGenData::Todo(msg) => panic!("{msg}")
        }
    }
}

impl<'vir, Curr, Next> ExprGenData<'vir, Curr, Next> {
    pub fn ty(&self) -> Type<'vir> {
        self.kind.ty()
    }
    pub fn lift<Prev>(&self) -> ExprGen<'vir, Prev, ExprKindGen<'vir, Curr, Next>> {
        match self.kind {
            ExprKindGenData::Lazy(_) => panic!("cannot lift lazy expression"),
            _ => unsafe { std::mem::transmute(self) },
        }
    }
}

pub struct LazyGenData<'vir, Curr: 'vir, Next: 'vir> {
    pub name: &'vir str,
    pub func: Box<dyn for <'a> Fn(&'vir crate::VirCtxt<'a>, Curr) -> Next + 'vir>,
}

impl<'vir, Curr: 'vir, Next: 'vir> std::hash::Hash for LazyGenData<'vir, Curr, Next> {
    fn hash<H>(&self, state: &mut H)
    where H: std::hash::Hasher
    {
        panic!("cannot hash lazy expression {}", self.name)
    }
}
impl<'vir, Curr: 'vir, Next: 'vir> serde::Serialize for LazyGenData<'vir, Curr, Next> {
    fn serialize<S>(&self, _serializer: S) -> Result<S::Ok, S::Error>
    where S: serde::ser::Serializer
    {
        panic!("cannot serialize lazy expression {}", self.name)
    }
}
impl<'vir, Curr: 'vir, Next: 'vir> serde::Deserialize<'vir> for LazyGenData<'vir, Curr, Next> {
    fn deserialize<D>(_deserializer: D) -> Result<Self, D::Error>
    where D: serde::de::Deserializer<'vir>
    {
        panic!("cannot deserialize lazy expression")
    }
}

#[derive(VirHash, VirReify, VirSerde)]
pub struct DomainAxiomGenData<'vir, Curr, Next> {
    pub name: &'vir str, // ? or comment, then auto-gen the names?
    pub expr: ExprGen<'vir, Curr, Next>,
}

#[derive(VirHash, VirReify, VirSerde)]
pub struct DomainGenData<'vir, Curr, Next> {
    pub name: &'vir str, // TODO: identifiers
    #[vir(reify_pass)] pub typarams: &'vir [DomainParam<'vir>],
    pub axioms: &'vir [DomainAxiomGen<'vir, Curr, Next>],
    #[vir(reify_pass)] pub functions: &'vir [DomainFunction<'vir>],
}

#[derive(VirHash, VirReify, VirSerde)]
pub struct PredicateGenData<'vir, Curr, Next> {
    pub name: &'vir str, // TODO: identifiers
    #[vir(reify_pass)] pub args: &'vir [LocalDecl<'vir>],
    pub expr: Option<ExprGen<'vir, Curr, Next>>,
}

#[derive(VirHash, VirReify, VirSerde)]
pub struct FunctionGenData<'vir, Curr, Next> {
    pub name: &'vir str, // TODO: identifiers
    #[vir(reify_pass)] pub args: &'vir [LocalDecl<'vir>],
    #[vir(reify_pass, is_ref)] pub ret: Type<'vir>,
    pub pres: &'vir [ExprGen<'vir, Curr, Next>],
    pub posts: &'vir [ExprGen<'vir, Curr, Next>],
    pub expr: Option<ExprGen<'vir, Curr, Next>>,
}

// TODO: why is this called "pure"?
#[derive(VirHash, VirReify, VirSerde)]
pub struct PureAssignGenData<'vir, Curr, Next> {
    pub lhs: ExprGen<'vir, Curr, Next>,
    //pub dest: Local<'vir>,
    //pub projs: &'vir [&'vir str],
    pub rhs: ExprGen<'vir, Curr, Next>,
}

#[derive(VirHash, VirReify, VirSerde)]
pub struct MethodCallGenData<'vir, Curr, Next> {
    #[vir(reify_pass)] pub targets: &'vir [Local<'vir>],
    pub method: &'vir str,
    pub args: &'vir [ExprGen<'vir, Curr, Next>],
}

#[derive(VirHash, VirReify, VirSerde)]
pub enum StmtGenData<'vir, Curr, Next> {
    LocalDecl(
        #[vir(reify_pass, is_ref)] LocalDecl<'vir>,
        Option<ExprGen<'vir, Curr, Next>>,
    ),
    PureAssign(PureAssignGen<'vir, Curr, Next>),
    Inhale(ExprGen<'vir, Curr, Next>),
    Exhale(ExprGen<'vir, Curr, Next>),
    Unfold(PredicateAppGen<'vir, Curr, Next>),
    Fold(PredicateAppGen<'vir, Curr, Next>),
    MethodCall(MethodCallGen<'vir, Curr, Next>),
    Comment(&'vir str),
    Dummy(&'vir str),
}

#[derive(VirHash, VirReify, VirSerde)]
pub struct GotoIfGenData<'vir, Curr, Next> {
    pub value: ExprGen<'vir, Curr, Next>,
    pub targets: &'vir [GotoIfTargetGen<'vir, Curr, Next>],
    #[vir(reify_pass, is_ref)] pub otherwise: CfgBlockLabel<'vir>,
    pub otherwise_statements: &'vir [StmtGen<'vir, Curr, Next>],
}

#[derive(VirHash, VirReify, VirSerde)]
pub struct GotoIfTargetGenData<'vir, Curr, Next> {
    pub value: ExprGen<'vir, Curr, Next>,
    #[vir(reify_pass, is_ref)] pub label: CfgBlockLabel<'vir>,
    pub statements: &'vir [StmtGen<'vir, Curr, Next>],
}

#[derive(VirHash, VirReify, VirSerde)]
pub enum TerminatorStmtGenData<'vir, Curr, Next> {
    AssumeFalse,
    Goto(#[vir(reify_pass, is_ref)] CfgBlockLabel<'vir>),
    GotoIf(GotoIfGen<'vir, Curr, Next>),
    Exit,
    Dummy(&'vir str),
}

#[derive(Debug, VirHash, VirReify, VirSerde)]
pub struct CfgBlockGenData<'vir, Curr, Next> {
    #[vir(reify_pass, is_ref)] pub label: CfgBlockLabel<'vir>,
    pub stmts: &'vir [StmtGen<'vir, Curr, Next>],
    pub terminator: TerminatorStmtGen<'vir, Curr, Next>,
}

#[derive(VirHash, VirReify, VirSerde)]
pub struct MethodGenData<'vir, Curr, Next> {
    pub name: &'vir str, // TODO: identifiers
    #[vir(reify_pass)] pub args: &'vir [LocalDecl<'vir>],
    #[vir(reify_pass)] pub rets: &'vir [LocalDecl<'vir>],
    // TODO: pre/post - add a comment variant
    pub pres: &'vir [ExprGen<'vir, Curr, Next>],
    pub posts: &'vir [ExprGen<'vir, Curr, Next>],
    pub body: Option<MethodBodyGen<'vir, Curr, Next>>,
}

#[derive(VirHash, VirReify, VirSerde)]
pub struct MethodBodyGenData<'vir, Curr, Next> {
    pub blocks: &'vir [CfgBlockGen<'vir, Curr, Next>], // first one is the entrypoint
}

#[derive(Debug, VirHash, VirReify, VirSerde)]
pub struct ProgramGenData<'vir, Curr, Next> {
    #[vir(reify_pass)] pub fields: &'vir [Field<'vir>],
    pub domains: &'vir [DomainGen<'vir, Curr, Next>],
    pub predicates: &'vir [PredicateGen<'vir, Curr, Next>],
    pub functions: &'vir [FunctionGen<'vir, Curr, Next>],
    pub methods: &'vir [MethodGen<'vir, Curr, Next>],
    // verification flags?
}

impl<'vir> ProgramGenData<'vir, !, !> {
    pub fn to_ref(&self) -> crate::ProgramRef {
        use std::hash::{Hash, Hasher};
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        self.hash(&mut hasher);
        crate::ProgramRef {
            hash: hasher.finish(),
            // SAFETY: this transmutes a `'vir` (or shorter) reference to a
            //   `'static` reference. The reference is not used except in
            //   `VirCtxt::get_program`. See comment there.
            program: unsafe { std::mem::transmute(self) },
        }
    }
}

// TODO: remove this, it is here only to fit the old API
impl<'vir, Curr, Next> ProgramGenData<'vir, Curr, Next> {
    pub fn get_name(&self) -> &str { "program" }
    pub fn get_check_mode(&self) -> &str { "check" }
    pub fn get_name_with_check_mode(&self) -> &str { "program-check" }
    pub fn set_name(&mut self, _name: &str) {}
}

#[cfg(test)]
mod tests {
    macro_rules! roundtrip_test_eq {
        ($name:ident, $vcx:ident, $val:expr) => {
            #[test]
            fn $name() {
                crate::init_vcx(crate::VirCtxt::new_without_tcx());
                let a = crate::with_vcx(|$vcx| $val);
                let b = bincode::serialize(&a).unwrap();
                let old_vcx = crate::replace_vcx(crate::VirCtxt::new_without_tcx()).unwrap();
                let c = bincode::deserialize(&b[..]).unwrap();
                assert_eq!(a, c);
                drop(old_vcx);
            }
        };
    }
    macro_rules! roundtrip_test_match {
        ($name:ident, $vcx:ident, $val:expr, $exp:pat) => {
            #[test]
            fn $name() {
                crate::init_vcx(crate::VirCtxt::new_without_tcx());
                let a = crate::with_vcx(|$vcx| $val);
                let b = bincode::serialize(&a).unwrap();
                let old_vcx = crate::replace_vcx(crate::VirCtxt::new_without_tcx()).unwrap();
                let c = bincode::deserialize(&b[..]).unwrap();
                assert!(matches!(c, $exp));
                drop(old_vcx);
            }
        };
    }

    roundtrip_test_match!(rt_binop, _vcx, crate::BinOpGenData {
        kind: crate::BinOpKind::Sub,
        lhs: &crate::ExprGenData {
            kind: &crate::ExprKindGenData::<!, !>::Todo("todo"),
        },
        rhs: &crate::ExprGenData {
            kind: &crate::ExprKindGenData::<!, !>::Todo("todo"),
        },
    }, crate::BinOpGenData {
        kind: crate::BinOpKind::Sub,
        lhs: &crate::ExprGenData {
            kind: &crate::ExprKindGenData::Todo("todo"),
        },
        rhs: &crate::ExprGenData {
            kind: &crate::ExprKindGenData::Todo("todo"),
        },
    });
    roundtrip_test_eq!(rt_binopkind, _vcx, crate::BinOpKind::Add);
    roundtrip_test_eq!(rt_cfgblocklabel, _vcx, crate::CfgBlockLabelData::BasicBlock(42));
    roundtrip_test_eq!(rt_const, _vcx, crate::ConstData::Int(0x1122334455667788));
    roundtrip_test_eq!(rt_domainfunction, vcx, crate::DomainFunctionData {
        unique: true,
        name: vcx.alloc_str("hello"),
        args: &[&crate::TypeData::Bool],
        ret: &crate::TypeData::Int,
    });
    roundtrip_test_eq!(rt_domainparam, vcx, crate::DomainParamData {
        name: vcx.alloc_str("hello"),
    });
    roundtrip_test_eq!(rt_field, vcx, crate::FieldData {
        name: vcx.alloc_str("hello"),
        ty: &crate::TypeData::Bool,
    });
    roundtrip_test_match!(rt_stmt, _vcx, crate::StmtGenData::<!, !>::Dummy(
        "hello",
    ), crate::StmtGenData::Dummy(
        "hello",
    ));
    roundtrip_test_match!(rt_terminatorstmt, _vcx,
        crate::TerminatorStmtGenData::<!, !>::Exit,
        crate::TerminatorStmtGenData::Exit);
    roundtrip_test_eq!(rt_type, vcx, crate::TypeData::Domain(
        vcx.alloc_str("hello"),
        vcx.alloc_slice(&[
            &crate::TypeData::Bool,
        ]),
    ));
    roundtrip_test_eq!(rt_unopkind, _vcx, crate::UnOpKind::Neg);
    roundtrip_test_eq!(rt_unsupportedtype, vcx, crate::UnsupportedType {
        name: vcx.alloc_str("hello"),
    });

    // TODO: one test for every type in VIR ...
}
