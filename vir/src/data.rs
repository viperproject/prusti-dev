use serde::{Deserialize, Serialize};
use std::{collections::HashMap, fmt::Debug};

use prusti_rustc_interface::middle::mir;

use crate::{debug_info::DebugInfo, refs::*, viper_ident::ViperIdent, CastType, CompType};

#[derive(Serialize, Deserialize, Hash)]
pub struct LocalData<'vir, T: CompType> {
    #[serde(with = "crate::serde::serde_str")]
    pub name: &'vir str, // TODO: identifiers
    #[serde(with = "crate::serde::serde_ref")]
    pub ty: Type<'vir, T>,
    pub debug_info: DebugInfo<'vir>,
}

#[derive(Eq, PartialEq, Serialize, Deserialize, Hash)]
pub struct LocalDeclData<'vir, T: CompType> {
    #[serde(with = "crate::serde::serde_str")]
    pub name: &'vir str, // TODO: identifiers
    #[serde(with = "crate::serde::serde_ref")]
    pub ty: Type<'vir, T>,
}

#[derive(PartialEq, Eq, Clone, Copy, Debug, Serialize, Deserialize, Hash)]
pub enum UnOpKind {
    Neg,
    Not,
}
impl From<mir::UnOp> for UnOpKind {
    fn from(value: mir::UnOp) -> Self {
        match value {
            mir::UnOp::Not => UnOpKind::Not,
            mir::UnOp::Neg => UnOpKind::Neg,
            mir::UnOp::PtrMetadata => unreachable!(),
        }
    }
}
impl From<&mir::UnOp> for UnOpKind {
    fn from(value: &mir::UnOp) -> Self {
        UnOpKind::from(*value)
    }
}

#[derive(PartialEq, Eq, Clone, Copy, Debug, Serialize, Deserialize, Hash)]
pub enum BinOpKind {
    CmpEq,
    CmpNe,
    CmpGt,
    CmpLt,
    CmpGe,
    CmpLe,
    And,
    Or,
    Implies,
    Add,
    Sub,
    Mul,
    Div,
    DivRational,
    Mod,
    // Set ops
    SetUnion,
    SetIn,
    // ...
}
impl From<mir::BinOp> for BinOpKind {
    fn from(value: mir::BinOp) -> Self {
        match value {
            mir::BinOp::Add | mir::BinOp::AddUnchecked | mir::BinOp::AddWithOverflow => {
                BinOpKind::Add
            }
            mir::BinOp::Sub | mir::BinOp::SubUnchecked | mir::BinOp::SubWithOverflow => {
                BinOpKind::Sub
            }
            mir::BinOp::Mul | mir::BinOp::MulUnchecked | mir::BinOp::MulWithOverflow => {
                BinOpKind::Mul
            }
            mir::BinOp::Div => BinOpKind::Div,
            mir::BinOp::Rem => BinOpKind::Mod,
            // TODO: this is a temporary workaround,
            // we need to fix this for integers and
            // do non-short-circuiting for booleans.
            mir::BinOp::BitXor => BinOpKind::CmpNe,
            mir::BinOp::BitAnd => BinOpKind::And,
            mir::BinOp::BitOr => BinOpKind::Or,
            mir::BinOp::Shl => todo!("bitwise operations"),
            mir::BinOp::ShlUnchecked => todo!("bitwise operations"),
            mir::BinOp::Shr => todo!("bitwise operations"),
            mir::BinOp::ShrUnchecked => todo!("bitwise operations"),
            mir::BinOp::Eq => BinOpKind::CmpEq,
            mir::BinOp::Lt => BinOpKind::CmpLt,
            mir::BinOp::Le => BinOpKind::CmpLe,
            mir::BinOp::Ne => BinOpKind::CmpNe,
            mir::BinOp::Ge => BinOpKind::CmpGe,
            mir::BinOp::Gt => BinOpKind::CmpGt,
            mir::BinOp::Offset => todo!(),
            mir::BinOp::Cmp => todo!(),
        }
    }
}
impl From<&mir::BinOp> for BinOpKind {
    fn from(value: &mir::BinOp) -> Self {
        BinOpKind::from(*value)
    }
}

#[derive(PartialEq, Eq, Clone, Copy, Serialize, Deserialize, Hash)]
pub enum ConstData {
    Bool(bool),
    Int(u128), // TODO: what about negative numbers? larger numbers?
    Wildcard,
    Null,
}

impl ConstData {
    pub fn ty(&self) -> TypePrim<'static> {
        match self {
            ConstData::Bool(_) => crate::TYPE_BOOL.upcast_ty(),
            ConstData::Int(_) => crate::TYPE_INT.upcast_ty(),
            ConstData::Wildcard => crate::TYPE_PERM.upcast_ty(),
            ConstData::Null => crate::TYPE_REF.upcast_ty(),
        }
    }
}

#[derive(PartialEq, Eq, Ord, PartialOrd, Serialize, Deserialize, Hash)]
#[serde(bound(deserialize = "'de: 'vir"))]
pub struct TypeData<'vir, T: CompType> {
    ty: TypeKind<'vir>,
    #[serde(skip)]
    _marker: core::marker::PhantomData<T>,
}

impl<'vir, T: CompType> TypeData<'vir, T> {
    pub(crate) const unsafe fn new_unchecked(ty: TypeKind<'vir>) -> Self {
        Self {
            ty,
            _marker: core::marker::PhantomData,
        }
    }

    pub fn new(ty: TypeKind<'vir>) -> Self {
        let self_ = unsafe { Self::new_unchecked(ty) };
        T::check(&self_);
        self_
    }

    pub fn kind(&self) -> &TypeKind<'vir> {
        &self.ty
    }
}

impl<'vir, T: CompType> core::ops::Deref for TypeData<'vir, T> {
    type Target = TypeKind<'vir>;
    fn deref(&self) -> &Self::Target {
        self.kind()
    }
}

#[derive(PartialEq, Eq, Ord, PartialOrd, Serialize, Deserialize, Hash)]
pub enum TypeKind<'vir> {
    Int,
    Bool,
    DomainTypeParam(DomainParamData<'vir>), // TODO: identifiers
    Domain(
        #[serde(with = "crate::serde::serde_str")] &'vir str, // TODO: identifiers
        #[serde(with = "crate::serde::serde_slice")] &'vir [TypeDyn<'vir>],
    ),
    // TODO: separate `TyParam` variant? `Domain` used for now
    Ref, // TODO: typed references ?
    Perm,
    Set(#[serde(with = "crate::serde::serde_ref")] TypeDyn<'vir>),
    Unsupported(UnsupportedType<'vir>),
    Err,
}

#[derive(PartialEq, Eq, Clone, Ord, PartialOrd, Serialize, Deserialize, Hash)]
pub struct UnsupportedType<'vir> {
    #[serde(with = "crate::serde::serde_str")]
    pub name: &'vir str,
}

pub type TySubsts<'vir> = HashMap<&'vir str, TypeDyn<'vir>>;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Ord, PartialOrd, Serialize, Deserialize, Hash)]
pub struct DomainParamData<'vir> {
    #[serde(with = "crate::serde::serde_str")]
    pub name: &'vir str, // TODO: identifiers
    pub index: usize,
}

#[derive(PartialEq, Eq, Clone, Hash, Serialize, Deserialize)]
pub struct FieldData<'vir, T: CompType> {
    #[serde(with = "crate::serde::serde_str")]
    pub name: &'vir str, // TODO: identifiers
    #[serde(with = "crate::serde::serde_ref")]
    pub ty: Type<'vir, T>,
}

#[derive(Debug, PartialEq, Eq, Clone, Hash, Serialize, Deserialize)]
pub struct AdtDestructorData<'vir, T: CompType, R: CompType> {
    #[serde(with = "crate::serde::serde_str")]
    pub name: &'vir str, // TODO: identifiers
    #[serde(with = "crate::serde::serde_ref")]
    pub input: Type<'vir, T>,
    #[serde(with = "crate::serde::serde_ref")]
    pub ty: Type<'vir, R>,
}

impl<'vir, T: CompType, R: CompType> AdtDestructorData<'vir, T, R> {
    pub fn as_dyn(&self) -> &AdtDestructorData<'vir, crate::Dyn, crate::Dyn> {
        let ptr = self as *const Self as *const AdtDestructorData<'vir, crate::Dyn, crate::Dyn>;
        unsafe { &*ptr }
    }
}

#[derive(PartialEq, Eq, Clone, Serialize, Deserialize, Hash)]
pub struct BackendInterpretationPair<'vir> {
    #[serde(with = "crate::serde::serde_str")]
    pub key: &'vir str,
    #[serde(with = "crate::serde::serde_str")]
    pub value: &'vir str,
}

impl<'vir> BackendInterpretationPair<'vir> {
    pub fn to_tuple(&self) -> (&'vir str, &'vir str) {
        (self.key, self.value)
    }
}

#[derive(PartialEq, Eq, Clone, Serialize, Deserialize, Hash)]
#[serde(bound(deserialize = "'de: 'vir"))]
pub struct BackendInterpretationData<'vir> {
    #[serde(with = "crate::serde::serde_slice")]
    pub interpretation: &'vir [&'vir BackendInterpretationPair<'vir>],
}

#[derive(PartialEq, Eq, Clone, Serialize, Deserialize, Hash)]
pub struct InterpretationData<'vir> {
    #[serde(with = "crate::serde::serde_str")]
    pub interpretation: &'vir str,
}

#[derive(PartialEq, Eq, Clone, Serialize, Deserialize, Hash)]
#[serde(bound(deserialize = "'de: 'vir"))]
pub struct DomainFunctionData<'vir> {
    pub unique: bool,
    pub name: ViperIdent<'vir>,
    #[serde(with = "crate::serde::serde_slice")]
    pub args: &'vir [TypeDyn<'vir>],
    #[serde(with = "crate::serde::serde_ref")]
    pub ret: TypeDyn<'vir>,
    pub interpretation: Option<InterpretationData<'vir>>,
}

#[derive(PartialEq, Eq, Clone, Copy, Serialize, Deserialize, Hash)]
pub enum CfgBlockLabelData {
    Start,
    End,
    BasicBlock(usize),
    BasicBlockTerminator(usize),
}

impl CfgBlockLabelData {
    pub fn name(&self) -> String {
        match self {
            Self::Start => "start".to_string(),
            Self::End => "end".to_string(),
            Self::BasicBlock(idx) => format!("bb_{idx}"),
            Self::BasicBlockTerminator(idx) => format!("bb_term_{idx}"),
        }
    }
}

#[derive(PartialEq, Eq, Clone, Copy, Serialize, Deserialize, Hash)]
pub enum OldLabel<'vir> {
    None,
    Lhs,
    Block(CfgBlockLabelData),
    Label(#[serde(with = "crate::serde::serde_str")] &'vir str),
}

pub type AccFieldData<'vir> = crate::gendata::AccFieldGenData<'vir, (), !>;
pub type AdtData<'vir> = crate::gendata::AdtGenData<'vir, (), !>;
pub type AdtConstructorData<'vir> = crate::gendata::AdtConstructorGenData<'vir, (), !>;
pub type BinOpData<'vir> = crate::gendata::BinOpGenData<'vir, (), !>;
pub type CfgBlockData<'vir> = crate::gendata::CfgBlockGenData<'vir, (), !>;
pub type CfgLabelData<'vir> = crate::gendata::CfgLabelGenData<'vir, (), !>;
pub type DomainAxiomData<'vir> = crate::gendata::DomainAxiomGenData<'vir, (), !>;
pub type DomainData<'vir> = crate::gendata::DomainGenData<'vir, (), !>;
pub type ExistsData<'vir> = crate::gendata::ExistsGenData<'vir, (), !>;
pub type ExprData<'vir, T> = crate::gendata::ExprGenData<'vir, (), !, T>;
pub type ExprKindData<'vir> = crate::gendata::ExprKindGenData<'vir, (), !>;
pub type ForallData<'vir> = crate::gendata::ForallGenData<'vir, (), !>;
pub type FuncAppData<'vir> = crate::gendata::FuncAppGenData<'vir, (), !>;
pub type FunctionData<'vir> = crate::gendata::FunctionGenData<'vir, (), !>;
pub type GotoIfData<'vir> = crate::gendata::GotoIfGenData<'vir, (), !>;
pub type LetData<'vir> = crate::gendata::LetGenData<'vir, (), !>;
pub type MethodData<'vir> = crate::gendata::MethodGenData<'vir, (), !>;
pub type MethodBodyData<'vir> = crate::gendata::MethodBodyGenData<'vir, (), !>;
pub type MethodCallData<'vir> = crate::gendata::MethodCallGenData<'vir, (), !>;
pub type OldData<'vir> = crate::gendata::OldGenData<'vir, (), !>;
pub type PredicateAppData<'vir> = crate::gendata::PredicateAppGenData<'vir, (), !>;
pub type PredicateData<'vir> = crate::gendata::PredicateGenData<'vir, (), !>;
pub type ProgramData<'vir> = crate::gendata::ProgramGenData<'vir, (), !>;
pub type PureAssignData<'vir> = crate::gendata::PureAssignGenData<'vir, (), !>;
pub type SetLiteralData<'vir> = &'vir crate::gendata::SetLiteralGenData<'vir, (), !>;
pub type StmtData<'vir> = crate::gendata::StmtGenData<'vir, (), !>;
pub type StmtKindData<'vir> = crate::gendata::StmtKindGenData<'vir, (), !>;
pub type TerminatorStmtData<'vir> = crate::gendata::TerminatorStmtGenData<'vir, (), !>;
pub type TernaryData<'vir> = crate::gendata::TernaryGenData<'vir, (), !>;
pub type TriggerData<'vir> = crate::gendata::TriggerGenData<'vir, (), !>;
pub type UnOpData<'vir> = crate::gendata::UnOpGenData<'vir, (), !>;
pub type UnfoldingData<'vir> = crate::gendata::UnfoldingGenData<'vir, (), !>;
pub type WandData<'vir> = crate::gendata::WandGenData<'vir, (), !>;
